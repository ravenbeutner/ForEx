(*    
    Copyright (C) 2023 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module Verifier 

open System 

open Util
open SMT
open SMTUtil
open Statement 

open PreProcessing
open StrongestPostComputer
open Heuristic

// Inner loop that tries all possible LI guesses within the current scheduling
// Prunes non-promising LIs
let rec private loopOverPossibleLIs (config : Configuration) (programList : list<StatementTypePair>) (k : int) (execState : ExecState) (post : SmtTerm<Var * int>) (mapTracesToAlignmentAndDag : Map<VerificationRunTrace,LoopAlignmentSkipping * Dag<LoopInvariant>>) (liGuesses : list<Map<VerificationRunTrace,int>>) =   
    match liGuesses with 
    | [] -> 
        // Exhausted all LI, no verification possible under the current loop alignment
        false 
    | guess:: xs -> 
        // Lookup the formula used for the respective index
        let liGuess = 
            guess 
            |> Map.map (fun k x -> 
                let alignment, dag = mapTracesToAlignmentAndDag.[k]
                alignment, dag.Nodes.[x]
            )

        try 
            let recRes = computeStrongestPost config programList k execState liGuess

            let timeIndexedPost = post |> SmtTerm.map (fun (x, i) -> ProgramVariable(x, i, recRes.VariableTime.[x, i]))

            // A post could be computed
            match checkWithFEF config programList k (SmtTerm.And [SmtTerm.Implies(recRes.Post, timeIndexedPost); recRes.Condition]) with 
            | SmtSatResult.UNKNOWN | SmtSatResult.ERROR _ -> raise <| ForExException "Could not solve FEF query"
            | SmtSatResult.SAT -> 
                true
            | SmtSatResult.UNSAT -> 
                // The current LI guess is not strong enough, block it and try again 
                config.Logger.LogN "Discard current LI: No strong enough postcondition"

                if Map.isEmpty guess then 
                    // There is no loop, so the property just does not hold
                    false
                else 
                    loopOverPossibleLIs config programList k execState post mapTracesToAlignmentAndDag xs 
                    
        with 
        | VerificationFailException (NonInitial, loc) -> 
            // The LI is not initial. This depends on all smaller traces that have an impact on this one. So filter out all attempts where the prefixes have the same LI as in guess 
            config.Logger.LogN "Discard current LI: Not initial"

            let prefixLocs = 
                Map.keys guess
                |> Seq.filter (fun l -> isTracePrefix l loc && l <> loc)

            // Find all stronger formulas. If the outer LIs are chosen then same, all those are not initial as well
            let dag = snd mapTracesToAlignmentAndDag.[loc]
            let strongerNodes = Dag.findStrongerNodes dag guess.[loc]

            let filteredXs = 
                xs 
                |> List.filter (fun m -> 
                    // We continue with all that differ on a LI for a prefix OR are weaker at the current not
                    prefixLocs
                    |> Seq.exists (fun l -> 
                        m.[l] <> guess.[l]
                        )
                    ||
                    (Set.contains m.[loc] strongerNodes |> not)
                    ) 

            loopOverPossibleLIs config programList k execState post mapTracesToAlignmentAndDag filteredXs

        | VerificationFailException (NonSimultaneous, loc) -> 
            // The LI at the current location does not ensures simultaneous termination
            config.Logger.LogN  "Discard current LI: No simultaneous termination"

            // All weaker formula also will not ensure simultaneous termination
            let dag = snd mapTracesToAlignmentAndDag.[loc]
            let weakerNodes = Dag.findWeakerNodes dag guess.[loc]

            let filteredXs = 
                xs 
                |> List.filter (fun m -> 
                    (Set.contains m.[loc] weakerNodes |> not)
                    ) 

            loopOverPossibleLIs config programList k execState post mapTracesToAlignmentAndDag filteredXs

        | VerificationFailException (NonInductive, _) -> 
            config.Logger.LogN  "Discard current LI: Not inductive"
            
            loopOverPossibleLIs config programList k execState post mapTracesToAlignmentAndDag xs 

        | VerificationFailException (NotNotReachable, loc) -> 
            config.Logger.LogN "Discard current LI: Not not reachable"

            let prefixLocs = 
                Map.keys guess
                |> Seq.filter (fun l -> isTracePrefix l loc && l <> loc)

            // Filter all formulas out that have the same prefix
            let filteredXs = 
                xs 
                |> List.filter (fun m -> 
                    // We continue with all that differ on the prefix or are weaker at the current not
                    prefixLocs
                    |> Seq.exists (fun l -> 
                        m.[l] <> guess.[l]
                        )
                    ||
                    (m.[loc] <> guess.[loc])
                    ) 

            loopOverPossibleLIs config programList k execState post mapTracesToAlignmentAndDag filteredXs 


let verify (config : Configuration) (programList : list<StatementTypePair>) (k : int) (pre : SmtTerm<String * int>) (post : SmtTerm<String * int>) = 
    
    let allProgramVars = 
        programList
        |> List.mapi (fun i s -> 
            s.TypeMapping.Keys
            |> set 
            |> Set.map (fun x -> x, i)
        )
        |> Set.unionMany


    // We compute all possible alignment of loops and rank them by the guard similarity
    let allPossibleLoopSchedulings = 
        computeAllTracesInProgram (List.map (fun x -> x.Statement) programList)
        |> List.filter (fun x -> 
            // Filter out all traces that have to many alignment points
            config.AnalysisOptions.MaxLoopAlignments.IsNone || (x.Count <= config.AnalysisOptions.MaxLoopAlignments.Value)
            )
        |> List.sortByDescending (fun x -> 
            x
            |> Set.toList
            |> List.map (fun y -> 
                if y.LoopAlignmentSkipping[0..k-1] |> List.exists id then 
                    let numberOfLoops = y.LoopAlignmentSkipping |> List.filter id |> List.length

                    let es = 
                        y.LoopCode
                        |> List.choose id 
                        |> List.map fst
                        |> Heuristic.judgeExpressionSimilarity

                    let esScore = 
                        match es with 
                        | ExpressionEqual -> 2
                        | ExpressionSameStructure -> 1
                        | NotApplicable -> 0
                        | ExpressionNotRelated -> -1

                    numberOfLoops + esScore
                else 
                    // This will use unreachable statements, not very likely so we give it a low (negative) priority
                    -5
                )
            |> List.sum
        )

    config.Logger.LogN $"Number of loop alignments: %i{List.length allPossibleLoopSchedulings}\n"

    
    let rec loopOverSchedulings (schedulings : list<Set<LoopLocationAndScheduling>>) = 
        match schedulings with 
        | [] -> 
            // No more alignment to check
            false 
        | sched :: schedulings ->
            // Create a map that maps each trace to the loop alignment and the invDag for that formula
            let mapTracesToAlignementAndDag = 
                sched
                |> Set.map (fun x -> 
                    // Compute likely loop invariants and their syntactic 
                    if x.LoopAlignmentSkipping[0..k-1] |> List.exists id then 
                        // At least one universal loop is scheduled, so we can pick a proper loop invariant 

                        let someUniversalLoopIsSurelyDiverging = 
                            x.LoopCode.[0..k-1] 
                            |> List.exists (fun z -> 
                                match z with 
                                | Some (Expression.BoolConst true, _) -> true 
                                | _ -> false )

                        if someUniversalLoopIsSurelyDiverging then 
                            // On of the universal loops is diverging
                            x.Trace, (x.LoopAlignmentSkipping, {Dag.Nodes = [DivergingLoop]; Implications = []} )
                        else 
                            let types = programList |> List.map (fun x -> x.TypeMapping)
                            let invDag = Heuristic.minePredicates pre post x.LoopCode types config.AnalysisOptions
                            x.Trace, (x.LoopAlignmentSkipping, invDag)
                    else 
                        // Only existential loops are scheduled this situation can only be verified when it is unreachable
                        x.Trace, (x.LoopAlignmentSkipping, {Dag.Nodes = [UnreachableInvariant]; Implications = []} )
                )
                |> Map.ofSeq

            // We start with all variables time-stamped to zero
            let execState = 
                {
                    ExecState.Term = pre |> SmtTerm.map (fun (x, i) -> ProgramVariable(x, i, {Time = 0}));
                    VariableTime = 
                        allProgramVars 
                        |> Set.toList 
                        |> List.map (fun v -> v, {Time = 0})
                        |> Map.ofList
                }

            // We identify a LI candidate by their ID in the invDAG
            let allCandidates = 
                mapTracesToAlignementAndDag
                |> Map.map (fun _ (_, d) -> [0..d.Nodes.Length - 1] |> seq)
                // We order based on the indices, so elements early in the list are preferred
                |> Util.cartesianProductMapOrdered (fun x y -> if x = y then 0 elif x < y then -1 else 1)
                |> Seq.toList
            

            config.Logger.LogN $"Need to check %i{List.length allCandidates} LIs for the current loop alignment\n"

            let res = loopOverPossibleLIs config programList k execState post mapTracesToAlignementAndDag allCandidates

            match res with 
            | true -> 
                // Could be verified using some LIs, the property holds
                true
            | false -> 
                // Tried all LIs in the current scheduling, continue with the next one 
                if List.isEmpty schedulings |> not then
                    config.Logger.LogN "========== Continue with next loop scheduling =========="

                loopOverSchedulings schedulings

            
    let res = loopOverSchedulings allPossibleLoopSchedulings

    config.Logger.LogN "\n"

    res

