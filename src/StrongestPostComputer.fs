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

module StrongestPostComputer

open System 
open FSharp.Collections

open Util
open Configuration
open SMT
open SMTUtil

open Statement
open PreProcessing

type AnalysisOptions = 
    {
        InvHints : list<SmtTerm<String * int>>
        MaxConjunctsInLI : int
        MinConjunctsInLI : int
        UseOnlyInvHints : bool
        MaxLoopAlignments : option<int>
        MaxAsynchronousAlignments : int
    }


type Configuration = 
    {
        SmtInterface : SmtInterface
        Logger : Logger
        AnalysisOptions : AnalysisOptions
    }


/// Generate a fresh string that is not contained in the existing variables
let private generateFreshVar (existingVarNames : seq<String>) = 
    let rec f n = 
        let s = "v" + string(n)
        if Seq.contains s existingVarNames then 
            f (n+1)
        else 
            s 
    
    f 0

type TimeIndex = 
    {
        Time : int;
    }

    member this.Inc = 
        {
            Time = this.Time + 1
        }

    static member max a1 a2 = 
        {
            Time = max a1.Time a2.Time
        }


type AssertionVariable = 
    | ProgramVariable of Var * int * TimeIndex
    | ChoiceVariable of string * SmtSort

module AssertionVariable = 

    let asString v = 
        match v with 
        | ProgramVariable (x, i, t) -> x + "_" + string(i) + "_" + string(t.Time)
        | ChoiceVariable (x, sort) -> "choice_" + (SmtSort.abr sort) + "_" + x

type LoopInvariant = 
    | CountingLoopInvariant of list<int> * SmtTerm<Var * int>
    | UnreachableInvariant
    | DivergingLoop 


let checkWithFEF (config: Configuration) (programList : list<StatementTypePair>) (k: int) (term : SmtTerm<AssertionVariable>) = 
    
    let vars = term |> SmtTerm.freeVars

    let univBlock1Vars = 
        vars 
        |> Set.toList
        |> List.filter (fun x -> 
            match x with 
            | ProgramVariable(_, i, _) when i < k -> true
            // The first time-step is quantified in the first universal block
            | ProgramVariable(_, _, {Time = 0}) -> true
            | _ -> false
        )
        
    let existsBlockVars = 
        vars 
        |> Set.toList
        |> List.filter (function ChoiceVariable _ -> true | _ -> false)

    let univBlock2Vars = 
        vars 
        |> Set.toList
        |> List.filter (fun x -> 
            match x with 
            | ProgramVariable(_, i, {Time = t}) when i >= k && t <> 0 -> true 
            | _ -> false
        )

    let getType v = 
        match v with
        | ProgramVariable (x, i, _) -> 
            // For program variables, we can immediately lookup the type in the program (equal across all time-steps)
            programList.[i].TypeMapping.[x] |> VarType.asSMTSort
        | ChoiceVariable (_, t) -> t

    let finalQuery = 
        SmtTerm.Forall ( 
            (univBlock1Vars |> List.map (fun x -> x, getType x) ), 
            SmtTerm.Exists (
                (existsBlockVars |> List.map (fun x -> x, getType x) ), 
                SmtTerm.Forall (
                    (univBlock2Vars |> List.map (fun x -> x, getType x) ),
                    term
                )
            )
        )

    let instance = 
        {
            SmtSatInstance.Term = finalQuery
            SortMapping = Map.empty
            VarStringer = AssertionVariable.asString
        }

    config.SmtInterface.isSat instance


type VerificationSuccessResult = 
    {
        Post : SmtTerm<AssertionVariable>;
        Condition : SmtTerm<AssertionVariable>;
        VariableTime : Map<Var * int, TimeIndex>;
    }

let mergeResults (recRes1: VerificationSuccessResult) (recRes2: VerificationSuccessResult) (unmergedChoiceVariables : list<string * SmtSort>) = 
    // We merge both results and ensure that the choice variables in both branches are distinct
    // We only keep the choice variables in unmergedChoiceVariables, i.e., those will stay unmerged in both branches
    
    let mergesFirst, mergesSecond =
        Set.union (recRes1.VariableTime.Keys |> set) (recRes2.VariableTime.Keys |> set)
        |> Seq.toList 
        |> List.map (fun (x, i) -> 
            if recRes1.VariableTime.[x, i] < recRes2.VariableTime.[x, i] then 
                let c = SmtTerm.App (SmtOperator.EQ, [ProgramVariable(x, i, recRes1.VariableTime.[x, i]) |> SmtTerm.Var; ProgramVariable(x, i, recRes2.VariableTime.[x, i]) |> SmtTerm.Var])

                Some c, None
            elif recRes1.VariableTime.[x, i] > recRes2.VariableTime.[x, i] then 
                let c = SmtTerm.App (SmtOperator.EQ, [ProgramVariable(x, i, recRes1.VariableTime.[x, i]) |> SmtTerm.Var; ProgramVariable(x, i, recRes2.VariableTime.[x, i]) |> SmtTerm.Var])
                
                None, Some c
            else 
                None, None
            )
        |> List.unzip

    let mergesFirst = List.choose id mergesFirst
    let mergesSecond = List.choose id mergesSecond


    // We ensure that the choice and branch variables in both results are distinct 
    let choiceVariablesRemap1 = 
        Set.union (SmtTerm.usedVars recRes1.Post) (SmtTerm.usedVars recRes1.Condition)
        |> Seq.choose (function 
            | ChoiceVariable (x, t) -> Some (x, t)
            | _ -> None
            )
        |> Seq.mapi (fun i (x, t) -> 
            (x, t), ("v" + string i, t)
            )
        |> Map.ofSeq

    let choiceVariablesRemap2 = 
        Set.union (SmtTerm.usedVars recRes2.Post) (SmtTerm.usedVars recRes2.Condition)
        |> Seq.choose (function 
            | ChoiceVariable (x, t) -> Some (x, t)
            | _ -> None
            )
        |> Seq.mapi (fun i (x, t) -> 
            if List.contains (x, t) unmergedChoiceVariables && Map.containsKey (x, t) choiceVariablesRemap1  then 
                // This variable should be shared (and is actually shared in both results)
                // We use the same name we already fixed for choiceVariablesRemap1
                (x, t), choiceVariablesRemap1.[x, t]
            else 
                // We remap this variable to a fresh ID
                (x, t), ("v" + string (i + Map.count choiceVariablesRemap1), t)
            )
        |> Map.ofSeq


    let remappedPost1 = 
        recRes1.Post
        |> SmtTerm.map (function 
            | ChoiceVariable (x, t) -> ChoiceVariable choiceVariablesRemap1.[x, t]
            | y -> y
            )

    let remappedPost2 = 
        recRes2.Post
        |> SmtTerm.map (function 
            | ChoiceVariable (x, t) -> ChoiceVariable choiceVariablesRemap2.[x, t]
            | y -> y
            )

    let remappedCondition1 = 
        recRes1.Condition
        |> SmtTerm.map (function 
            | ChoiceVariable (x, t) -> ChoiceVariable choiceVariablesRemap1.[x, t]
            | y -> y
            )

    let remappedCondition2 = 
        recRes2.Condition
        |> SmtTerm.map (function 
            | ChoiceVariable (x, t) -> ChoiceVariable choiceVariablesRemap2.[x, t]
            | y -> y
            )

    {
        // Construct the disjunction of both branches and, if needed, update the state of the variables to re-align the time-points
        VerificationSuccessResult.Post = 
            SmtTerm.Or [
                    (SmtTerm.And (remappedPost1 :: mergesFirst))
                    (SmtTerm.And (remappedPost2 :: mergesSecond))
                ]

        Condition = SmtTerm.And [remappedCondition1; remappedCondition2]

        VariableTime = 
            Seq.append recRes1.VariableTime.Keys recRes2.VariableTime.Keys 
            |> Seq.map (fun k -> 
                let newTime = 
                    match Map.tryFind k recRes1.VariableTime, Map.tryFind k recRes1.VariableTime with 
                    | Some time1, Some time2 -> 
                        TimeIndex.max time1 time2 
                    | None, Some time | Some time, None -> time 
                    | None, None -> failwith ""

                k, newTime
                )
            |> Map.ofSeq
    }

type VerificationFailureResult = 
    | NonInitial
    | NonSimultaneous
    | NonInductive
    | NotNotReachable


exception VerificationFailException of VerificationFailureResult * VerificationRunTrace

type InputInfo = 
    {
        Trace : VerificationRunTrace;
        LoopInvariantGuess : Map<VerificationRunTrace, LoopAlignmentSkipping * LoopInvariant>
    }


type ExecState = 
    {
        Term : SmtTerm<AssertionVariable>;
        VariableTime : Map<Var * int, TimeIndex>;
    }

let computeStrongestPost (config: Configuration) (programList : list<StatementTypePair>) (k : int) (execState : ExecState) (guess : Map<VerificationRunTrace,LoopAlignmentSkipping * LoopInvariant>) = 

    let rec verifyLoops (info: InputInfo) (loopBodiesAndRemainder : list<option<Expression * Statement> * Statement * TypeMapping>) (execState : ExecState) = 
        let invAlignment, invCand = info.LoopInvariantGuess.[info.Trace]

        // Convert the Loop guards to a SMTTerm 
        let guards = 
            loopBodiesAndRemainder
            |> List.mapi (fun i (x, _, _) -> 
                match x, invAlignment.[i] with 
                | Some (g, _), true ->  
                    // The i-th position contains a loop AND is scheduled in the alignment
                    (Expression.asSmtTerm g, i)
                    |> Some
                | _ ->   // No loop at this location
                    None
                
                )
            |> List.choose id

        match invCand with 
        | UnreachableInvariant -> 
            // We must assert that this position is unreachable
            let implicationCondition = SmtTerm.App(SmtOperator.IMPLIES, [execState.Term; SmtTerm.False])

            match checkWithFEF config programList k implicationCondition with 
            | SmtSatResult.UNKNOWN | SmtSatResult.ERROR _ -> raise <| ForExException "Could not solve FEF query"
            | SmtSatResult.UNSAT -> 
                raise <| VerificationFailException (NotNotReachable, info.Trace)
            | SmtSatResult.SAT -> ()

            {
                VerificationSuccessResult.Post = SmtTerm.False
                Condition = implicationCondition
                VariableTime = execState.VariableTime
            } 

        | DivergingLoop -> 
            // This loop is diverging in one universal copy

            // This should be ensured by the oracle that proposes a loop invariant
            assert (guards |> List.exists (fun (t, i) -> i < k && t = SmtTerm.True))

            // Disregard the computation after this, i.e., the post is False and there are no conditions
            {
                VerificationSuccessResult.Post = SmtTerm.False
                Condition = SmtTerm.True
                VariableTime = execState.VariableTime
            } 

        | CountingLoopInvariant (counts, invFormula) -> 
            // Check if pre implies the invariant at least locally. This implication is later added as a global constraint
            let implicationCondition = SmtTerm.App(SmtOperator.IMPLIES, [execState.Term; invFormula |> SmtTerm.map (fun (y, i) -> ProgramVariable(y, i, execState.VariableTime.[(y, i)]))])
            
            match checkWithFEF config programList k implicationCondition with 
            | SmtSatResult.UNKNOWN | SmtSatResult.ERROR _ -> raise <| ForExException "Could not solve FEF query"
            | SmtSatResult.UNSAT -> raise <| VerificationFailException (NonInitial, info.Trace)
            | SmtSatResult.SAT -> ()

            // The Loop invariant is (locally) initial
            // Next: Check if the LI ensure simultaneous termination

            let modifiedVars = 
                loopBodiesAndRemainder
                |> List.mapi (fun i (x, _, _) -> 
                    match x, invAlignment.[i] with 
                    | Some (_, body), true -> 
                        // The i-th position contains a loop AND is scheduled in the alignment
                        body
                        |> Statement.modifiedVars
                        |> Set.map (fun v -> (v, i))
                    | _ -> Set.empty
                    )
                |> Set.unionMany

            // Collect all variables that are ''removed'' from the current precondition as they are fixed by the LI
            let variablesWhereTimeIsIncreased = 
                modifiedVars

            let increasedVariableTime = 
                execState.VariableTime
                |> Map.map (fun (x, i) t -> 
                    if Set.contains (x, i) variablesWhereTimeIsIncreased then 
                        // This variable is reset, i.e., fixed by the LI so we increase its time-index
                        t.Inc
                    else 
                        t 
                    )

            // The state for the analysis of the body. We increase the time-steps to ensure that we do not conflict with the constraints generated by previous conditions
            let execStateForSimTermination = 
                {
                    ExecState.Term =
                        SmtTerm.And [
                            execState.Term; 
                            invFormula |> SmtTerm.map (fun (y, i) -> ProgramVariable(y, i, increasedVariableTime.[y, i]))
                        ]
                    
                    VariableTime = increasedVariableTime
                } 

            let simultaneousTerminationCondition = 
                let allGuardsEquiv = 
                    guards[1..]
                    |> List.map (fun (g, i) -> 
                        let g0, i0 = guards.[0]

                        let a = g |> SmtTerm.map (fun y -> ProgramVariable(y, i, execStateForSimTermination.VariableTime.[y, i]))
                        let b = g0 |> SmtTerm.map (fun y -> ProgramVariable(y, i0, execStateForSimTermination.VariableTime.[y, i0]))
                        SmtTerm.App(SmtOperator.EQ, [a; b])
                    )
                    |> SmtTerm.And

                SmtTerm.Implies(execStateForSimTermination.Term, allGuardsEquiv)

            match checkWithFEF config programList k simultaneousTerminationCondition  with 
            | SmtSatResult.UNKNOWN | SmtSatResult.ERROR _ -> raise <| ForExException "Could not solve FEF query"
            | SmtSatResult.UNSAT -> raise <| VerificationFailException (NonSimultaneous, info.Trace)
            | SmtSatResult.SAT -> ()

            // The Loop invariant (locally) ensures simultaneous termination 
            // Next: Check if the LI is also inductive

            let scheduledLoopBodies, scheduledLoopRemainders = 
                loopBodiesAndRemainder 
                |> List.mapi (fun i (loop, remainder, typeMap) -> 
                    match loop, invAlignment.[i] with 
                    | None, _ -> 
                        // No loop at this position, the body is Skip and afterwards we continue with the remainder
                        {Statement = Skip; TypeMapping = typeMap}, {Statement = remainder; TypeMapping = typeMap}
                    | Some (g, body), false -> 
                        // There exists a loop in this copy but it is not scheduled
                        // Return skip and execute the loop afterwards
                        {Statement = Skip; TypeMapping = typeMap}, {Statement = Seq(While(g, body), remainder); TypeMapping = typeMap}
                    | Some (g, body), true -> 
                        // There exists a loop AND it is scheduled
                        let c = counts.[i]

                        // We only support unrolling for c > 1 (i.e., proper unrolling) if no nested loops are present
                        assert(c = 1 || body |> Statement.containsLoop |> not)

                        // If we unroll we need to ensure that thi unrolling is also valid
                        // This depends on whether we have a universal or exiential copy
                        let assumeOrAssert = if i < k then Assert g else Assume g

                        let newBody =
                            List.init c (fun _ -> body)
                            |> List.reduce (fun x y -> Seq(x, Seq(assumeOrAssert, y)))

                        {Statement = newBody; TypeMapping = typeMap}, {Statement = remainder; TypeMapping = typeMap}
                    )
                |> List.unzip

            
            // We increase the time-points AGAIN, to ensure that future constraints do not clash with the simultaneous termination condition
            let increasedVariableTime2 = 
                execStateForSimTermination.VariableTime
                |> Map.map (fun (x, i) t -> 
                    if Set.contains (x, i) variablesWhereTimeIsIncreased then 
                        t.Inc
                    else 
                        t 
                    )

            let execStateForLoopBody = 
                {
                    // We modify the precondition to assert that all guards are satisfied and compute the post of the body
                    ExecState.Term = SmtTerm.And ([   
                            execState.Term; 
                            invFormula |> SmtTerm.map (fun (y, i) -> ProgramVariable(y, i, increasedVariableTime2.[y, i]))
                        ] @
                        (guards
                        |> List.map (fun (g, i) -> 
                            g |> SmtTerm.map (fun y -> ProgramVariable(y, i, increasedVariableTime2.[y, i]))
                        )));

                    ExecState.VariableTime = increasedVariableTime2
                } 

            // We compute the strongest post-condition for the loop bodies
            let recResBody = verifyRec info scheduledLoopBodies execStateForLoopBody

            // Check if this post implies the invariant, i.e., whether the invariant is (locally) inductive. This will also be added as a global condition
            let inductiveCondition = 
                SmtTerm.And [
                    SmtTerm.Implies(
                        recResBody.Post, 
                        invFormula |> SmtTerm.map (fun (y, i) -> ProgramVariable(y, i, recResBody.VariableTime.[y, i]))
                    ); 
                    recResBody.Condition
                ]

            match checkWithFEF config programList k inductiveCondition with 
            | SmtSatResult.UNKNOWN | SmtSatResult.ERROR _ -> raise <| ForExException "Could not solve FEF query"
            | SmtSatResult.UNSAT -> raise <| VerificationFailException (NonInductive, info.Trace)
            | SmtSatResult.SAT -> ()
            // The invariant is (locally) inductive

            let increasedVariableTime3 = 
                recResBody.VariableTime
                |> Map.map (fun (x, i) t -> 
                    if Set.contains (x, i) variablesWhereTimeIsIncreased then 
                        // This variable is reset, i.e., fixed by the LI so we increase its time-index
                        t.Inc
                    else 
                        t 
                    )

            let execStateForRemainder = 
                {
                    // We assume that the precondition holds AND all loop guards do not hold (i.e., all loop have terminated)
                    ExecState.Term = SmtTerm.And ([   
                            execState.Term; 
                            invFormula |> SmtTerm.map (fun (y, i) -> ProgramVariable(y, i, increasedVariableTime3.[y, i]))
                        ] @
                        (guards
                        |> List.map (fun (g, i) -> 
                            g |> SmtTerm.map  (fun y -> ProgramVariable(y, i, increasedVariableTime3.[y, i]))
                            )
                        // We assume that all guards do NOT hold, i.e., all loops have terminated
                        |> List.map SmtTerm.Not 
                        ));

                    ExecState.VariableTime = increasedVariableTime3 
                } 

            // Continue to verify the remaining program (after the loop). 
            let recResRemainder = verifyRec {info with Trace = LoopEnd :: info.Trace} scheduledLoopRemainders execStateForRemainder

            // We add all conditions that we have already checked (locally) as a global condition
            let conditions = 
                [implicationCondition; simultaneousTerminationCondition; inductiveCondition]
                
            {recResRemainder with 
                VerificationSuccessResult.Condition = SmtTerm.And (recResRemainder.Condition :: conditions)
            } 
          
    and verifyRec (info : InputInfo) (programList : list<StatementTypePair>) (execState : ExecState) = 
        // Always simplify the term first
        let execState = {execState with Term = execState.Term |> SmtTerm.simplify}

        if List.forall (fun x -> match x.Statement with Terminated -> true | _ -> false) programList then 
            // All programs are terminated, reached the end of the computation
            {
                VerificationSuccessResult.Post = execState.Term;
                Condition = SmtTerm.True;
                VariableTime = execState.VariableTime;
            }
        elif List.forall (fun x -> match x.Statement with Seq(While(_, _), _) | Terminated -> true | _ -> false) programList then 
            // All programs start with a loop or are terminated. Moreover, there is at least one loop 

            let loopBodiesAndRemainder = 
                programList
                |> List.map (fun x -> 
                    match x.Statement with 
                    | Seq(While(guard, body), P2) -> 
                        (Some (guard, body), P2, x.TypeMapping) 
                    | Terminated -> 
                        None, Skip, x.TypeMapping
                    | _ -> failwith "Unreachable"    
                    )

            verifyLoops {info with Trace = Loop :: info.Trace} loopBodiesAndRemainder execState
        else 
            // We compute the first index that can make a proper (loop-free) step
            let targetIndex = List.findIndex (fun x -> match x.Statement with Terminated | Seq(While _, _) -> false | _ -> true) programList 

            // Investigate the structure of the target program
            match programList.[targetIndex] with 
            | {Statement = Skip; TypeMapping = t} -> 
                verifyRec info (Util.replaceAt targetIndex {Statement = Terminated; TypeMapping = t} programList) execState

            | {Statement = P; TypeMapping = t} when (match P with Seq _ -> false | _ -> true) -> 
                verifyRec info (Util.replaceAt targetIndex {Statement = Seq(P, Skip); TypeMapping = t} programList) execState
            
            | {Statement = Seq(Skip, P); TypeMapping = t} -> 
                verifyRec info (Util.replaceAt targetIndex {Statement = P; TypeMapping = t} programList) execState

            | {Statement = Seq(Seq(P1, P2), P3); TypeMapping = t} -> 
                verifyRec info (Util.replaceAt targetIndex {Statement = Seq(P1, Seq(P2, P3)); TypeMapping = t} programList) execState

            | {Statement = Seq(VarAssign(x, e), P'); TypeMapping = t} -> 
                let newTimeX = execState.VariableTime.[x, targetIndex].Inc

                let expTerm = 
                    e |> Expression.asSmtTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex]))
                
                let post = 
                    SmtTerm.And [
                        execState.Term;
                        SmtTerm.Eq (
                            SmtTerm.Var (ProgramVariable(x, targetIndex, newTimeX)), 
                            expTerm
                        )
                    ]

                let postExecState = 
                    {
                        ExecState.Term = post;
                        VariableTime = Map.add (x, targetIndex) newTimeX execState.VariableTime
                    }

                verifyRec info (Util.replaceAt targetIndex {Statement = P'; TypeMapping = t} programList) postExecState

            | {Statement = Seq(ArrayAssign(x, pos, e), P'); TypeMapping = t} -> 
                let newTimeX = execState.VariableTime.[x, targetIndex].Inc

                if pos.Length <> 1 then 
                    raise <| ForExException "Currently NO support for array with order > 1"

                let posTerm  = 
                    pos.[0] |> Expression.asSmtTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex]))
                
                let expTerm = 
                    e |> Expression.asSmtTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex]))
                    
                let updateTerm = 
                    SmtTerm.ArrayStore (ProgramVariable(x, targetIndex, execState.VariableTime.[x, targetIndex]) |> SmtTerm.Var, posTerm, expTerm)

                let post = 
                    SmtTerm.And [
                        execState.Term;
                        SmtTerm.Eq (
                            SmtTerm.Var (ProgramVariable(x, targetIndex, newTimeX)), 
                            updateTerm
                        )
                    ]

                let postExecState = 
                    {
                        ExecState.Term = post;
                        VariableTime = Map.add (x, targetIndex) newTimeX execState.VariableTime
                    }

                verifyRec info (Util.replaceAt targetIndex {Statement = P'; TypeMapping = t} programList) postExecState

            | {Statement = Seq(Assume b, P'); TypeMapping = t} -> 
                let guardAsTerm = b |> Expression.asSmtTerm

                if targetIndex < k then 
                    let postExecState = 
                        {execState with 
                            Term = 
                                SmtTerm.And 
                                    [
                                        guardAsTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex]));
                                        execState.Term
                                    ]
                        }

                    verifyRec info (Util.replaceAt targetIndex {Statement = P'; TypeMapping = t} programList) postExecState
                else 
                    // For existentially copies, we need to ensure that this holds on the current path, i.e., treat it as an assert
                    let newCondition = SmtTerm.Implies(execState.Term, guardAsTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex])))
                
                    let recRes = verifyRec info (Util.replaceAt targetIndex  {Statement = P'; TypeMapping = t} programList) execState
                    
                    {
                        recRes with Condition = SmtTerm.And [newCondition; recRes.Condition]
                    }
                    
            | {Statement = Seq(Assert b, P'); TypeMapping = t} -> 
                let guardAsTerm = b |> Expression.asSmtTerm

                let newCondition = SmtTerm.Implies (execState.Term, guardAsTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex])))

                let recRes = verifyRec info (Util.replaceAt targetIndex {Statement = P'; TypeMapping = t} programList) execState
        
                {
                    recRes with Condition = SmtTerm.And [newCondition; recRes.Condition]
                }

            | {Statement = Seq(If(b, P1, P2), P'); TypeMapping = t} -> 
                let guardAsTerm = b |> Expression.asSmtTerm

                let bAsTerm = guardAsTerm |> SmtTerm.map (fun y -> ProgramVariable(y, targetIndex, execState.VariableTime.[y, targetIndex]))

                let recRes1 = verifyRec {info with Trace = BranchLeft::info.Trace} (Util.replaceAt targetIndex {Statement = Seq(P1, P'); TypeMapping = t} programList) {execState with Term = (SmtTerm.And [bAsTerm; execState.Term])}

                let recRes2 = verifyRec {info with Trace = BranchRight::info.Trace} (Util.replaceAt targetIndex {Statement = Seq(P2, P'); TypeMapping = t} programList) {execState with Term = (SmtTerm.And [SmtTerm.Not bAsTerm; execState.Term])}

                mergeResults recRes1 recRes2 []

            | {Statement = Seq(Nondet(P1, P2), P'); TypeMapping = t} ->
                if targetIndex < k then 

                    let recRes1 = verifyRec {info with Trace = BranchLeft::info.Trace} (Util.replaceAt targetIndex {Statement = Seq(P1, P'); TypeMapping = t} programList) execState

                    let recRes2 = verifyRec {info with Trace = BranchRight::info.Trace} (Util.replaceAt targetIndex {Statement = Seq(P2, P'); TypeMapping = t} programList) execState

                    mergeResults recRes1 recRes2 []
                else 
                    // For existential copies we can choose which branch to follow
                    let freshParameter = 
                        execState.Term
                        |> SmtTerm.usedVars
                        |> Set.map (function
                            | ChoiceVariable (y, _) -> Set.singleton y
                            |  _ -> Set.empty
                            )
                        |> Set.unionMany
                        |> generateFreshVar

                    let freshChoiceVar = ChoiceVariable (freshParameter, BOOL)

                    let recRes1 = verifyRec {info with Trace = BranchLeft::info.Trace} (Util.replaceAt targetIndex {Statement = Seq(P1, P'); TypeMapping = t} programList) {execState with Term = (SmtTerm.And [SmtTerm.Var freshChoiceVar; execState.Term])}

                    let recRes2 = verifyRec {info with Trace = BranchRight::info.Trace} (Util.replaceAt targetIndex {Statement = Seq(P2, P'); TypeMapping = t} programList) {execState with Term = (SmtTerm.And [SmtTerm.Not (SmtTerm.Var freshChoiceVar); execState.Term])}

                    mergeResults recRes1 recRes2 [(freshParameter, BOOL)]
            | {Statement = Seq(NondetAssign x, P'); TypeMapping = t} -> 
                if targetIndex < k then 
                    let newTimeForX = execState.VariableTime.[x, targetIndex].Inc

                    // We do not get any new information but instead simply update the timeIndex of x
                    let postExecState =  
                        {
                            ExecState.Term = execState.Term;
                            VariableTime = Map.add (x, targetIndex) newTimeForX execState.VariableTime
                        }

                    verifyRec info (Util.replaceAt targetIndex {Statement = P'; TypeMapping = t} programList) postExecState
                else 
                    let freshChoiceVar = 
                        execState.Term 
                        |> SmtTerm.usedVars
                        |> Set.map (function
                            | ChoiceVariable (y, _) -> Set.singleton y
                            |  _ -> Set.empty
                            )
                        |> Set.unionMany
                        |> generateFreshVar
                        |> fun y -> ChoiceVariable(y, VarType.asSMTSort t.[x])

                    let newTimeForX = execState.VariableTime.[x, targetIndex].Inc

                    let postExecState = 
                        {
                            ExecState.Term = 
                                SmtTerm.And [
                                    execState.Term; 
                                    SmtTerm.Eq (ProgramVariable(x, targetIndex, newTimeForX) |> SmtTerm.Var, SmtTerm.Var freshChoiceVar)
                                ];
                            ExecState.VariableTime = Map.add (x, targetIndex) newTimeForX execState.VariableTime
                        }
                
                    verifyRec info (Util.replaceAt targetIndex {Statement = P'; TypeMapping = t} programList) postExecState
            | {Statement = FunctionCall _; TypeMapping = _} ->  
                raise <| ForExException "Encountered a procedure call which needs to be inlined first"
            | _ -> 
                // Should not be reached
                failwith ""

    let info = {InputInfo.Trace = []; LoopInvariantGuess = guess}

    verifyRec info programList execState



