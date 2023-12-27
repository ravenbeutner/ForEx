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

module Heuristic 

open System.Collections.Generic

open SMT
open Statement
open StrongestPostComputer


type ExpressionSimilarity = 
    | ExpressionEqual
    | ExpressionSameStructure
    | ExpressionNotRelated
    | NotApplicable

let judgeExpressionSimilarity l = 
    let judge (e1 : Expression) (e2 : Expression) = 
        if e1 = e2 then 
            ExpressionEqual
        elif Expression.haveSameStructure e1 e2 then 
            ExpressionSameStructure
        else 
            ExpressionNotRelated

    if List.length l <= 1 then 
        // No comparison so, not related
        NotApplicable
    else 
        let res = 
            l[1..]
            |> List.map (fun x -> judge x l.[0])

        if List.forall (fun x -> x = ExpressionEqual) res then 
            ExpressionEqual
        elif List.forall (fun x -> x = ExpressionEqual || x = ExpressionSameStructure) res then 
            ExpressionSameStructure
        else 
            ExpressionNotRelated

type Dag<'T when 'T: comparison> =
    {
        Nodes : list<'T>;
        Implications : list<int * int>
    }

module Dag = 

    let findWeakerNodes dag x = 
        let queue = new Queue<_>()
        queue.Enqueue x 

        let solution = new HashSet<_>()

        while queue.Count <> 0 do 
            let n = queue.Dequeue()
            solution.Add n |> ignore

            dag.Implications
            |> List.filter (fun (x, _) -> x = n)
            |> List.map snd
            |> List.iter (fun x -> 
                if (solution.Contains x |> not) && (queue.Contains x |> not) then 
                    queue.Enqueue x
                )

        set solution

    let findStrongerNodes dag x = 
        let queue = new Queue<_>()
        queue.Enqueue x 

        let solution = new HashSet<_>()

        while queue.Count <> 0 do 
            let n = queue.Dequeue()
            solution.Add n |> ignore

            dag.Implications
            |> List.filter (fun (_, x) -> x = n)
            |> List.map fst
            |> List.iter (fun x -> 
                if (solution.Contains x |> not) && (queue.Contains x |> not) then 
                    queue.Enqueue x
                )

        set solution


let minePredicates (pre : SmtTerm<Var * int>) (post : SmtTerm<Var * int>) (loops : list<option<Expression * Statement>>) (types : list<TypeMapping>) (opt : AnalysisOptions) = 
    let prePostWeight = 100
    let hintWeight = 200
    let loopGuardEqualityWeight = 50
    let unreachWeight = 250
    let trueWeight = 90

    let modifiedVars = 
        loops 
        |> List.map (fun x -> 
            match x with 
            | Some (_, body) -> 
                body |> Statement.modifiedVars
            | _ -> Set.empty
        )

    // We compute possible conjuncts and assign each a priority
    let prePostConjuncts = 
        (pre |> SmtTerm.topLevelConjuncts) @ (post |> SmtTerm.topLevelConjuncts)
        |> List.choose (fun x -> 
            let usesModifiedVars = x |> SmtTerm.usedVars  |> Set.exists (fun (x, i) -> modifiedVars.[i].Contains x)

            if usesModifiedVars then 
                (x, prePostWeight) |> Some
            else 
                // The formula does not refer to any variable that is modified in the loop, no need to include it as a LI
                None
            )

    let hintConjuncts = 
        opt.InvHints
        |> List.map (fun x -> x, hintWeight)

    let loopGuardVars = 
        loops 
        |> List.mapi (fun i x -> 
            match x with 
            | None -> Set.empty
            | Some (g, body) -> 
                Set.intersect (Expression.usedVars g) (Statement.usedVars body)
                |> Set.map (fun y -> (y, i)
                )
        )
        |> Set.unionMany
        |> Set.toList

    
    let loopGuardEqualities = 
        List.allPairs loopGuardVars loopGuardVars 
        |> List.choose (fun ((x, i), (y, j)) -> 
            if i <= j || types.[i].[x] <> types.[j].[y] then
                None
            else 
                (SmtTerm.Eq (SmtTerm.Var(x, i), SmtTerm.Var (y, j)), loopGuardEqualityWeight - (Util.levenshtein x y ))
                |> Some
            )

    let allConjunctionBlocks = 
        if opt.UseOnlyInvHints then 
            set hintConjuncts
        else 
            prePostConjuncts @ loopGuardEqualities @ hintConjuncts
            |> set

    let allCounts = 
        loops
        |> List.map (function 
            | None -> seq [1]
            | Some (_, body)-> 
                if Statement.containsLoop body then 
                    // The inner body contains nested loops, we only align such loops synchronously 
                    seq [1]
                else    
                    seq [1..opt.MaxAsynchronousAlignments]
                )
        |> Util.cartesianProduct
        |> Seq.toList

    let nodes = 
        [opt.MinConjunctsInLI..opt.MaxConjunctsInLI]
        |> List.map (fun i -> Util.powersetOfFixedSize i allConjunctionBlocks)
        |> Seq.concat
        |> Seq.toList
        |> List.map (fun x -> 
            let terms = Set.map fst x 
            let weightSum = Set.map snd x |> Seq.sum

            let averageWeight = if Set.isEmpty x then 0 else weightSum / (Set.count x) 

            let inv = terms |> Set.toList |> SmtTerm.And

            allCounts
            |> List.map (fun counts -> 
                if List.forall ((=) 1) counts then 
                    LoopInvariant.CountingLoopInvariant(counts, inv), averageWeight + 100
                else 
                    LoopInvariant.CountingLoopInvariant(counts, inv), averageWeight
                )
        )
        |> List.concat

    
    let nodes = 
        (UnreachableInvariant, unreachWeight) 
        :: (LoopInvariant.CountingLoopInvariant(List.init (List.length loops) (fun _ -> 1), SmtTerm.And []), trueWeight) 
        :: nodes

    // Sort the nodes so that the most promising candidate goes first
    let nodes = 
        List.sortByDescending snd nodes 
        |> List.map fst

    // We use a simple approximation of implication by checking the set of conjuncts for subset inclusion
    let implications = 
        List.allPairs [0..nodes.Length-1] [0..nodes.Length-1]
        |> List.filter (fun (i, j) ->   
            match nodes.[i], nodes.[j] with 
            | CountingLoopInvariant(l1, SmtTerm.App(SmtOperator.AND, f1)), CountingLoopInvariant(l2, SmtTerm.App(SmtOperator.AND, f2)) -> 
                l1 = l2 && Set.isSuperset (set f1) (set f2)
            | _ -> 
                false 
            )

    {
        Dag.Nodes = nodes
        Dag.Implications = implications
    }
