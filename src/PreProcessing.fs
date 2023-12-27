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

module PreProcessing

open Statement
open FSharp.Collections

open Util

// Records the Run through the verification process, to identify unique positions 
type VerificationRunEvent = 
    | BranchLeft 
    | BranchRight
    | Loop
    | LoopEnd


type VerificationRunTrace = list<VerificationRunEvent>

let rec isTracePrefix (tr1 : VerificationRunTrace) (tr2 : VerificationRunTrace) = 
    match tr1, tr2 with 
    | _, [] -> true 
    | x::tr1, y::tr2 when x = y -> isTracePrefix tr1 tr2
    | _, _ -> false

let rec isNestedLoopTrace (tr1 : VerificationRunTrace) (tr2 : VerificationRunTrace) = 
    match tr1, tr2 with 
    | [Loop], Loop::x::_ when x <> LoopEnd -> 
        true 
    | x::tr1, y::tr2 when x = y -> 
        isNestedLoopTrace tr1 tr2
    | _, _ -> false

type LoopAlignmentSkipping = list<bool>

type LoopLocationAndScheduling = 
    {
        Trace : VerificationRunTrace;
        LoopAlignmentSkipping : LoopAlignmentSkipping
        LoopCode : list<option<Expression * Statement>>
    }


/// Computes all traces to loops used in the program
let computeAllTracesInProgram (programList : list<Statement>) = 
    let rec computeAllTracesLoop trace (loopBodiesAndRemainder : list<option<Expression * Statement> * Statement>) = 
        
        let allPossibleAlignments : seq<LoopAlignmentSkipping> = 
            loopBodiesAndRemainder
            |> List.map (fun (x, _) -> 
                match x with 
                | None -> seq [false] 
                | Some _ -> 
                    seq [true; false]
                )
            |> Util.cartesianProduct
            |> Seq.filter (List.exists id)
                

        let res = 
            allPossibleAlignments
            |> Seq.map (fun a -> 
                // Compute the loop bodies and remainder module to the current loop alignment
                let guards, scheduledLoopBodies, scheduledLoopRemainders = 
                    (loopBodiesAndRemainder, a) 
                    ||> List.zip
                    |> List.map (fun ((loop, remainder), isScheduled) -> 
                        match loop, isScheduled with 
                        | None, _ -> 
                            // No loop at this position, the body is Skip and afterwards we continue with the remainder
                            None, Skip, remainder
                        | Some (g, body), false -> 
                            // There exists a loop in this copy but the scheduling does not schedule it
                            // Return skip but execute the loop afterwards
                            None, Skip, Seq(While(g, body), remainder)
                        | Some (g, body), true -> 
                            // There exists a loop and it is scheduled
                            Some g, body, remainder
                        
                        )
                    |> List.unzip3

                let tracesInside = computeAllTracesRec trace scheduledLoopBodies
                let tracesAfter = computeAllTracesRec (LoopEnd::trace) scheduledLoopRemainders

                let allTraces = 
                    Util.cartesianProduct [tracesInside; tracesAfter]
                    |> Seq.map Set.unionMany
                    |> Seq.toList

                let guardsAndBodies = 
                    guards 
                    |> List.mapi (fun i x -> 
                        x 
                        |> Option.map (fun g -> 
                            g, scheduledLoopBodies.[i]
                            )
                        )

                allTraces
                |> List.map (Set.add {Trace = trace; LoopAlignmentSkipping = a; LoopCode = guardsAndBodies})
                )
            |> List.concat

        res
        
    // Main verification loop
    and computeAllTracesRec trace (programList : list<Statement>) : list<Set<LoopLocationAndScheduling>> = 
        if List.forall (fun x -> match x with Terminated -> true | _ -> false) programList then 
            List.singleton Set.empty

        elif List.forall (fun x -> match x with Seq(While(_, _), _) | Terminated -> true | _ -> false) programList then 
            let loopBodiesAndRemainder = 
                programList
                |> List.map (fun x -> 
                    match x with 
                    | Seq(While(guard, body), P2) -> 
                        (Some (guard, body), P2) 
                    | Terminated -> 
                        None, Skip
                    | _ -> failwith ""
                    )

            computeAllTracesLoop (Loop::trace) loopBodiesAndRemainder
        else 
            let targetIndex = List.findIndex (fun x -> match x with Terminated | Seq(While _, _) -> false | _ -> true) programList 

            match programList.[targetIndex] with 
            | Skip -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex Terminated programList)

            | P when (match P with Seq _ -> false | _ -> true) -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex (Seq(P, Skip)) programList)
            
            | Seq(Skip, P) -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex P programList)

            | Seq(Seq(P1, P2), P3) -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex (Seq(P1, Seq(P2, P3))) programList)

            | Seq(VarAssign _, P') -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex P' programList)

            | Seq(ArrayAssign _, P') -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex P' programList)

            | Seq(Assume _, P') -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex P' programList) 

            | Seq(Assert _, P') -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex P' programList)

            | Seq(If(_, P1, P2), P') -> 
                let l1 = computeAllTracesRec (BranchLeft::trace) (Util.replaceAt targetIndex (Seq(P1, P')) programList)
                let l2 = computeAllTracesRec (BranchRight::trace) (Util.replaceAt targetIndex (Seq(P2, P')) programList)
                
                Util.cartesianProduct [l1; l2]
                |> Seq.map Set.unionMany
                |> Seq.toList
                    
            | Seq(Nondet(P1, P2), P') ->
                let l1 = computeAllTracesRec (BranchLeft::trace) (Util.replaceAt targetIndex (Seq(P1, P')) programList)
                let l2 = computeAllTracesRec (BranchRight::trace) (Util.replaceAt targetIndex (Seq(P2, P')) programList)
                
                Util.cartesianProduct [l1; l2]
                |> Seq.map Set.unionMany
                |> Seq.toList
                        
            | Seq(NondetAssign _, P') -> 
                computeAllTracesRec trace (Util.replaceAt targetIndex P' programList)
            
            | FunctionCall _ -> 
                raise <| ForExException "Encountered a procedure call. Need to be inlined first"

            | _ -> 
                failwith ""

    computeAllTracesRec [] programList


