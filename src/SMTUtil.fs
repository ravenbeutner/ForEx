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

module SMTUtil

open System
open System.IO
open System.Collections.Generic
open FSharp.Collections

open Util
open Configuration
open SMT


let mutable satQueryCount = 0
let mutable satCacheHitCount = 0

let mutable smtSatTime = System.Diagnostics.Stopwatch()

type SmtSatResult = 
    | SAT 
    | UNSAT 
    | UNKNOWN 
    | ERROR of string


type SmtSolver = 
    | Z3
    | CVC5


type SmtSatInstance<'T when 'T: comparison> = 
    {
        Term : SmtTerm<'T>
        SortMapping : Map<'T, SmtSort>
        VarStringer : 'T -> string
    }

type SmtInterface = 
    abstract isSat : SmtSatInstance<'T> -> SmtSatResult


/// Check if a given SMT Formula is satisfiable
let checkSatDirect 
    (solverConfig : SolverConfiguration)
    (solver : SmtSolver) 
    (instance : SmtSatInstance<'T>) =

    // Write the variables types for the SMTLIB query
    let declareVarsString =
        instance.Term
        |> SmtTerm.freeVars
        |> Set.toList
        |> List.map (fun x -> 
            let sort = 
                Map.tryFind x instance.SortMapping
                |> Option.defaultWith (fun _ -> raise <| ForExException $"No sort given for %A{x}")
            "(declare-fun " + 
            instance.VarStringer x + 
            " () " +
            SmtSort.asString sort +
            ")"
        )
        |> String.concat "\n"

    let query =
        "(set-logic ALL)\n" +
        declareVarsString + "\n" + 
        "(assert\n" +
        SmtTerm.toSMTLibString instance.VarStringer instance.Term +
        "\n)" + "\n" +
        "(check-sat)"

    let pathToFile = Path.Combine [|solverConfig.MainPath; "query.smt2"|]

    // Write the query to the file     
    File.WriteAllText(pathToFile, query)

    let cmd =
        match solver with 
        | Z3 -> 
            solverConfig.Z3Path
            |> Option.defaultWith (fun _ -> raise <| ForExException $"Request Z3 solver but path to Z3 was not given")
        | CVC5 -> 
            solverConfig.CVC5Path
            |> Option.defaultWith (fun _ -> raise <| ForExException $"Request cvc5 solver but path to cvc5 was not given")

    smtSatTime.Start()
    let res = Util.SubprocessUtil.executeSubprocess cmd pathToFile
    smtSatTime.Stop()

    if res.Stderr.Trim() <> "" then 
        SmtSatResult.ERROR (res.Stderr.Trim())
    else 
        if res.Stdout.Trim() = "unsat" then 
            SmtSatResult.UNSAT
        elif res.Stdout.Trim() = "sat" then 
            SmtSatResult.SAT
        elif res.Stdout.Trim() = "unknown" then 
            SmtSatResult.UNKNOWN
        else 
            SmtSatResult.ERROR $"Unexpected output by SMT solver: %s{res.Stdout}"


type private SmtSatHashInstance = 
    {
        Term : SmtTerm<string>
        SortMapping : Map<string, SmtSort>
    }


let createHashingInterface (solverConfig: SolverConfiguration) (solver) = 
    let hashingSatString = new Dictionary<SmtSatHashInstance, _>()

    {new SmtInterface with 

        member this.isSat (instance: SmtSatInstance<'T>) = 

            satQueryCount <- satQueryCount + 1

            let term = SmtTerm.simplify instance.Term

            let freeVars = SmtTerm.freeVars term

            let sortMapping = 
                instance.SortMapping
                |> Map.filter (fun k _ -> Set.contains k freeVars)


            let hashingInstance = 
                {
                    SmtSatHashInstance.Term = 
                        term
                        |> SmtTerm.map (fun x -> instance.VarStringer x)
                    SortMapping = 
                        sortMapping
                        |> Map.toSeq
                        |> Seq.map (fun (k, v) -> instance.VarStringer k, v
                            )
                        |> Map.ofSeq
                }

            let res = 
                if hashingSatString.ContainsKey hashingInstance then 
                    satCacheHitCount <- satCacheHitCount + 1
                    hashingSatString.[hashingInstance]
                else 
                    let res = checkSatDirect solverConfig solver {SmtSatInstance.Term = term; SortMapping = sortMapping; VarStringer = instance.VarStringer}
                    hashingSatString.Add (hashingInstance, res)
                    res

            res
        }
        