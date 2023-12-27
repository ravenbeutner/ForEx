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

module VerificationEntryPoint

open Util
open Configuration
open InputInstance
open SMT
open SMTUtil
open Statement
open StrongestPostComputer

let verify (smtInterface : SmtInterface) (logger : Logger) (input : VerificationInput) = 

    let programList = input.UnivList @ input.ExistsList

    // Check each program for syntax errors and inline any procedure calls
    let programList = 
        programList
        |> List.mapi (fun i p -> 
            match Program.findErrors p with 
            | None -> 
                Program.inlineProcedures p
            | Some err -> 
                raise <| ForExException $"Error in the %i{i}th program: %s{err}"
            )

    Set.union (SmtTerm.usedVars input.Pre) (SmtTerm.usedVars input.Post)
    |> Set.iter (fun (x,  i) -> 
        if i >= List.length programList then 
            raise <| ForExException $"The Pre-or post-condition used variable ('%s{x}', %i{i}) but there are only %i{List.length programList} programs"

        if programList.[i].TypeMapping.ContainsKey x |> not then 
            raise <| ForExException $"The Pre-or post-condition used variable ('%s{x}', %i{i}) but '%s{x}' is not defined in the %i{i} program"
    )

    let filteredHints = 
        input.InvHints
        |> List.filter (fun t -> 
            t
            |> SmtTerm.freeVars
            |> Set.forall (fun (x, i) -> Set.contains x (Statement.usedVars programList.[i].Statement))
            )

    let opt = 
        {
            AnalysisOptions.InvHints = filteredHints; 
            MaxConjunctsInLI= input.Options.MaxConjunctsInInv |> Option.defaultValue 2;
            MinConjunctsInLI = input.Options.MinConjunctsInInv |> Option.defaultValue 1;
            UseOnlyInvHints = input.Options.UseOnlyInvHints |> Option.defaultValue false;
            MaxLoopAlignments = input.Options.MaxTraces;
            MaxAsynchronousAlignments = input.Options.ExploreAsynchronousAlignments |> Option.defaultValue 1
        }

    let config: Configuration = 
        {
            SmtInterface = smtInterface;
            Logger = logger 
            AnalysisOptions = opt
        }

    let res = Verifier.verify config programList (input.UnivList.Length) input.Pre input.Post

    res
    