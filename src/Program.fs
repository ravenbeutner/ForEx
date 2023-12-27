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

module Program

open System.IO

open Util
open Configuration
open SMTUtil
open CommandLineParser


let run (args: array<string>) = 
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    // Start Parsing Console Input 
    let args = 
        if args.Length = 0 then 
            // In case no command line arguments are given, we assume the user wants the help message
            [|"--help"|]
        else 
            args

    let cmdArgs = 
        match CommandLineParser.parseCommandLineArguments (Array.toList args) with 
        | Result.Ok x -> x 
        | Result.Error err -> raise <| ForExException $"%s{err}" 

    let solverConfig = Configuration.getSolverConfiguration()

    let inputFile = 
        match cmdArgs.InputFile with 
        | Some f -> f 
        | None -> raise <| ForExException "Must specify an input file"

    let inputContent =   
        try 
            File.ReadAllText inputFile
        with 
        | _ ->  raise <| ForExException $"Could not open/read file %s{inputFile}"

    let input = 
        match InputInstance.parseInputContent inputContent with 
        | Result.Ok x -> x 
        | Result.Error err -> raise <| ForExException $"Could not parse input file: %s{err}" 

    let smtInterface = SMTUtil.createHashingInterface solverConfig (input.Options.SmtSolver |> Option.defaultValue Z3)

    let logger = 
        {
            Logger.Log = fun s -> 
                if cmdArgs.LogPrintouts then
                    printf $"{s}"
        }

    let res = VerificationEntryPoint.verify smtInterface logger input 

    logger.LogN "========================================\n"
    match res with 
    | true -> printfn "SAT"
    | false -> printfn "Could not be verified"
    logger.LogN "\n========================================\n"
    
    logger.LogN $"Total Time %i{sw.ElapsedMilliseconds}ms (~=%.2f{double(sw.ElapsedMilliseconds) / 1000.0}s)\n"

    let satTime = SMTUtil.smtSatTime.ElapsedMilliseconds

    logger.LogN $"SAT: %i{SMTUtil.satQueryCount} queries. %i{SMTUtil.satCacheHitCount} cache hits. Time: %i{satTime}ms (~=%.2f{double(satTime) / 1000.0}s)"
    

[<EntryPoint>]
let main args = 
    try 
        run args 
        0
    with 
    | ForExException err ->
        printfn "===================== ERROR =====================\n" 
        printfn $"{err}"
        printfn "\n===================== ERROR - END =====================\n" 
        // reraise()

        -1

    