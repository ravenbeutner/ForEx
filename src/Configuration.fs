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

module Configuration 

open System
open System.IO

open Util
open Json

type SolverConfiguration = 
    {
        MainPath : string
        Z3Path: option<string>
        CVC5Path: option<string>
    }

let private parseSolverConfiguration (s : string) =
    match Json.Parser.parseJsonString s with 
    | Result.Error err -> raise <| ForExException $"Could not parse config file: %s{err}"
    | Result.Ok x -> 
        {
            MainPath = "./"
            Z3Path =
                (Json.tryLookup "z3" x)
                |> Option.map (fun x -> 
                    Json.tryGetString x
                    |> Option.defaultWith (fun _ -> raise <| ForExException "Field 'z3' must contain a string")
                    )
            CVC5Path = 
                (Json.tryLookup "cvc5" x)
                |> Option.map (fun x -> 
                    Json.tryGetString x
                    |> Option.defaultWith (fun _ -> raise <| ForExException "Field 'cvc5' must contain a string")
                    )
        }
        

let getSolverConfiguration() = 
    // By convention the paths.json file is located in the same directory as the HyPA executable
    let configPath = 
        System.IO.Path.Join [|System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location); "paths.json"|]
                     
    // Check if the path to the config file is valid , i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        raise <| ForExException "The paths.json file does not exist in the same directory as the executable"            
    
    // Parse the config File
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                raise <| ForExException "Could not open paths.json file"

    let solverConfig = parseSolverConfiguration configContent

    if solverConfig.Z3Path.IsSome then 
        if System.IO.FileInfo(solverConfig.Z3Path.Value).Exists |> not then 
            raise <| ForExException "The given z3 executable does not exist"

    if solverConfig.CVC5Path.IsSome then 
        if System.IO.FileInfo(solverConfig.CVC5Path.Value).Exists |> not then 
            raise <| ForExException "The given cvc5 executable does not exist"

    solverConfig


type Logger = 
    {
        Log : string -> unit
    }

    member this.LogN = 
        fun s -> this.Log (s + "\n")

