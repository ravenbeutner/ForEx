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

module CommandLineParser

type CommandLineArguments = 
    {
        InputFile : option<string>
        LogPrintouts : bool
    }

    static member Default = 
        {
            InputFile = Option.None
            LogPrintouts = false
        }

let parseCommandLineArguments (args : list<string>) =
    let rec parseArgumentsRec (args : list<string>) (opt : CommandLineArguments) = 
        match args with 
        | [] -> Result.Ok opt
        | x::xs -> 
            match x with 
            | "--log" -> 
                parseArgumentsRec xs { opt with LogPrintouts = true }

            | "-h" | "--help" -> 
                printfn "ForEx (Version 1.0)"
                printfn "usage: ForEx input_file"
                exit 0

            | "--version"  -> 
                printfn "ForEx (Version 1.0)"

                exit 0
            | s when s <> "" && s.Trim().StartsWith "-" -> 
                Result.Error ("Option " + s + " is not supported" )
            | _ ->
                // When no option is given, we assume that this is the input 
                if opt.InputFile.IsSome then 
                    Result.Error "Input files cannot be given more than once"
                else 
                    parseArgumentsRec xs {opt with InputFile = Some x}
        
    parseArgumentsRec args CommandLineArguments.Default
