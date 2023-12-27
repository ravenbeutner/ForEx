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

module InputInstance 

open System

open FParsec

open SMT
open Statement

type VerificationOptions = 
    {
        MaxConjunctsInInv : option<int>;
        MinConjunctsInInv : option<int>;
        UseOnlyInvHints : option<bool>;
        MaxTraces : option<int>;
        ExploreAsynchronousAlignments : option<int>
        SmtSolver : option<SMTUtil.SmtSolver>;
    }

type VerificationInput = 
    {
        UnivList : list<Program>; 
        ExistsList : list<Program>;
        Pre : SmtTerm<String * int>;
        Post : SmtTerm<String * int>;
        InvHints : list<SmtTerm<String * int>>;
        Comment : option<String>;
        Options : VerificationOptions
    }

type private VerificationInputTemp = 
    {
        UnivList : list<Program>; 
        ExistsList : list<Program>;
        Pre : option<SmtTerm<String * int>>;
        Post : option<SmtTerm<String * int>>;
        InvHints : list<SmtTerm<String * int>>;
        Comment : option<String>

        MaxConjunctsInInv : option<int>;
        MinConjunctsInInv : option<int>;
        UseOnlyInvHints : option<bool>;
        MaxTraces : option<int>;
        ExploreAsynchronousAlignments : option<int>
        SmtSolver : option<SMTUtil.SmtSolver>;
    }

    static member Default = 
        {
            UnivList = []
            ExistsList = []
            Pre = None
            Post = None
            InvHints = []
            MaxConjunctsInInv = None
            MinConjunctsInInv = None
            UseOnlyInvHints = None
            MaxTraces = None
            SmtSolver = None
            ExploreAsynchronousAlignments = None
            Comment = None
        }


let parseInputContent s = 
    let convertStringToAssertionVariable (s : String) = 
        let parts = s.Split '_'
        if parts.Length <> 2 then 
            None 
        else 
            try 
                let var = parts.[0]
                let index = Int32.Parse(parts.[1])

                (var, index)
                |> Some
            with 
                _ -> None

    let inputElementParser (config : VerificationInputTemp) = 
        let forallProgramParser = 
            skipString "[forall]" >>. spaces >>. Statement.Parser.programParser 
            |>> (fun p -> {config with UnivList = config.UnivList @ [p]})

        let existsProgramParser = 
            skipString "[exists]" >>. spaces >>. Statement.Parser.programParser 
            |>> (fun p -> {config with ExistsList = config.ExistsList @ [p]})

        let preParser = 
            skipString "[pre]" >>. spaces >>. SMT.Parser.infixTermParser SMT.Parser.symbolParser
            |>> (fun x -> 
                let f = x |> SmtTerm.map (fun s -> convertStringToAssertionVariable s |> Option.get)
                {config with Pre = Some f}
            ) 
        
        let postParser = 
            skipString "[post]" >>. spaces >>. SMT.Parser.infixTermParser SMT.Parser.symbolParser
            |>> (fun x -> 
                let f = x |> SmtTerm.map (fun s -> convertStringToAssertionVariable s |> Option.get)
                {config with Post = Some f}
            ) 

        let invHintParser = 
            skipString "[inv]" >>. spaces >>. SMT.Parser.infixTermParser SMT.Parser.symbolParser
            |>> (fun x -> 
                let f = x |> SmtTerm.map (fun s -> convertStringToAssertionVariable s |> Option.get)
                {config with InvHints = f :: config.InvHints}
            ) 

        let maxconjBoundParser = 
            skipString "[maxC]" >>. spaces >>. pint32
            |>> (fun x -> {config with MaxConjunctsInInv = Some x})

        let minconjBoundParser = 
            skipString "[minC]" >>. spaces >>. pint32
            |>> (fun x -> {config with MinConjunctsInInv = Some x})

        let traceBoundParser = 
            skipString "[traceBound]" >>. spaces >>. pint32
            |>> (fun x -> {config with MaxTraces = Some x})

        let onlyInvHintsParser = 
            stringReturn "[onlyHints]" {config with UseOnlyInvHints = Some true}

        let solverParserZ3 = 
            stringReturn "[z3]" {config with SmtSolver = Some SMTUtil.SmtSolver.Z3}
    
        let solverParserCvc5 = 
            stringReturn "[cvc5]" {config with SmtSolver = Some SMTUtil.SmtSolver.CVC5}

        let asynchronousParser = 
            skipString "[asynchronous]" >>. spaces >>. pint32
            |>> (fun x -> {config with ExploreAsynchronousAlignments = Some x})

        let commentParser = 
            skipString "[comment]" >>. spaces >>. manyChars anyChar
            |>> (fun x -> {config with Comment = Some x})

        spaces
        >>. choice [ 
                forallProgramParser
                existsProgramParser
                preParser
                postParser
                invHintParser
                maxconjBoundParser
                minconjBoundParser
                traceBoundParser
                solverParserZ3
                solverParserCvc5
                commentParser
                onlyInvHintsParser
                asynchronousParser
            ]
        .>> spaces

    let rec inputParser (config: VerificationInputTemp) =
        (attempt (inputElementParser config) >>= inputParser)
        <|>% config

    let parser = inputParser (VerificationInputTemp.Default)  .>> spaces .>> eof
    let res = run parser s
    match res with
        | Success (res, _, _) -> 
            if res.Pre.IsNone || res.Post.IsNone then 
                Result.Error "Must specify pre-and postcondition"
            else 
                {
                    VerificationInput.UnivList = res.UnivList
                    ExistsList = res.ExistsList
                    Pre = res.Pre |> Option.get
                    Post = res.Post |> Option.get
                    InvHints = res.InvHints
                    Comment = res.Comment
                    Options = 
                        {
                            MaxConjunctsInInv = res.MaxConjunctsInInv
                            MinConjunctsInInv = res.MinConjunctsInInv
                            UseOnlyInvHints = res.UseOnlyInvHints
                            MaxTraces = res.MaxTraces
                            SmtSolver = res.SmtSolver
                            ExploreAsynchronousAlignments = res.ExploreAsynchronousAlignments
                        }    
                }
                |> Result.Ok
        | Failure (err, _, _) -> Result.Error err
