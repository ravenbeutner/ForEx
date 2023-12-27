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

module SMT

open System
open FSharp.Collections



type PrePost = PRE | POST

type SmtSort =
    | INT 
    | BOOL
    | ARRAY of SmtSort * SmtSort
    | BITVECTOR of int 
    | STRING

module SmtSort = 
    let rec asString (s : SmtSort) = 
        match s with
        | INT -> "Int"
        | BOOL -> "Bool"
        | ARRAY(t1, t2) -> "(Array " + asString t1 + " " + asString t2 + ")"
        | BITVECTOR x -> "(_ BitVec " + string(x) + ")"
        | STRING -> "String"

    let rec abr (s : SmtSort) = 
        match s with
        | INT -> "int"
        | BOOL -> "bool"
        | ARRAY _ -> "array"
        | BITVECTOR _ -> "bv"
        | STRING -> "string"


type SmtOperator =   
    // Arithmetic
    | ADD 
    | SUB 
    | MUL 
    | MIN
    // Boolean
    | NOT 
    | AND
    | OR
    | IMPLIES
    // Equality
    | EQ 
    // Comparison
    | LE 
    | GE 
    | LT 
    | GT 
    // String functions
    | STR_LEN 
    | STR_APP 
    // Bitvector functions
    | BV_AND 
    | BV_OR 
    | BV_NOT
    | BV_EXTRACT of int * int
    // Array functions
    | ARRAY_SELECT
    | ARRAY_STORE
    // 
    | ITE

module SmtOperator = 
    let asSmtLibString o = 
        match o with 
        | ADD -> "+"
        | SUB -> "-"
        | MUL -> "*"
        | MIN -> "-"

        | NOT -> "not"
        | AND-> "and"
        | OR -> "or"
        | IMPLIES -> "=>"

        | EQ -> "="

        | LE -> "<="
        | GE -> ">="
        | LT -> "<"
        | GT -> ">"

        | STR_LEN -> "str.len"
        | STR_APP -> "str.++"

        | BV_AND -> "bvand"
        | BV_OR -> "bvor"
        | BV_NOT -> "bvnot"
        | BV_EXTRACT (l, u) -> "(_ extract " + string u + " " + string l + ")"
        
        | ARRAY_SELECT -> "select"
        | ARRAY_STORE -> "store"

        | ITE -> "ite"

type SmtConstant = 
    | IntConst of int64
    | StringConst of string
    | BoolConst of bool
    | BvConst of list<bool>

/// The type representing an SMT formula
type SmtTerm<'T when 'T : comparison> =
    | Var of 'T
    | Const of SmtConstant
    | App of SmtOperator * list<SmtTerm<'T>>
    | Forall of list<'T * SmtSort> * SmtTerm<'T>
    | Exists of list<'T * SmtSort> * SmtTerm<'T>
    | Let of list<'T * SmtTerm<'T>> * SmtTerm<'T>

module SmtTerm = 

    // ========== Abbreviations ==========
    let False = SmtTerm.Const (SmtConstant.BoolConst false)
    let True = SmtTerm.Const (SmtConstant.BoolConst true)

    let And xs = App(AND, xs)
    let Or xs = App(OR, xs)

    let Implies(a, b) = App(IMPLIES, [a; b])


    let ArrayStore(a, b, c) = App(ARRAY_STORE, [a; b; c])

    let Eq(a, b) = App(EQ, [a; b])

    let Not a = App(NOT, [a])

    // ========== Abbreviations - END ==========

    let rec usedVars (t : SmtTerm<'T>) =
        match t with
        | Var v -> Set.singleton v 
        | Const _ -> Set.empty
        | App (_, l) -> l |> List.map usedVars |> Set.unionMany
        | Forall(v, t) | Exists(v, t)   -> 
            (usedVars t, v)
            ||> List.fold (fun s (x, _) -> Set.add x s)
        | Let(_, _) -> raise <| NotImplementedException()


    let rec freeVars (t : SmtTerm<'T>) =
        match t with
        | Var v -> Set.singleton v 
        | Const _ -> Set.empty
        | App(_, l) ->
            l |> List.map freeVars |> Set.unionMany 
        | Forall(v, f) | Exists(v, f)   -> 
            List.fold (fun s (x, _)-> Set.remove x s) (freeVars f) v
        | Let(_, _) -> raise <| NotImplementedException()


    let rec topLevelConjuncts (t : SmtTerm<'T>) = 
        match t with 
        | App(AND, l) -> 
            l |> List.map topLevelConjuncts |> List.concat
        | _ -> [t]

    let rec map (m : 'T -> 'a) (t : SmtTerm<'T>) = 
        match t with
        | Var s -> Var (m s)
        | Const c -> Const c
        | App(n, l) -> App(n, List.map (map m) l)
        | Forall(v, t) -> Forall(List.map (fun (x, s) -> (m x, s)) v, map m t)
        | Exists(v, t) -> Exists(List.map (fun (x, s) -> (m x, s)) v, map m t)
        | Let _ -> raise <| NotImplementedException()
        
    let rec bind (m : 'T -> SmtTerm<'T>) (t : SmtTerm<'T>) = 
        match t with
        | Var s -> m s
        | Const c -> Const c
        | App(name, l) -> App(name, List.map (bind m) l)
        | Forall(v, t) -> Forall(List.map (fun (x, s) -> (x, s)) v, bind m t)
        | Exists(v, t) -> Exists(List.map (fun (x, s) -> (x, s)) v, bind m t)
        | Let _ -> raise <| NotImplementedException()
    
    let rec bindQuantifierFree (m : 'T -> SmtTerm<'A>) (t : SmtTerm<'T>) = 
        match t with
        | Var s -> m s
        | Const c -> Const c
        | App(name, l) -> App(name, List.map (bindQuantifierFree m) l)
        | Forall _ | Exists _ -> raise <| NotImplementedException()
        | Let _ -> raise <| NotImplementedException()

    let rec resolveLets (t : SmtTerm<'T>) = 
        match t with
        | Var s -> Var s
        | Const c -> Const c
        | App(n, l) -> App(n, List.map resolveLets l)
        | Forall(v, t) -> Forall(List.map (fun (x, s) -> (x, s)) v, resolveLets t)
        | Exists(v, t) -> Exists(List.map (fun (x, s) -> (x, s)) v, resolveLets t)
        | Let (bindings, body) ->   
            let m = Map.ofList bindings
            body
            |> resolveLets
            |> bind (fun x -> 
                if Map.containsKey x m then 
                    m.[x]
                else 
                    Var x 
                )

    let rec simplify (t : SmtTerm<'T>) = 
        match t with
        | Var s -> Var s
        | Const c -> Const c
        | App(ADD, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(ADD, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> function 
                | [] -> 0L |> IntConst |> Const
                | [x] -> x 
                | xs -> App(ADD, xs)
        | App(MIN, [t]) -> 
            match simplify t with 
            | App(MIN, [t1]) -> t1
            | t1 -> App(MIN, [t1])
        | App(MUL, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(MUL, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> function 
                | [] -> 1L |> IntConst |> Const
                | [x] -> x 
                | xs -> App(MUL, xs)
        | App(AND, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(AND, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> function 
                | [] -> true |> BoolConst |> Const
                | [x] -> x 
                | xs -> App(AND, xs)
        | App(OR, l) -> 
            l 
            |> List.map simplify
            |> List.map (fun x -> 
                match x with 
                | App(OR, l1) -> l1
                | _ -> [x])
            |> List.concat 
            |> function 
                | [] -> false |> BoolConst |> Const
                | [x] -> x 
                | xs -> App(OR, xs)
        | App(NOT, [t]) -> 
            match simplify t with 
            | App(NOT, [t1]) -> t1
            | t1 -> App(NOT, [t1])
        | App(ITE, [t1; t2; t3]) -> 
            match simplify t1 with 
            | Const (BoolConst true) -> simplify t2
            | Const (BoolConst false) -> simplify t3
            | x -> App(ITE, [x; simplify t2; simplify t3])
        | Forall(v, t) -> 
            if List.isEmpty v then 
                simplify t 
            else 
                Forall(v, simplify t)
        | Exists(v, t) -> 
            if List.isEmpty v then 
                simplify t 
            else 
                Exists(v, simplify t)
        | Let _ -> raise <| NotImplementedException()
        | App (f, l) -> 
            App(f, List.map simplify l)


    let rec mapFreeVars (m : 'T -> 'T) (t : SmtTerm<'T>) = 
        match t with
        | Var s -> Var (m s)
        | Const c -> Const c
        | App(f, l) -> App (f, List.map (mapFreeVars m) l)
        | Forall(v, t) -> 
            Forall(v, mapFreeVars (fun x -> if List.exists (fun (y, _) -> x = y) v then x else m x) t)
        | Exists(v, t) -> 
            Exists(v, mapFreeVars (fun x -> if List.exists (fun (y, _) -> x = y) v then x else m x) t)
        | Let _ -> raise <| NotImplementedException()


    let rec toSMTLibString (varStringer : 'T -> String) (t : SmtTerm<'T>)  =
        match t with
        | Var v -> varStringer v
        | Const (IntConst n) -> string(n)
        | Const (BoolConst b) -> 
            match b with 
            | true -> "true"
            | false -> "false"
        | Const (StringConst c) -> "\"" + c + "\""
        | Const (BvConst c) -> 
            c 
            |> List.map (function 
                | true -> "1"
                | false -> "0")
            |> String.concat ""
            |> fun x -> "#b" + x
        | App(f, l) ->
            l 
            |> List.map (toSMTLibString varStringer)
            |> String.concat " "
            |> fun x -> "(" + SmtOperator.asSmtLibString f + " " + x + ")"
        | Forall (v, b) -> 
            let bodyString = toSMTLibString varStringer b
            match v with 
            | [] -> 
                bodyString
            | _ -> 
                let args = 
                    v 
                    |> List.map (fun (v, s) -> "(" + varStringer v + " " + SmtSort.asString s + ")")
                    |> String.concat " "

                "(forall (" + args + ")" + bodyString + ")"

        | Exists (v, b) -> 
            let bodyString = toSMTLibString varStringer b
            match v with 
            | [] -> 
                bodyString
            | _ -> 
                let args = 
                    v 
                    |> List.map (fun (v, s) -> "(" + varStringer v + " " + SmtSort.asString s + ")")
                    |> String.concat " "

                "(exists (" + args + ")" + bodyString + ")"

        | Let (bindings, body) -> 
            let bindingsString = 
                bindings
                |> List.map (fun (n, t) -> 
                    "("+ varStringer n + " " + toSMTLibString varStringer t + ")"
                )
                |> String.concat " "

            "(let (" + bindingsString + ")" + toSMTLibString varStringer body + ")"

/// A Term that adnitially carries the sort for all free variables
type SortedSmtTerm<'T when 'T : comparison> = 
    {
        Term : SmtTerm<'T>
        VariableSort : Map<'T, SmtSort>
    }


module Parser = 
    open FParsec


    let private reservedWords = 
        [
            "BINARY"
            "DECIMAL"
            "HEXADECIMAL" 
            "NUMERAL" 
            "STRING"
            "_" 
            "!" 
            "as" 
            "let" 
            "exists" 
            "forall" 
            "match" 
            "par"
        ]

    /// Parses any possible symbol as defined by the SMTLIB standard
    let symbolParser : Parser<string, unit> = 
        let specialSymbolParser = 
            choice [
                pchar '~'
                pchar '!'
                pchar '@'
                pchar '%'
                pchar '^'
                pchar '&'
                pchar '*'
                pchar '_'
                pchar '-'
                pchar '+'
                pchar '='
                pchar '<'
                pchar '>'
                pchar '.'
                pchar '?'
                pchar '/'
            ]
        
        let simpleSymbolParser = 
            pipe2
                (letter <|> specialSymbolParser)
                (many (letter <|> digit <|> specialSymbolParser))
                (fun x y -> x :: y |> List.toArray |> String)

        let escapedStringParser = 
            pipe3 
                (pchar '|')
                (many (satisfy (fun c -> c <> '\\' && c <> '|')))
                (pchar '|')
                // We ignore the |s
                (fun _ x _ -> x |> List.toArray |> String)

        attempt
            (
                escapedStringParser <|> simpleSymbolParser
                >>= fun x -> if List.contains x reservedWords then fail "" else preturn x
            )

    let private operatorParser = 
        choice [
            stringReturn "str.++" STR_APP;
            stringReturn "str.len" STR_LEN;

            stringReturn "select" ARRAY_SELECT;
            stringReturn "store" ARRAY_STORE;

            stringReturn "bv.and" BV_AND;
            stringReturn "bv.or" BV_OR;
            stringReturn "bv.not" BV_NOT;

            (
                pipe2 
                    (skipString "(_extract" >>. spaces >>. pint32 .>> spaces) 
                    (pint32 .>> spaces .>> skipChar ')')
                    (fun l u -> BV_EXTRACT (l, u))
            )

            stringReturn "+" ADD;
            stringReturn "-" SUB;
            stringReturn "*" MUL;
            stringReturn "and" AND;
            stringReturn "or" OR;

            stringReturn "=" EQ;
            
            stringReturn "<=" LE;
            stringReturn ">=" GE;
            stringReturn "<" LT;
            stringReturn ">" GT;
            
            stringReturn "ite" ITE;
        ]

    let private sortParser : Parser<SmtSort, unit> = 
        choice [
            stringReturn "Int" SmtSort.INT
            stringReturn "Bool" SmtSort.BOOL
            stringReturn "String" SmtSort.STRING
            (skipString "(_BitVec" >>. spaces >>. pint32 .>> spaces .>> skipChar ')' |>> SmtSort.BITVECTOR)
        ]

    let termParser (varParser : Parser<'T, unit>) = 
        let termParser, termParserRef  = createParserForwardedToRef()
        
        let variableParser =
            varParser
            |>> Var

        let constantParser = 
            let intConstParser =
                pint64 |>> IntConst

            let bvConstParser =
                skipChar '#' >>. spaces >>. skipChar 'b' >>. spaces >>. many1 ((charReturn '0' false) <|> (charReturn '1' true))
                |>> BvConst

            let boolConstParser =
                stringReturn "true" (BoolConst true) <|> stringReturn "false" (BoolConst false)

            let stringConstParser =
                between (skipChar '"') (skipChar '"') (manyChars (satisfy (fun c -> c <> '"')))
                |>> StringConst

            choice [intConstParser; bvConstParser; boolConstParser; stringConstParser]
            |>> Const

        let appParser = 
            pipe3
                (skipChar '(' >>. spaces >>. operatorParser .>> spaces) 
                (many (termParser .>> spaces) .>> spaces)
                (skipChar ')')
                (fun f l _ -> App(f, l))

        let letParser =
            let parseAssign =
                spaces >>.
                pipe2
                    (skipChar '(' >>. varParser)
                    (spaces >>. termParser)
                    (fun x y -> (x, y))
                .>> spaces .>> skipChar ')'


            let parseSeq =
                spaces >>. skipChar '(' >>.
                many parseAssign
                .>> spaces .>> skipChar ')'

            pipe2
                (skipString "(let" >>. parseSeq)
                (termParser .>> spaces .>> skipChar ')')
                (fun a b -> Let(a, b))

        do termParserRef.Value <-
            spaces >>. choice [ 
                constantParser
                appParser
                letParser
                variableParser 
            ] .>> spaces

        termParser

    let infixTermParser (varParser : Parser<'T, unit>) = 
        let termParser, termParserRef  = createParserForwardedToRef()
        
        let variableParser =
            varParser
            |>> Var

        let constantParser = 
            let intConstParser =
                pint64 |>> IntConst

            let bvConstParser =
                skipChar '#' >>. spaces >>. skipChar 'b' >>. spaces >>. many1 ((charReturn '0' false) <|> (charReturn '1' true))
                |>> BvConst

            let boolConstParser =
                stringReturn "true" (BoolConst true) <|> stringReturn "false" (BoolConst false)

            let stringConstParser =
                between (skipChar '"') (skipChar '"') (manyChars (satisfy (fun c -> c <> '"')))
                |>> StringConst

            choice [intConstParser; bvConstParser; boolConstParser; stringConstParser]
            |>> Const

        let parParser =
            skipString "(" >>. termParser .>> skipChar ')'


        let opp : OperatorPrecedenceParser<SmtTerm<'T>,unit,unit>=
            new OperatorPrecedenceParser<SmtTerm<'T>, unit, unit>()

        let addInfixOperator string precedence associativity f =
            opp.AddOperator(
                InfixOperator(string, spaces, precedence, associativity, f)
            )

        let addPrefixOperator string precedence associativity f =
            opp.AddOperator(
                PrefixOperator(string, spaces, precedence, associativity, f)
            )

        let addTernaryOperator lstring rstring precedence associativity f =
            opp.AddOperator(
                TernaryOperator(lstring, spaces, rstring, spaces, precedence, associativity, f)
            )

        addInfixOperator "str.++" 90 Associativity.Left (fun e1 e2 -> SmtTerm.App (STR_APP, [e1; e2]))
        addPrefixOperator "str.len" 90 true (fun e1 -> SmtTerm.App (STR_LEN, [e1]))

        addInfixOperator "bv.&" 50 Associativity.Left (fun e1 e2 -> SmtTerm.App (BV_AND, [e1; e2]))
        addInfixOperator "bv.|" 40 Associativity.Left (fun e1 e2 -> SmtTerm.App (BV_AND, [e1; e2]))
        addPrefixOperator "bv.!" 60 true (fun x -> SmtTerm.App (BV_NOT, [x]))


        addInfixOperator "*" 95 Associativity.Left (fun e1 e2 -> SmtTerm.App (MUL, [e1; e2]))

        addInfixOperator "+" 90 Associativity.Left (fun e1 e2 -> SmtTerm.App (ADD, [e1; e2]))
        addInfixOperator "-" 80 Associativity.Left (fun e1 e2 -> SmtTerm.App (SUB, [e1; e2]))
        addPrefixOperator "-" 100 true (fun x -> SmtTerm.App (MIN, [x]))

        addInfixOperator "==" 70 Associativity.Left (fun e1 e2 -> SmtTerm.App (EQ, [e1; e2]))
        addInfixOperator "!=" 70 Associativity.Left (fun e1 e2 -> SmtTerm.App(NOT, [SmtTerm.App (EQ, [e1; e2])]))
        addInfixOperator "<=" 70 Associativity.Left (fun e1 e2 -> SmtTerm.App (LE, [e1; e2]))
        addInfixOperator ">=" 70 Associativity.Left (fun e1 e2 -> SmtTerm.App (GE, [e1; e2]))
        addInfixOperator "<" 70 Associativity.Left (fun e1 e2 -> SmtTerm.App (LT, [e1; e2]))
        addInfixOperator ">" 70 Associativity.Left (fun e1 e2 -> SmtTerm.App (GT, [e1; e2]))

        addInfixOperator "&&" 50 Associativity.Left (fun e1 e2 -> SmtTerm.App (AND, [e1; e2]))
        
        addInfixOperator "||" 40 Associativity.Left (fun e1 e2 -> SmtTerm.App (OR, [e1; e2]))
        addPrefixOperator "!" 60 true (fun x -> SmtTerm.App (NOT, [x]))
        addInfixOperator "=>" 30 Associativity.Left (fun e1 e2 -> SmtTerm.App (IMPLIES, [e1; e2]))

        addTernaryOperator "?" ":" 30 Associativity.None (fun s1 s2 s3 -> SmtTerm.App (ITE, [s1; s2; s3]))


        let basicParser = 
            spaces >>. choice [ 
                constantParser
                (attempt variableParser)
                parParser
            ] .>> spaces


        opp.TermParser <- basicParser

        do termParserRef.Value <- opp.ExpressionParser

        termParser

    /// Given a parser for variables, parses a given string to a term
    let parseSmtTerm s = 
        let parser = 
            spaces >>. termParser symbolParser .>> spaces .>> eof
        let res = run parser s
        match res with
            | Success (res, _, _) -> Result.Ok res
            | Failure (err, _, _) -> Result.Error err

