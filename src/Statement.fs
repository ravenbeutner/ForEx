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

module Statement 

open SMT

type Var = string
type ProcedureName = string

type VarType = 
    | IntType
    | BoolType
    | StringType
    | ArrayType of VarType * list<VarType> 
    | BitvectorType of int 


module VarType = 
    let rec asSMTSort t = 
        match t with 
        | IntType -> SmtSort.INT
        | BoolType -> SmtSort.BOOL
        | StringType -> SmtSort.STRING
        | ArrayType(t, args) -> 
            (args, asSMTSort t)
            ||> List.foldBack (fun s x -> SmtSort.ARRAY(asSMTSort s, x))
        | BitvectorType x -> SmtSort.BITVECTOR x
            

type TypeMapping = Map<Var, VarType>

type ExpressionOperator =   
    | ADD 
    | SUB 
    | MUL 
    | MIN 
    //
    | NOT 
    | AND
    | OR
    //
    | EQ 
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
    // 
    | ITE

module ExpressionOperator = 
    let toSmtOperator o = 
        match o with 
        | ADD -> SmtOperator.ADD
        | SUB -> SmtOperator.SUB
        | MUL -> SmtOperator.MUL
        | MIN -> SmtOperator.MIN
        //
        | NOT -> SmtOperator.NOT
        | AND -> SmtOperator.AND
        | OR -> SmtOperator.OR
        //
        | EQ -> SmtOperator.EQ
        | LE -> SmtOperator.LE
        | GE -> SmtOperator.GE
        | LT -> SmtOperator.LT
        | GT -> SmtOperator.GT
        //
        | ITE -> SmtOperator.ITE
        //
        | STR_APP -> SmtOperator.STR_APP
        | STR_LEN -> SmtOperator.STR_LEN

        | ARRAY_SELECT -> SmtOperator.ARRAY_SELECT

        | BV_AND -> SmtOperator.BV_AND
        | BV_OR -> SmtOperator.BV_OR
        | BV_NOT -> SmtOperator.BV_NOT
        | BV_EXTRACT (l, u) -> SmtOperator.BV_EXTRACT (l, u)


type Expression = 
    | IntConst of int
    | BoolConst of bool
    | StringConst of string
    | BvConst of list<bool>
    | Var of Var
    | App of ExpressionOperator * list<Expression>

module Expression = 
    let rec usedVars (e : Expression) = 
        match e with 
        | IntConst _ | BoolConst _ | StringConst _ | BvConst _ -> Set.empty
        | Var x -> Set.singleton x 
        | App(_, args) -> args |> List.map usedVars |> Set.unionMany

    let rec inferType (typeEnv : Var -> VarType) (e : Expression) = 
        match e with 
        | IntConst _ -> IntType |> Some
        | BoolConst _ -> BoolType |> Some
        | StringConst _ -> StringType |> Some
        | BvConst l -> (BitvectorType (l.Length)) |> Some
        | Var x -> typeEnv x |> Some
        // ============== Arithmetic Functions ==============
        | App (ADD, [e1; e2]) | App (SUB, [e1; e2]) | App (MUL, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some IntType, Some IntType -> Some IntType
            | _ -> None
        | App (MIN, [e]) ->
            match inferType typeEnv e with 
            | Some IntType -> Some IntType
            | _ -> None
        | App (LE, [e1; e2]) | App (GE, [e1; e2])| App (LT, [e1; e2])| App (GT, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some IntType, Some IntType -> Some BoolType
            | _ -> None
        // ============== Bool Functions ==============
        | App (NOT, [e]) ->
            match inferType typeEnv e with 
            | Some BoolType -> Some BoolType
            | _ -> None
        | App (AND, [e1; e2]) | App (OR, [e1; e2]) ->
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some BoolType, Some BoolType -> Some BoolType
            | _ -> None
        
        // ============== String Functions ==============
        | App (STR_APP, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some StringType, Some StringType -> Some StringType
            | _ -> None
        | App (STR_LEN, [e1]) -> 
            match inferType typeEnv e1 with 
            | Some StringType -> Some IntType
            | _ -> None
        // ============== BV Functions ==============
        | App (BV_AND, [e1; e2]) | App (BV_OR, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some (BitvectorType n), Some (BitvectorType m) when n = m -> Some (BitvectorType m)
            | _ -> None
        | App (BV_NOT, [e1]) -> 
            match inferType typeEnv e1 with 
            | Some (BitvectorType n) -> Some (BitvectorType n)
            | _ -> None
        | App (BV_EXTRACT(l, u), [e1]) -> 
            match inferType typeEnv e1 with 
            | Some (BitvectorType n) -> 
                if l <= 0 && l <= u && u < n then 
                    Some (BitvectorType (u - l + 1))
                else 
                    None 
            | _ -> None
        // ============== Array Functions ==============
        | App (ARRAY_SELECT, (Var n) :: args) -> 
            match typeEnv n with 
            | ArrayType(t, targs) ->
                if List.length args <> List.length targs then 
                    None 
                elif 
                    List.zip args targs 
                    |> List.forall (fun (x, t) -> match inferType typeEnv x with Some t' when t = t' -> true | _ -> false)  
                then 
                    Some t
                else 
                    // Wrong number of arguments
                    None
            | _ -> None
        // ============== General Functions ==============
        | App (EQ, [e1; e2]) -> 
            match inferType typeEnv e1, inferType typeEnv e2 with 
            | Some x, Some y when x = y -> Some BoolType
            | _ -> None
        | App (ITE, [e1; e2; e3]) ->
            match inferType typeEnv e1, inferType typeEnv e2, inferType typeEnv e3 with 
            | Some BoolType, Some t1, Some t2 when t1 = t2 -> Some t1 
            | _ -> None
        | App (_, _) -> 
            None

    let rec map f (e : Expression) = 
        match e with 
        | IntConst c -> IntConst c 
        | StringConst c -> StringConst c 
        | BoolConst c -> BoolConst c 
        | BvConst c -> BvConst c 
        | Var x -> Var (f x) 
        | App(o, args) -> App(o, args |> List.map (map f))

    let rec bind f (e : Expression) = 
        match e with 
        | IntConst c -> IntConst c 
        | StringConst c -> StringConst c 
        | BoolConst c -> BoolConst c 
        | BvConst c -> BvConst c 
        | Var x -> f x
        | App(o, args) -> App(o, args |> List.map (bind f))

    let rec asSmtTerm (e : Expression) = 
        match e with 
        | IntConst c -> SmtTerm.Const (SmtConstant.IntConst (int64 c))
        | StringConst c -> SmtTerm.Const (SmtConstant.StringConst c)
        | BoolConst c -> SmtTerm.Const (SmtConstant.BoolConst c)
        | BvConst c -> SmtTerm.Const (SmtConstant.BvConst c)
        | Var x -> SmtTerm.Var x 
        | App(f, args) -> SmtTerm.App(ExpressionOperator.toSmtOperator f, args |> List.map asSmtTerm)

    let rec haveSameStructure e1 e2 = 
        match e1, e2 with 
        | IntConst _, IntConst _ -> true
        | BoolConst _, BoolConst _ -> true
        | StringConst _, StringConst _ -> true
        | BvConst _, BvConst _ -> true
        | Var _, Var _ -> true
        | App(f1, args1), App(f2, args2) when f1 = f2 && List.length args1 = List.length args2 -> 
            List.zip args1 args2
            |> List.forall (fun (a, b) -> haveSameStructure a b)
        | _ -> false
    

type Statement = 
    | Terminated
    | Skip 
    | VarAssign of Var * Expression
    | ArrayAssign of Var * list<Expression> * Expression
    | If of Expression * Statement * Statement
    | Seq of Statement * Statement 
    | Nondet of Statement * Statement 
    | NondetAssign of Var
    | Assume of Expression
    | Assert of Expression
    | While of Expression * Statement
    | FunctionCall of Var * ProcedureName * list<Expression>

module Statement = 
    let rec usedVars s = 
        match s with 
        | Terminated | Skip -> Set.empty
        | VarAssign(x, e) -> Set.add x (Expression.usedVars e)
        | ArrayAssign (x, pos, e) -> 
            pos 
            |> List.map Expression.usedVars
            |> Set.unionMany
            |> Set.union (Expression.usedVars e)
            |> Set.add x
        | If (e, s1, s2) -> Set.unionMany [Expression.usedVars e; usedVars s1; usedVars s2]
        | Seq(s1, s2) | Nondet(s1, s2) -> Set.union (usedVars s1) (usedVars s2)
        | NondetAssign x -> Set.singleton x 
        | Assume e -> Expression.usedVars e
        | Assert e -> Expression.usedVars e
        | While(e, s) -> Set.union (Expression.usedVars e) (usedVars s)
        | FunctionCall (r, _, args) -> 
            args 
            |> List.map Expression.usedVars
            |> Set.unionMany
            |> Set.add r

    let rec usedProcedures (s : Statement) = 
        match s with 
        | Terminated | Skip | VarAssign _ | NondetAssign _ | Assume _ | Assert _ | ArrayAssign _ -> Set.empty
        | If (_, s1, s2) | Seq(s1, s2) | Nondet(s1, s2) -> Set.union (usedProcedures s1) (usedProcedures s2)
        | While(_, s) -> usedProcedures s
        | FunctionCall (_, f, _) -> Set.singleton f

    let rec mapVars f (s : Statement) =
        match s with 
        | Terminated -> Terminated
        | Skip -> Skip
        | VarAssign(x, e) -> VarAssign(f x, Expression.map f e)
        | ArrayAssign(x, pos, e) -> ArrayAssign(f x, List.map (Expression.map f) pos, Expression.map f e)
        | If (e, s1, s2) -> If (Expression.map f e, mapVars f s1, mapVars f s2)
        | Seq(s1, s2) -> Seq(mapVars f s1, mapVars f s2) 
        | Nondet(s1, s2) -> Nondet(mapVars f s1, mapVars f s2) 
        | NondetAssign x -> NondetAssign (f x)
        | Assume e -> Assume (Expression.map f e)
        | Assert e -> Assert (Expression.map f e)
        | While(e, s) -> While(Expression.map f e, mapVars f s)
        | FunctionCall (x, name, args) -> FunctionCall(f x, name, args |> List.map (fun x -> Expression.map f x))


    exception private CheckTypeException of string
    let findTypeError (typeEnv : Var -> VarType) (procEnv : Var -> list<VarType> * VarType) (s : Statement) =  
        let rec checkTypeRec (s : Statement) = 
            match s with 
            | Terminated -> ()
            | Skip -> ()
            | VarAssign(x, e) -> 
                match Expression.inferType typeEnv e with 
                | Some t -> 
                    if t = typeEnv x then
                        ()
                    else 
                        raise <| CheckTypeException $"In variable assignment %s{x} := %A{e} the type of %s{x} (%A{typeEnv x}) does not match that of the expression (%A{t})"
                | _ -> 
                    raise <| CheckTypeException $"In variable assignment %s{x} := %A{e} the expression could not be typed."
            | ArrayAssign (x, args, e) -> 
                match typeEnv x with 
                | ArrayType(t, targs) ->
                    match Expression.inferType typeEnv e with 
                    | None -> raise <| CheckTypeException  $"In Array Assignment %s{x}%A{args} := %A{e}: Could not derive a type for %A{e}" 
                    | Some t' -> 
                        if t <> t' then 
                            raise <| CheckTypeException  $"In Array Assignment %s{x}%A{args} := %A{e} the target type of %s{x} (%A{t}) does not match that of the expression (%A{t'})"

                        if List.length args <> List.length targs then 
                            raise <| CheckTypeException  $"In Array Assignment %s{x}%A{args} := %A{e}: Mismatch in array dimension"

                        List.zip args targs 
                        |> List.iteri (fun i (eArg, targetType) -> 
                            match Expression.inferType typeEnv eArg with
                            | None -> raise <| CheckTypeException $"In Array Assignment %s{x}%A{args} := %A{e}: Could not infer the type of %A{eArg}"
                            | Some actualType -> 
                                if targetType <> actualType then 
                                    raise <| CheckTypeException $"In Array Assignment %s{x}%A{args} := %A{e}: The type of the %i{i}th expression %A{eArg} does not match the %i{i} argument type of $s{x}."
                            )
                | _ -> raise <| CheckTypeException  $"In Array Assignment %s{x}%A{args} := %A{e}: Variable %s{x} does not have a Array type"
            | If (e, s1, s2) -> 
                match Expression.inferType typeEnv e with 
                | Some BoolType -> 
                    checkTypeRec s1
                    checkTypeRec s2
                | _ -> 
                    raise <| CheckTypeException $"In conditional: expression %A{e} could not be typed with bool"
            | Seq(s1, s2) -> 
                checkTypeRec s1
                checkTypeRec s2
            | Nondet(s1, s2) -> 
                checkTypeRec s1
                checkTypeRec s2
            | NondetAssign _ -> ()
            | Assume e -> 
                match Expression.inferType typeEnv e with 
                | Some BoolType -> () 
                | _ -> 
                    raise <| CheckTypeException $"In assume: expression %A{e} could not be typed with bool"
            | Assert e -> 
                match Expression.inferType typeEnv e with 
                | Some BoolType -> () 
                | _ -> 
                    raise <| CheckTypeException $"In assert: expression %A{e} could not be typed with bool"
            | While(e, s) -> 
                match Expression.inferType typeEnv e with 
                | Some BoolType -> checkTypeRec s
                | _ -> raise <| CheckTypeException $"In while loop: expression %A{e} could not be typed with bool"
            | FunctionCall (x, f, args) -> 
                let argTypes, returnType = procEnv f

                if List.length args <> List.length argTypes then 
                    raise <| CheckTypeException $"In Call to %s{x}: Mismatch in domain dimension"

                List.zip args argTypes
                |> List.iteri (fun i (e, t) -> 
                    match Expression.inferType typeEnv e with 
                    | None -> raise <| CheckTypeException$"In Call to %s{x}: The %i{i}th argument could not be typed."  
                    | Some t' -> 
                        if t <> t' then 
                            raise <| CheckTypeException $"In Call to %s{x}: Mismatch in the type of the %i{i}th argument."     
                )

                if typeEnv x <> returnType then 
                    raise <| CheckTypeException $"In call to function %s{f}: Mismatch in the type of the return value"  
               

        try 
            checkTypeRec s
            None
        with 
        | CheckTypeException err -> 
            Some err

    let rec containsLoop s = 
        match s with 
        | Terminated | Skip | VarAssign _ | ArrayAssign _ | NondetAssign _ | Assume _ | Assert _ | FunctionCall _ -> false
        | If (_, s1, s2) | Nondet(s1, s2) | Seq(s1, s2) -> containsLoop s1 || containsLoop s2
        | While _ -> true

    let rec modifiedVars s = 
        match s with 
        | Terminated | Skip | Assume _ | Assert _ -> Set.empty
        | VarAssign (x, _) | ArrayAssign (x, _, _) | NondetAssign x -> Set.singleton x
        | If (_, s1, s2) | Seq(s1, s2) | Nondet(s1, s2) -> Set.union (modifiedVars s1) (modifiedVars s2)
        | While(_, s) -> modifiedVars s
        | FunctionCall (x, _, _) -> Set.singleton x

    
type StatementTypePair = 
    {
        Statement : Statement;
        TypeMapping : TypeMapping
    }


type ProcedureDeclaration = 
    {
        Name : Var;
        Arguments : list<Var>;
        ReturnType : VarType
        ReturnExpression : Expression;
        Body : Statement;
        TypeMapping : TypeMapping;
    }

type Program =  
    {
        Procedures : list<ProcedureDeclaration>;
        Main : Statement;
        MainTypeMapping : TypeMapping;
    }


module Program = 
    exception private ProgramError of string

    let findErrors (p : Program)  = 
        try 
            p.Main
            |> Statement.usedVars
            |> Set.iter (fun x -> 
                if Map.containsKey x p.MainTypeMapping |> not then 
                    raise <| ProgramError $"Variable %s{x} is used in the main program but not declared."
            )

            p.Main
            |> Statement.usedProcedures
            |> Set.iter (fun x -> 
                if p.Procedures |> List.exists (fun pd' -> pd'.Name = x) |> not then
                    raise <| ProgramError $"The main code calls procedure %s{x}, but this procedure is not defined (no recursive calls)"
            )

            p.Procedures
            |> List.iter (fun pd -> 
                Set.union (Statement.usedVars pd.Body) (pd.Arguments |> set)
                |> Set.iter (fun x -> 
                    if Map.containsKey x pd.TypeMapping |> not then 
                        raise <| ProgramError $"Variable %s{x} is used in procedure %s{pd.Name} but not declared in %s{pd.Name}'s local variable declaration."
                ) 

                pd.ReturnExpression
                |> Expression.usedVars
                |> Set.iter (fun x -> 
                    if Map.containsKey x p.MainTypeMapping |> not then 
                        raise <| ProgramError $"Variable %s{x} is used in the return expression of procedure %s{pd.Name} but not declared."
                )
                
                pd.Body
                |> Statement.usedProcedures
                |> Set.iter (fun x -> 
                    if p.Procedures |> List.exists (fun pd' -> pd'.Name = x && pd.Name <> pd'.Name) |> not then
                        raise <| ProgramError $"Procedure %s{pd.Name} calls procedure %s{x}, but this procedure is not defined (no recursive calls)"
                    )
                )

            let procTypes = 
                p.Procedures
                |> List.map (fun pd -> 
                    let argTypes = 
                        pd.Arguments
                        |> List.map (fun x -> pd.TypeMapping.[x])

                    pd.Name, (argTypes, pd.ReturnType)
                    )
                |> Map.ofList

            match p.Main |> Statement.findTypeError (fun x -> p.MainTypeMapping.[x]) (fun x -> procTypes.[x]) with 
            | None -> () 
            | Some e -> raise <| ProgramError $"The main body is not well typed: %s{e}"

            p.Procedures
            |> List.iter (fun pd -> 
                match  pd.Body |> Statement.findTypeError (fun x -> pd.TypeMapping.[x]) (fun x -> procTypes.[x]) with 
                | None -> () 
                | Some e -> raise <| ProgramError $"The body of procedure %s{pd.Name} is not well typed: %s{e}"
                )

            None 

        with 
        | ProgramError err -> 
            Some err

    let inlineProcedures (p : Program) = 
        let inlineProc (pd : ProcedureDeclaration) (args : list<Expression>) (returnVar : Var) = 
            assert(pd.Arguments.Length = args.Length)

            let argsTransfer = 
                List.zip pd.Arguments args 
                |> List.map (fun (v, e) -> 
                    Statement.VarAssign(pd.Name + "@" + v, e)
                    )
                |> List.reduce (fun x y -> Statement.Seq (x, y))

            let body = pd.Body |> Statement.mapVars (fun x -> pd.Name + "@" + x)

            let returnTransfer = Statement.VarAssign(returnVar, pd.ReturnExpression |> Expression.map (fun v -> pd.Name + "@" + v))

            Seq(argsTransfer, Seq(body, returnTransfer))

        let rec transformProgram s = 
            match s with 
            | Terminated -> Terminated
            | Skip -> Skip
            | VarAssign(x, e) -> VarAssign(x, e)
            | ArrayAssign (x, args, s) -> ArrayAssign(x, args, s)
            | If (e, s1, s2) -> If (e, transformProgram s1, transformProgram s2)
            | Seq(s1, s2) -> Seq(transformProgram s1, transformProgram s2) 
            | Nondet(s1, s2) -> Nondet(transformProgram s1, transformProgram s2) 
            | NondetAssign x -> NondetAssign x
            | Assume e -> Assume e
            | Assert e -> Assert e
            | While(e, s) -> While(e, transformProgram s)
            | FunctionCall (x, f, args) -> 
                let pd = 
                    p.Procedures
                    |> List.find (fun pd -> pd.Name = f)
                inlineProc pd args x

        let s = transformProgram p.Main

        let t = 
            p.Procedures
            |> List.map (fun pd -> 
                pd.TypeMapping
                |> Map.toList
                |> List.map (fun (k, x) -> pd.Name + "@" + k, x)
                )
            |> List.concat
            |> List.append (Map.toList p.MainTypeMapping)
            |> Map.ofList

        {Statement = s; TypeMapping = t}


module Parser = 
    open FParsec

    let commentLineParser =
        (skipString "//" .>> restOfLine false)

    let commentBlockParser =
        skipString "/*" >>. manyCharsTill anyChar (skipString "*/")
        |>> ignore

    let ws = spaces .>> sepEndBy (commentLineParser <|> commentBlockParser) spaces // whitespace and comment parser

    let private keywords = 
        [
            "if";
            "else";
            "while";
            "int";
            "bool";
            "string";
            "proc";
            "call";
            "str.++";
            "str.len";
            "bv.&";
            "bv.|";
            "bv.not"
            "return"
        ]

    let variableParser =
        Util.ParserUtil.programVariableParser
        >>= (fun x -> 
            if List.contains x keywords then 
                fail ""
            else 
                preturn x
            )

    let functionNameParser = variableParser

    /// Given a parser for variables, construct a parser for SMT Lib formulas
    let private expressionParser = 
        let expressionParser, expressionParserRef  = createParserForwardedToRef()
        
        let varParser =
            (variableParser .>> ws)
            >>= (fun v -> 
                    // Check if this is actually an array access, a BV access or a plain variable
                    (
                        many1 (skipChar '[' >>. ws >>. expressionParser .>> ws .>> skipChar ']')
                        |>> (fun args -> 
                            Expression.App(ExpressionOperator.ARRAY_SELECT, (Var v) :: args)
                        )
                    )
                    <|>
                    (
                        pipe2 
                            (skipChar '{' >>. ws >>. pint32 .>> ws .>> skipChar ',')
                            (ws >>. pint32 .>> ws .>> skipChar '}')
                            (fun l u -> 
                                Expression.App(ExpressionOperator.BV_EXTRACT (l, u), [Var v])
                            )
                    )
                    <|>
                    (preturn (Var v))
                )

        let boolConstParser =
            stringReturn "true" (Expression.BoolConst true) <|> stringReturn "false" (Expression.BoolConst false)

        let intConstParser =
            pint32 |>> IntConst

        let bvConstParser = 
            skipChar '#' >>. ws >>. skipChar 'b' >>. ws >>. many1 ((charReturn '0' false) <|> (charReturn '1' true))
            |>> BvConst

        let stringConstParser =
            between (skipChar '"') (skipChar '"') (manyChars (satisfy (fun c -> c <> '"')))
            |>> StringConst

        let ifParser = 
            pipe3
                (skipString "if" >>. ws >>. expressionParser .>> ws)
                (skipString "then" >>. ws >>. expressionParser .>> ws)
                (skipString "else" >>. ws >>. expressionParser .>> ws)
                (fun a b c -> App(ITE, [a; b; c]))

        let parParser =
            skipString "(" >>. expressionParser .>> skipChar ')'

    
        let opp : OperatorPrecedenceParser<Expression,unit,unit>=
            new OperatorPrecedenceParser<Expression, unit, unit>()

        let addInfixOperator string precedence associativity f =
            opp.AddOperator(
                InfixOperator(string, ws, precedence, associativity, f)
            )

        let addPrefixOperator string precedence associativity f =
            opp.AddOperator(
                PrefixOperator(string, ws, precedence, associativity, f)
            )

        let addTernaryOperator leftString rightString precedence associativity f =
            opp.AddOperator(
                TernaryOperator(leftString, ws, rightString, ws, precedence, associativity, f)
            )
        
        addInfixOperator "str.++" 90 Associativity.Left (fun e1 e2 -> App(STR_APP, [e1; e2]))
        addPrefixOperator "str.len" 90 true (fun e1 -> App(STR_LEN, [e1]))

        addInfixOperator "bv.&" 90 Associativity.Left (fun e1 e2 -> App(BV_AND, [e1; e2]))
        addInfixOperator "bv.|" 90 Associativity.Left (fun e1 e2 -> App(BV_OR, [e1; e2]))
        addPrefixOperator "bv.!" 90 true (fun e1 -> App(BV_NOT, [e1]))

        addInfixOperator "+" 90 Associativity.Left (fun e1 e2 -> App(ADD, [e1; e2]))
        addInfixOperator "*" 95 Associativity.Left (fun e1 e2 -> App(MUL, [e1; e2]))
        addInfixOperator "-" 80 Associativity.Left (fun e1 e2 -> App(SUB, [e1; e2]))
        addPrefixOperator "-" 100 true (fun x -> App(MIN, [x]))

        addInfixOperator "==" 70 Associativity.None (fun e1 e2 -> App(EQ, [e1; e2]))
        addInfixOperator "!=" 70 Associativity.None (fun e1 e2 -> App(NOT, [App(EQ, [e1; e2])]))
        addInfixOperator "<=" 70 Associativity.None (fun e1 e2 -> App(LE, [e1; e2]))
        addInfixOperator ">=" 70 Associativity.None (fun e1 e2 -> App(GE, [e1; e2]))
        addInfixOperator "<" 70 Associativity.None (fun e1 e2 -> App(LT, [e1; e2]))
        addInfixOperator ">" 70 Associativity.None (fun e1 e2 -> App(GT, [e1; e2]))

        addInfixOperator "&&" 50 Associativity.Left (fun e1 e2 -> App(AND, [e1; e2]))
        addInfixOperator "||" 40 Associativity.Left (fun e1 e2 -> App(OR, [e1; e2]))
        addPrefixOperator "!" 60 true (fun x -> App(NOT, [x]))


        addTernaryOperator "?" ":" 30 Associativity.None (fun e1 e2 e3 -> App(ITE, [e1; e2; e3]))

        let basicParser = 
            ws >>. choice [ 
                ifParser
                parParser
                boolConstParser
                stringConstParser
                intConstParser
                bvConstParser
                varParser
            ] .>> ws

        opp.TermParser <- basicParser

        do expressionParserRef.Value <- opp.ExpressionParser
        
        expressionParser

    let statementParser = 
        let statementParser, statementParserRef  = createParserForwardedToRef()

        let assumeParser = 
            skipString "assume" >>. ws >>. expressionParser
            |>> Assume

        let ifParser = 
            let elIfParser = 
                pipe2
                    (skipString "elif" >>. ws >>. expressionParser .>> ws)
                    (skipChar '{' >>. statementParser .>> skipChar '}' .>> ws)
                    (fun g s -> (g, s))

            let elseParser = 
                (skipString "else" >>. ws >>. skipChar '{' >>. ws >>. statementParser .>> skipChar '}')

            pipe4 
                (attempt (skipString "if" >>. ws >>. expressionParser .>> ws)) 
                (skipChar '{' >>. statementParser .>> skipChar '}' .>> ws)
                (many (elIfParser .>> ws))
                (opt elseParser)
                (fun g m eif el -> 
                    let el = Option.defaultValue Skip el
                    let a = 
                        (eif, el)
                        ||> List.foldBack (fun (g, s) x -> If(g, s, x))
                    If(g, m, a)
                    )

        let skipParser =  
            stringReturn "skip" Skip

        let whileParser =  
            pipe2 
                (skipString "while" >>. ws >>. expressionParser .>> ws)
                (skipChar '{' >>. statementParser .>> skipChar '}')
                (fun g p -> While(g, p))

        let nondetParser =  
            pipe3 
                (attempt (skipString "if" >>. ws >>. skipChar '*' .>> ws))
                (skipChar '{' >>. statementParser .>> skipChar '}' .>> ws .>> skipString "else" .>> ws)
                (skipChar '{' >>. statementParser .>> skipChar '}')
                (fun _ x y -> Nondet(x, y))

        
        let assignParser = 
            variableParser .>> ws 
            >>= (fun v -> 
                    attempt(
                        skipChar '=' >>. ws >>. skipChar '*'
                        |>> (fun _ -> NondetAssign v) 
                    )
                    <|> 
                    attempt(
                        pipe2
                            (skipChar '=' >>. ws >>. functionNameParser .>> ws .>> skipChar '(')
                            (sepBy (expressionParser .>> ws) (skipChar ',' .>> ws) .>> ws .>> skipChar ')')
                            (fun name args -> FunctionCall(v, name, args))
                    )
                    <|>
                    attempt (
                        pipe2 
                            (many1 (skipChar '[' >>. ws >>. expressionParser .>> ws .>> skipChar ']' .>> ws))
                            (skipChar '=' >>. ws >>. expressionParser)
                            (fun args e -> ArrayAssign(v, args, e))
                    )
                    <|> 
                    attempt(
                        skipChar '=' >>. ws >>. expressionParser
                        |>> (fun e -> VarAssign(v, e)) 
                    )
                )

        let parParser =  
            skipChar '{' >>. statementParser .>> skipChar '}'
        

        let basicBlockParser = 
            ws >>. choice 
                [
                    skipParser .>> ws .>> skipChar ';'
                    whileParser
                    assumeParser .>> ws .>> skipChar ';'
                    ifParser
                    nondetParser
                    assignParser .>> ws .>> skipChar ';'
                    parParser
                ] .>> ws

        do 
            statementParserRef.Value <-
                many1 basicBlockParser
                |>> fun l ->
                    l 
                    |> List.reduce (fun x y -> Seq(x, y))

        statementParser

    
    let typeParser = 
        let baseTypeParser = 
            (stringReturn "int" VarType.IntType)
            <|>
            (stringReturn "bool" VarType.BoolType)
            <|>
            (stringReturn "string" VarType.StringType)
            <|> 
            (skipString "bv_" >>. pint32 |>> VarType.BitvectorType)

        (baseTypeParser .>> spaces)
        >>= (fun b -> 
            (
                (skipChar '[' >>. spaces >>. sepBy1 (baseTypeParser .>> spaces) (pchar ',' .>> spaces) .>> spaces .>> skipChar ']')
                |>> (fun x -> VarType.ArrayType(b, x))
            )
            <|>
            (preturn b)
            )

    let typeDeclarationParser = 
        let typeMappingParser = 
            pipe2 
                (typeParser .>> spaces)
                (variableParser .>> ws .>> skipChar ';')
                (fun t x -> (x, t))

        ws >>. many (typeMappingParser .>> ws)
        |>> Map.ofList
        
    let procedureDefinitionParser =
        Util.ParserUtil.pipe6
            typeParser
            (ws >>. functionNameParser .>> ws)
            (skipChar '(' >>. spaces >>. sepBy (typeParser .>>. (spaces >>. variableParser .>> spaces)) (skipChar ',' .>> spaces) .>> spaces .>> skipChar ')' .>> ws)
            (skipChar '{' >>. typeDeclarationParser .>> ws)
            (statementParser .>> ws)
            (skipString "return" >>. ws >>. expressionParser .>> ws .>> skipChar ';' .>> ws .>> skipChar '}')
            (fun returnType name args  typeMapping body returnExpression -> 
                {
                    ProcedureDeclaration.Name = name
                    Arguments = List.map snd args
                    ReturnType = returnType
                    ReturnExpression = returnExpression
                    Body = body
                    TypeMapping = 
                        Util.mergeMaps (args |> List.map (fun (x, y) -> (y, x)) |> Map.ofList) typeMapping 
                }
            )
        
    let programParser = 
        pipe3
            (ws >>. many (attempt(procedureDefinitionParser) .>> ws) .>> ws)
            (ws >>. typeDeclarationParser)
            (ws >>. statementParser)
            (fun pds t b -> 
                {
                    Program.Procedures = pds;
                    Program.Main = b;
                    Program.MainTypeMapping = t;
                })
