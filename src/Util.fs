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

module Util 

exception ForExException of string
    
/// Compute the Levenshtein distance between two strings
let levenshtein (word1: string) (word2: string) =
    let preprocess = fun (str : string) -> str.ToLower().ToCharArray()
    let chars1, chars2 = preprocess word1, preprocess word2
    let m, n = chars1.Length, chars2.Length
    let table : int[,] = Array2D.zeroCreate (m + 1) (n + 1)
    for i in 0..m do
        for j in 0..n do
            match i, j with
            | i, 0 -> table.[i, j] <- i
            | 0, j -> table.[i, j] <- j
            | _, _ ->
                let delete = table.[i-1, j] + 1
                let insert = table.[i, j-1] + 1
                //cost of substitution is 2
                let substitute = 
                    if chars1.[i - 1] = chars2.[j - 1] 
                        then table.[i-1, j-1] //same character
                        else table.[i-1, j-1] + 2
                table.[i, j] <- List.min [delete; insert; substitute]
    table.[m, n]
    

/// Compute the cartesian product of a list of sequences
let rec cartesianProduct (LL: list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }


/// Compute the powerset of a given set of a fixed size
let powersetOfFixedSize (size : int) (s : Set<'a>)  =
    let asList = Set.toList s 

    let rec computeFiniteChoices size (A : list<'a>) =
        if size = 0 then 
            Seq.singleton Set.empty
        else 
            match A with 
            | [] -> Seq.empty
            | x::xs -> 
                // Either x is included or it is not ]
                let alt1 =
                    computeFiniteChoices (size - 1) xs 
                    |> Seq.map (fun y -> Set.add x y)

                let alt2 = computeFiniteChoices size xs 

                Seq.append alt1 alt2

    computeFiniteChoices size asList


/// Merge two maps, asserts that all shared keys are mapped to the same value
let mergeMaps (map1: Map<'K,'V>) (map2: Map<'K,'V>) = 
    (map1, Map.toSeq map2)
    ||> Seq.fold (fun s (k, v) -> 
        if Map.containsKey k s then 
            if s.[k] = v then 
                s
            else 
                raise <| System.ArgumentException()
        else 
            Map.add k v s
        )

let mergeMapsMany maps = 
    (Map.empty, maps)
    ||> Seq.fold (fun s x -> mergeMaps s x)


/// Replaces the item at a given index in a list
let rec replaceAt index (value : 'T) (source : list<'T>) = 
    match source, index with 
    | _::xs, 0 -> value :: xs 
    | x::xs, index -> x:: replaceAt (index - 1) value xs
    | _ -> raise <| System.ArgumentException()



/// Given a map A -> B seq compute all possible maps A -> B that are obtained by picking some element from that set for each key in A
/// The result is ordered by the given order on B (lexicographically with some order on A). 
let cartesianProductMapOrdered (ord : 'B -> 'B -> int) (m : Map<'A, seq<'B>>) =
    let rec lexOrder (comp) (list1) (list2) = 
        match list1, list2 with 
        | [], [] -> 0 
        | _::_, [] -> -1 
        | [], _::_ -> 1
        | x::xs, y::ys  -> 
            match comp x y with 
            | 0 -> 
                lexOrder comp xs ys 
            | r -> r

    let keys = Map.keys m |> Seq.toList

    let valueCombinations = 
        keys 
        |> List.map (fun k -> m.[k])
        |> cartesianProduct
        // Now order all options based on the order on B
        |> Seq.sortWith (lexOrder ord)

    // Now add the keys again and convert to a map
    valueCombinations
    |> Seq.map (fun values -> 
        List.zip keys values 
        |> Map.ofList
        )


module SubprocessUtil = 
    type SubprocessResult = 
        {
            Stdout : string 
            Stderr : string 
            ExitCode : int
        }

    let executeSubprocess (cmd: string) (arg: string) = 
        let psi =
            System.Diagnostics.ProcessStartInfo(cmd, arg)

        psi.UseShellExecute <- false
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.CreateNoWindow <- true
        let p = System.Diagnostics.Process.Start(psi)
        let output = System.Text.StringBuilder()
        let error = System.Text.StringBuilder()
        p.OutputDataReceived.Add(fun args -> output.Append(args.Data) |> ignore)
        p.ErrorDataReceived.Add(fun args -> error.Append(args.Data) |> ignore)
        p.BeginErrorReadLine()
        p.BeginOutputReadLine()
        p.WaitForExit()

        {
            SubprocessResult.Stdout = output.ToString();
            Stderr = error.ToString()
            ExitCode = p.ExitCode
        }

module ParserUtil = 
    open FParsec

    let programVariableParser : Parser<string, unit> = 
        pipe2 
            (letter)
            (many (letter <|> digit <|> pchar '.'))
            (fun x y -> x::y |> List.toArray |> System.String)

    let pipe6 a b c d e f fu = 
        pipe5
            (a .>>. b)
            c 
            d 
            e 
            f 
            (fun (a, b) c d e f -> fu a b c d e f)
