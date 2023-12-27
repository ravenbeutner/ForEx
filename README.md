# ForEx: Automated Software Verification of Hyperliveness

This repository contains **ForEx** (short for "**For**all **Ex**ist Verification" ), a tool that can verify hyperliveness properties in (infinite-state) software programs.

## Overview

ForEx is a tool for the software verification of _hyperproperties_, i.e., properties that relate multiple executions of a program. 
Concretely, ForEx targets the verification of `\forall\exists` hyperproperties, i.e., properties that mix universal and existential quantification over executions, and can thus handle properties beyond k-safety (i.e., properties that universally qunatify over `k` executions).
ForEx reads a list of (possibly identical) programs in a C-like language and relational pre-and post-conditions.
The pre-and post-condition specifies a `\forall\exists` hyperproperty in the form of a _Forall-Exists Hoare tuple_.
More details are given in the corresponding paper:

> Automated Software Verification of Hyperliveness. Raven Beutner. TACAS 2024. [1]


## Structure 

This repository is structured as follows:

- `src/` contains the source code of ForEx (written in F#)
- `benchmarks/` contains various verification instances used to evaluate ForEx [1] 
- `app/` is the target folder for the build. The final ForEx executable will be placed here

## Build ForEx

### Dependencies

To build and run ForEx we require the following dependencies:

- [.NET 8 SDK](https://dotnet.microsoft.com/en-us/download) (tested with version 8.0.100)
- [Z3](https://github.com/Z3Prover/z3) (tested with version 4.11.2)

Install the .NET 8 SDK (see [here](https://dotnet.microsoft.com/en-us/download) for details) and make sure it is installed correctly by running `dotnet --version`.
Clone and build the Z3 SMT solver (details can be found [here](https://github.com/Z3Prover/z3)).
You can place the Z3 executables in any location of your choosing; HyPro will need the *absolute* path to Z3 executable (see details below).
Alternatively, you can download a pre-build Z3 binary for your architecture (see [here](https://github.com/Z3Prover/z3/releases)).

### Build ForEx

To build ForEx run the following (when in the main directory of this repository).

```shell
cd src
dotnet build -c "release" -o ../app
cd ..
```

Afterward, the ForEx executable is located in the `app/` folder.
Test that everything works as expected by running 

```shell
app/ForEx --version
```

### Connect Z3 to HyPro

HyPro requires the Z3 solver to discharge SMT queries.
HyPro is designed such that it only needs the *absolute* path to Z3, so Z3 can be installed and placed at whatever locations fits best.
The absolute path is specified in a `paths.json` configuration file. 
This file must be located in the same directory as the HyPro executable. 
We already provide a template file `app/paths.json` that **needs to be modified**. 
After having built Z3, paste the absolute path to the *Z3* executables to the `paths.json` file. 
For example, if `/usr/bin/z3` is the _Z3_ executable, the content of `app/paths.json` should be

```json
{
    "z3":"/usr/bin/z3"
}
```


### A First Example

To test that ForEx can access the Z3 binary, run the following

```shell
app/ForEx benchmarks/hypa/asynch_gni.txt
```

which should return `SAT`.


## Run ForEx

To invoke ForEx, run

```
app/ForEx <input-instance>
```

where `<input-instance>` is a (path to) the verification instance. 
The programs to be verified, the specification, and (optional) parameters are all configured in this input file. 


### Input File 

A typical input file has the following structure 

```
[forall]
<program>

...

[forall]
<program>

[exists]
<program>

...

[exists]
<program>

[pre]
<formula>

[post]
<formula>
```

where each `<program>` is a C-like program, and each `<formula>` is a relational formula over the states of all programs. 
All programs preceded by `[forall]` are quantified universally, and all `[exists]` programs are quantified existentially.
The verification instance asks if, for all states of the programs that, together, satisfy the relational `[pre]` formula, and for all executions of universally quantified programs, there exist executions of the existentially quantified programs such that the final states of all executions, together, satisfy the `[post]` formula. 
For more details see the definition of FEHTs in [1]. 

In the following, we formally define `<program>` and `<formula>`.

### Specifying Programs

Programs are written in a simple C-like imperative language. 

**Variables:**
A variable `<VAR>` is any non-reserved string consisting of letters and digits (starting with a letter).

**Types:**
Each variable has a type `<varType>` which can be one of the following:
- `int`: A mathematical integer value
- `bool`: a boolean, 
- `string`: a string 
- `bv_<n>`: a _fixed-size_ bitvector of positive length `<n>`


**Expressions:**
An expression `<expression>` is formed by the following grammar

- `<VAR>`
- `"<string>"` denotes a string constant, where `<string>` is any sequence of characters not containing `"`. For example, `"hallo"`.
- `<n>`, denotes an integer constant, where `<n>` in an arbitrary integer.
- `true` or `false`, denote the boolean constants.
- `#b<bit>...<bit>`, denotes a bitvector constant, where each `<bit>` is either `0` or `1`. This denotes a bitvector constant. For example, `#b1001` denotes the bitvector `1001` of length 4. 
- `<expression> <bopp> <expression>`, denotes the application of a binary operator `<bopp>`. Supported binary operators include `+`, `-`, `*`, `==`, `!=`, `>=`, `<=`, `>`, `<`, `&&`, `||`, `str.++` (concatenation of strings), `bv.&` (pointwise conjunction on bitvectors), and `bv.|` (pointwise disjunction on bitvectors). 
- `<uopp> <expression>`, denotes the application of a unary operator `<uopp>`. Supported binary operators include `!`, `-`, `str.len` (returns the length of a string), and `bv.!` (pointwise negation on bitvectors).
- `<expression>{<l>, <u>}`, is a special operation applicable only to bitvectors that extracts a subsequence of the vector given by the indices `<l>`  and `<u>`. For example `(#b1010){0, 1}` takes the bitvector `#b1010` of length 4 and extracts the first two bits, i.e., it evaluates to the bitvector `#b10` of length 2. 


**Statements:**
A `<statement>` is formed using the following constructs: 

- `skip;`, denotes the skip statement that does nothing 
- `<VAR> = <expression>;`, assigns the variable the value obtained when evaluating the expression in the current state. 
- `<VAR> = *;`, assigns the variable a non-deterministically chosen value
- `if (<expression>) { <statementList> } else {<statementList>}`, branches on whether or not the expression evaluates to `true`
- `if * { <statementList> } else {<statementList>}`, non-deterministically executed one of the two branches
- `while (<expression>) { <statementList> }`, executes the statement as long as the expression evaluates to `true`

Here, we write `<statementList>` for a non-empty sequence of `<statement>`s.


**Programs:**
Finally, a `<program>` is formed by declaring the type of each variable, followed by a list of statements. 

```
<varType> <VAR>;
...
<varType> <VAR>;

<statementList>
```

Importantly, all variables used in the program must be declared (and typed). 
ForEx checks that the program is well-formed, including, e.g., that all used variables are declared, operators are only applied to arguments of the correct type, etc. 

As an example program consider the following:

```
int o;
int x;

o = 0;
while (x > 0) {
    if * {
        o = o + 1;
    } else {
        skip;
    }

    x = x - 1;
}
```

### Specifying Pre-and Postcondition

The pre-and post-condition is given as a relational formula, i.e., a formula that can refer to variables in multiple programs. 
A `<formula>` is formed similar to an `<expression>` but indexes all variables:

- `<VAR>_<n>`, where `<VAR>` is a program variable and `<n>` is an index that refers to a program. For example, `x_0` refers to variable `x` in the first (0th) program. The index must be between 0 (inclusive) and the total number of programs given in the input instance (exclusive).
- `"<string>"` denotes a string constant, where `<string>` is any sequence of characters not containing `"`.
- `<n>`, denotes an integer constant, where `<n>` in an arbitrary integer.
- `true` or `false`, denote the boolean constants.
- `#b<bit>...<bit>`, denotes a bitvector constant, where each `<bit>` is either `0` or `1`. This denotes a bitvector constant. 
- `<formula> <bopp> <formula>`, denotes the application of a binary operator `<bopp>`. Supported binary operators include `+`, `-`, `*`, `==`, `!=`, `>=`, `<=`, `>`, `<`, `&&`, `||`, `=>` (implication), `str.++` (concatenation of strings), `bv.&` (pointwise conjunction on bitvectors), and `bv.|` (pointwise disjunction on bitvectors). 
- `<uopp> <formula>`, denotes the application of a unary operator `<uopp>`. Supported binary operators include `!`, `-`, `str.len` (returns the length of a string), and `bv.!` (pointwise negation on bitvectors).

Note that pre-and post-condition must be of type `bool`.



### Example Input

A possible input instance is the following: 

```
[forall]
int o;
int x;

o = 0;
while (x > 0) {
    x = x - 1;
    if * {
        o = o + 1;
    } else {
        skip;
    }
}

[exists]
int o;
int x;
int s;

o = 0;
while (x > 0) {
    x = x - 1;
    s = *;
    o = o + s;
}

[pre]
x_0 == x_1

[post]
o_0 == o_1
```

More verification instances (including those used in [1]) are located in the `benchmarks/` folder.


### Additional Parameters

Each input instance **must** specify a pre-and postcondition and at least one program. 
In addition, the user can include additional parameters to guide the verification of ForEx.  

**Number Of Conjuncts:**
ForEx attempts to infer suitable loop invariants, by forming conjunctions of expressions found in the pre-and postcondition and equalities between loop guards.  
By adding 
```
[maxC]
<n>
```
or 
```
[minC]
<n>
```
for some natural number `<n>`, ForEx bounds the maximal (resp. minimal) number of conjuncts in each invariant guess. 

**Invariant Hints:**
We can give hints to ForEx by suggesting conjuncts that might prove useful. 
By adding 
```
[inv]
<formula>
```
ForEx prioritizes invariants that include the provided hint(s).


**Asynchronous Loop Alignment:**
ForEx can search for asynchronous loop alignments, by offsetting the execution of each loop (see [1]). 
By adding 
```
[asynchronous]
<n>
```
ForEx searches for asynchronous alignments with offset at most `<n>`.


## References  

[1] Automated Software Verification of Hyperliveness. Raven Beutner. TACAS 2024
