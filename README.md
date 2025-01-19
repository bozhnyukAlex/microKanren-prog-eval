# MicroKanren Program Evaluator written on Haskell
Haskell implementation MicroKanren and simple relational program evaluator

## Program evaluation task with miniKanren
Given the following language:
```
program: function* expr

function: NAME args expr

arg: NAME*

expr: INTEGER | NAME | call | expr BINOP expr | cond

call: NAME expr*

cond: expr expr expr

BINOP: '+' | '-' | '*' | '>=' | '>' | '=' | '<>'

```

An example in possible concrete syntax:

```
fun fact (n) {
  if 1 >= n then 1 else n * fact (n-1) fi
}

fact (5)

```
**Task**: Given a number R and a program F\* E, where E contains free variables x₁, ..., xₖ. Find such values n₁, ..., nₖ that \[|F\* (E)[xᵢ ← nᵢ]|] = R (that is, find such values of the free variables in E, for which the program produces the result R). For example, if the program looks like this:
```
fun fact (n) {
  if 1 >= n then 1 else n * fact (n-1) fi
}

fact (n)

```
Then for **R = 120**, the answer is **n = 5**.

## Run tests for microKanren

```bash
ghci .\src\MicroKanren.hs

ghci> runAllTests
```

## Run program evaluator

```bash
cd .\src\
ghci .\RelationalDSL.hs
ghci> solve [program] [result]
```

### Examples
```bash
ghci> solve factorialProgram 120 -- [5]
ghci> solve factorialProgram 5040 -- [7]

ghci> testFactorial -- [5]
ghci> testFactorial2 -- [7]
```