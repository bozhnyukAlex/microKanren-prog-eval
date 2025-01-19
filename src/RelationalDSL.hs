{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant lambda" #-}

module RelationalDSL where

import Control.Monad (guard)
import Data.List (nub)
import Data.Maybe (fromMaybe)
import MicroKanren

data Program = Program [Function] Expr

data Function = Function String [String] Expr

data Expr
  = EInt Int
  | EVar String
  | ECall String [Expr]
  | EBinOp String Expr Expr
  | ECond Expr Expr Expr
  deriving (Eq, Show)

type Env = [(String, Term)]

type FunEnv = [(String, Function)]

addo :: Term -> Term -> Term -> Goal
addo x y z = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
      z' = walk z s
   in case (x', y', z') of
        (TmInt a, TmInt b, _) -> (z === TmInt (a + b)) state
        (TmInt a, _, TmInt c) -> (y === TmInt (c - a)) state
        (_, TmInt b, TmInt c) -> (x === TmInt (c - b)) state
        (_, _, _) -> mzero

subo :: Term -> Term -> Term -> Goal
subo x y z = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
      z' = walk z s
   in case (x', y', z') of
        (TmInt a, TmInt b, _) -> (z === TmInt (a - b)) state
        (TmInt a, _, TmInt c) -> (y === TmInt (a - c)) state
        (_, TmInt b, TmInt c) -> (x === TmInt (b + c)) state
        (_, _, _) -> mzero

mulo :: Term -> Term -> Term -> Goal
mulo x y z = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
      z' = walk z s
   in case (x', y', z') of
        (TmInt a, TmInt b, _) -> (z === TmInt (a * b)) state
        (TmInt a, _, TmInt c) ->
          if a /= 0
            then (y === TmInt (c `div` a)) `conj` checkDiv (TmInt c) (TmInt a) $ state
            else mzero
        (_, TmInt b, TmInt c) ->
          if b /= 0
            then (x === TmInt (c `div` b)) `conj` checkDiv (TmInt c) (TmInt b) $ state
            else mzero
        (_, _, _) -> mzero
  where
    checkDiv :: Term -> Term -> Goal
    checkDiv c d = \s ->
      let c' = walk c (fst s)
          d' = walk d (fst s)
       in case (c', d') of
            (TmInt cval, TmInt dval) ->
              if cval `mod` dval == 0 then unit s else mzero
            _ -> mzero

eqo :: Term -> Term -> Goal
eqo x y = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
   in case (x', y') of
        (TmInt a, TmInt b) ->
          if a == b then unit state else mzero
        _ -> mzero

neqo :: Term -> Term -> Goal
neqo x y = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
   in case (x', y') of
        (TmInt a, TmInt b) ->
          if a /= b then unit state else mzero
        _ ->
          mzero

gto :: Term -> Term -> Goal
gto x y = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
   in case (x', y') of
        (TmInt a, TmInt b) ->
          if a > b then unit state else mzero
        _ -> mzero

geqo :: Term -> Term -> Goal
geqo x y = \state ->
  let s = fst state
      x' = walk x s
      y' = walk y s
   in case (x', y') of
        (TmInt a, TmInt b) ->
          if a >= b then unit state else mzero
        _ ->
          mzero

opGoal :: String -> Term -> Term -> Term -> Goal
opGoal "+" t1 t2 res = addo t1 t2 res
opGoal "-" t1 t2 res = subo t1 t2 res
opGoal "*" t1 t2 res = mulo t1 t2 res
opGoal ">=" t1 t2 res = geqo t1 t2 `conj` (res === TmBool True)
opGoal ">" t1 t2 res = gto t1 t2 `conj` (res === TmBool True)
opGoal "=" t1 t2 res = eqo t1 t2 `conj` (res === TmBool True)
opGoal "<>" t1 t2 res = neqo t1 t2 `conj` (res === TmBool True)
opGoal _ _ _ _ = failure

evalExpr :: Env -> FunEnv -> Expr -> Term -> Goal
evalExpr env funEnv expr res =
  case expr of
    EInt n ->
      res === TmInt n
    EVar x -> case lookup x env of
      Just v ->
        res === v
      Nothing ->
        failure
    EBinOp op e1 e2 ->
      callFresh $ \t1 ->
        callFresh $ \t2 ->
          evalExpr env funEnv e1 t1
            `conj` evalExpr env funEnv e2 t2
            `conj` callFresh (\r -> opGoal op t1 t2 r `conj` (res === r))
    ECall f es ->
      case lookup f funEnv of
        Just (Function _ argNames body) ->
          if length argNames == length es
            then callFreshN (length argNames) $ \args ->
              let argPairs = zip argNames args
                  env' = argPairs ++ env
                  argGoals = zipWith (evalExpr env funEnv) es args
                  bodyGoal = evalExpr env' funEnv body res
               in foldr conj bodyGoal argGoals
            else failure
        Nothing -> failure
    ECond e1 e2 e3 ->
      callFresh $ \c ->
        evalExpr env funEnv e1 c
          `conj` ((c === TmBool True) `conj` evalExpr env funEnv e2 res)
          `disj` ((c === TmBool False) `conj` evalExpr env funEnv e3 res)

callFreshN :: Int -> ([Term] -> Goal) -> Goal
callFreshN n f = go n []
  where
    go 0 vars = f (reverse vars)
    go m vars = callFresh $ \x -> go (m - 1) (x : vars)

freeVars :: Expr -> [String]
freeVars expr = nub (go expr)
  where
    go (EInt _) = []
    go (EVar x) = [x]
    go (EBinOp _ e1 e2) = go e1 ++ go e2
    go (ECall _ es) = concatMap go es
    go (ECond e1 e2 e3) = go e1 ++ go e2 ++ go e3

evalProgram :: Program -> Term -> Int -> Int -> Goal
evalProgram (Program funcs expr) res l h =
  let funEnv = [(name, func) | func@(Function name _ _) <- funcs]
      vars = freeVars expr
   in callFreshN (length vars) $ \vs ->
        let env = zip vars vs
         in inDomains l h vs `conj` evalExpr env funEnv expr res

factFunc :: Function
factFunc = Function "fact" ["n"] body
  where
    body =
      ECond
        (EBinOp ">=" (EVar "n") (EInt 1))
        ( EBinOp
            "*"
            (EVar "n")
            (ECall "fact" [EBinOp "-" (EVar "n") (EInt 1)])
        )
        (EInt 1)

factorialProgram :: Program
factorialProgram = Program [factFunc] (ECall "fact" [EVar "n"])

inDomain :: Int -> Int -> Term -> Goal
inDomain low high var = foldr disj failure [var === TmInt n | n <- [low .. high]]

inDomains :: Int -> Int -> [Term] -> Goal
inDomains low high = foldr (conj . inDomain low high) unit

extractNs :: [Int] -> [Substitution] -> [Int]
extractNs idxs subs =
  [ n
    | s <- subs,
      (v, TmInt n) <- s,
      Var idx <- [v],
      idx `elem` idxs
  ]

generateSeq :: Int -> Int -> [Int]
generateSeq n x = [x .. x + n - 1]

solveInDomain :: Program -> Int -> Int -> Int -> [Int]
solveInDomain program@(Program _ mainExpr) r low high =
  let freeVs = freeVars mainExpr
      solveGoal = callFresh $ \result ->
        evalProgram program result low high `conj` (result === TmInt r)
      idxs = generateSeq (length freeVs) 1
   in extractNs idxs $ map fst $ takeStream 1 $ run solveGoal

solve :: Program -> Int -> [Int]
solve program result = solveInDomain program result 1 2432902008176640000

----- TESTS

factorial :: Int -> Int
factorial 0 = 1
factorial n
  | n > 0 = n * factorial (n - 1)
  | otherwise = error "Bad argument"

testFactorial1 = solve factorialProgram (factorial 5)

testFactorial2 = solve factorialProgram (factorial 20)