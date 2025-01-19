{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant lambda" #-}
{-# HLINT ignore "Use camelCase" #-}

module MicroKanren where

import Control.Monad (guard)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

newtype Var = Var Int deriving (Eq, Show)

type Substitution = [(Var, Term)]

data Stream a
  = Empty
  | Cons a (Stream a)
  | Susp (() -> Stream a)

type Goal = State -> Stream State

type State = (Substitution, Int)

data Term
  = TmVar Var
  | TmInt Int
  | TmBool Bool
  | TmPair Term Term
  | TmNil
  | TmSymbol String
  deriving (Eq, Show)

extS :: Var -> Term -> Substitution -> Substitution
extS x v s = (x, v) : s

(===) :: Term -> Term -> Goal
u === v = \(s, c) ->
  case unify u v s of
    Just s' -> unit (s', c)
    Nothing -> mzero

unit :: a -> Stream a
unit x = Cons x Empty

mzero :: Stream a
mzero = Empty

failure :: Goal
failure = \_ -> mzero

walk :: Term -> Substitution -> Term
walk u s = case u of
  TmVar v -> fromMaybe u (lookup v s >>= \t -> Just $ walk t s)
  _ -> u

unify :: Term -> Term -> Substitution -> Maybe Substitution
unify u v s =
  let u' = walk u s
      v' = walk v s
   in case (u', v') of
        (TmVar x, _) -> Just $ extS x v' s
        (_, TmVar y) -> Just $ extS y u' s
        (TmPair a b, TmPair c d) ->
          unify a c s >>= unify b d
        (TmInt a, TmInt b) | a == b -> Just s
        (TmBool a, TmBool b) | a == b -> Just s
        (TmSymbol a, TmSymbol b) | a == b -> Just s
        (TmNil, TmNil) -> Just s
        _ -> Nothing

callFresh :: (Term -> Goal) -> Goal
callFresh f = \(s, c) ->
  let x = TmVar (Var c)
   in f x (s, c + 1)

disj :: Goal -> Goal -> Goal
disj g1 g2 = \s -> mplus (g1 s) (g2 s)

conj :: Goal -> Goal -> Goal
conj g1 g2 = \s -> bind (g1 s) g2

mplus :: Stream a -> Stream a -> Stream a
mplus Empty ys = ys
mplus (Susp s) ys = Susp (\() -> mplus ys (s ()))
mplus (Cons x xs) ys = Cons x (mplus xs ys)

delay :: Goal -> Goal
delay g = \s -> Susp (\_ -> g s)

list :: [Term] -> Term
list [] = TmNil
list (x : xs) = TmPair x (list xs)

bind :: Stream a -> (a -> Stream b) -> Stream b
bind Empty _ = Empty
bind (Susp s) f = Susp (\() -> bind (s ()) f)
bind (Cons x xs) f = mplus (f x) (bind xs f)

takeStream :: Int -> Stream a -> [a]
takeStream _ Empty = []
takeStream n _ | n <= 0 = []
takeStream n (Cons x xs) = x : takeStream (n - 1) xs
takeStream n (Susp s) = takeStream n (s ())

run :: Goal -> Stream State
run g = g ([], 0)

---------- TESTS

aAndB :: Goal
aAndB =
  conj
    (callFresh (\a -> a === TmInt 7))
    (callFresh (\b -> disj (b === TmInt 5) (b === TmInt 6)))

fives :: Term -> Goal
fives x =
  disj
    (x === TmInt 5)
    (delay (fives x))

appendo :: Term -> Term -> Term -> Goal
appendo l s out =
  disj
    (conj (l === TmNil) (s === out))
    ( callFresh
        ( \a ->
            callFresh
              ( \d ->
                  conj
                    (l === TmPair a d)
                    ( callFresh
                        ( \res ->
                            conj
                              (out === TmPair a res)
                              (delay (appendo d s res))
                        )
                    )
              )
        )
    )

appendo2 :: Term -> Term -> Term -> Goal
appendo2 l s out =
  disj
    (conj (l === TmNil) (s === out))
    ( callFresh
        ( \a ->
            callFresh
              ( \d ->
                  conj
                    (l === TmPair a d)
                    ( callFresh
                        ( \res ->
                            conj
                              (delay (appendo2 d s res))
                              (out === TmPair a res)
                        )
                    )
              )
        )
    )

callAppendo :: Goal
callAppendo =
  callFresh
    ( \q ->
        callFresh
          ( \l ->
              callFresh
                ( \s ->
                    callFresh
                      ( \out ->
                          conj
                            (appendo l s out)
                            (q === list [l, s, out])
                      )
                )
          )
    )

callAppendo2 :: Goal
callAppendo2 =
  callFresh
    ( \q ->
        callFresh
          ( \l ->
              callFresh
                ( \s ->
                    callFresh
                      ( \out ->
                          conj
                            (appendo2 l s out)
                            (q === list [l, s, out])
                      )
                )
          )
    )

callAppendo3 :: Goal
callAppendo3 =
  callFresh
    ( \q ->
        callFresh
          ( \l ->
              callFresh
                ( \s ->
                    callFresh
                      ( \out ->
                          conj
                            (q === list [l, s, out])
                            (appendo l s out)
                      )
                )
          )
    )

groundAppendo :: Goal
groundAppendo =
  appendo
    (list [TmSymbol "a"])
    (list [TmSymbol "b"])
    (list [TmSymbol "a", TmSymbol "b"])

groundAppendo2 :: Goal
groundAppendo2 =
  appendo2
    (list [TmSymbol "a"])
    (list [TmSymbol "b"])
    (list [TmSymbol "a", TmSymbol "b"])

relo :: Term -> Goal
relo x =
  callFresh
    ( \x1 ->
        callFresh
          ( \x2 ->
              conj
                (x === TmPair x1 x2)
                ( disj
                    (x1 === x2)
                    (delay (relo x))
                )
          )
    )

manyNonAns :: Goal
manyNonAns =
  callFresh
    ( \x ->
        disj
          (relo (TmPair (TmInt 5) (TmInt 6)))
          (x === TmInt 3)
    )

showTerm :: Term -> String
showTerm t = case t of
  TmVar (Var n) -> "v" ++ show n
  TmInt i -> show i
  TmBool b -> show b
  TmPair a b -> "(" ++ showTerm a ++ " . " ++ showTerm b ++ ")"
  TmNil -> "()"
  TmSymbol s -> s

showSubst :: Substitution -> String
showSubst s = "{" ++ concatMap showPair s ++ "}"
  where
    showPair (Var n, t) = "v" ++ show n ++ " = " ++ showTerm t ++ "; "

testGoal :: Int -> Goal -> IO ()
testGoal times goal = do
  let results = takeStream times (run goal)
  case results of
    [] -> putStrLn "No results."
    _ -> mapM_ (print . showSubst . fst) results
  putStrLn ""

runAllTests :: IO ()
runAllTests = do
  let tTimes = 3
  testGoal tTimes aAndB
  testGoal tTimes (callFresh fives)
  testGoal tTimes callAppendo
  testGoal tTimes callAppendo2
  testGoal tTimes callAppendo3
  testGoal tTimes groundAppendo
  testGoal tTimes groundAppendo2
  testGoal tTimes manyNonAns