module Main

import Decidable.Equality

import Data.AList
import Data.BList


-- Test bidirectional lists

bl1 : BList Nat
bl1 = []

bl2 : BList Nat
bl2 = 1 :- 2 :- 3 :- 4 :- 5 :- []

bl3 : BList Nat
bl3 = [] -: 1 -: 2 -: 3 -: 4 -: 5

bl4 : BList Nat
bl4 = (1 :- 2 :- ([] -: 3)) -: 4 -: 5

bl5 : BList Nat
bl5 = 1 :- 2 :- 3 :- []

bl6 : BList Nat
bl6 = [] -: 4 -: 5 -: 6

bl7 : BList Nat
bl7 = (2 :- ((4 :- []) -: 3)) -: 1

-- Test append lists

al1 : AList Nat
al1 = N 0

al2 : AList Nat
al2 = N 1 ++ (N 2 ++ (N 3 ++ (N 4 ++ N 5)))

al3 : AList Nat
al3 = (((N 1 ++ N 2) ++ N 3) ++ N 4) ++ N 5

-- Main
main : IO ()
main = do
  putStrLn (repr al1)
  putStrLn (show al1)
  putStr "\n"
  putStrLn (repr al2)
  putStrLn (show al2)
  putStr "\n"
  putStrLn (repr al3)
  putStrLn (show al3)
