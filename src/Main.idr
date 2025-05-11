module Main

import Decidable.Equality

import Data.BList


-- Test lists

dl1 : BList Nat
dl1 = []

dl2 : BList Nat
dl2 = 1 :- 2 :- 3 :- 4 :- 5 :- []

dl3 : BList Nat
dl3 = [] -: 1 -: 2 -: 3 -: 4 -: 5

dl4 : BList Nat
dl4 = (1 :- 2 :- ([] -: 3)) -: 4 -: 5

dl5 : BList Nat
dl5 = 1 :- 2 :- 3 :- []

dl6 : BList Nat
dl6 = [] -: 4 -: 5 -: 6

dl7 : BList Nat
dl7 = (2 :- ((4 :- []) -: 3)) -: 1



-- Main
main : IO ()
main = do
  putStrLn (repr dl7)
  putStrLn (show dl7 ++ "\n")
  case decTailOf (((4 :- []) -: 3) -: 1) dl7 of
    No tailContra => putStrLn "NO TAIL"
    Yes tailPrf => putStrLn "TAIL"
