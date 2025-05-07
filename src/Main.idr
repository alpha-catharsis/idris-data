module Main

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

-- Main
main : IO ()
main = do
  putStrLn (repr dl1)
  putStrLn (show dl1 ++ "\n")
  putStrLn (repr dl2)
  putStrLn (show dl2 ++ "\n")
  putStrLn (repr dl3)
  putStrLn (show dl3 ++ "\n")
  putStrLn (repr dl4)
  putStrLn (show dl4 ++ "\n")
