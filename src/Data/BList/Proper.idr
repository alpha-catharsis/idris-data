--------------------
-- Module definition
--------------------

module Data.BList.Proper

-------------------
-- Internal imports
-------------------

import Data.BList.BList

------------------
-- Proper property
------------------

public export
data Proper : BList a -> Type where
  ProperCons : Proper (x :- xs)
  ProperSnoc : Proper (xs -: x)

Uninhabited (Proper []) where
  uninhabited _ impossible

public export
decProper : (xs : BList a) -> Dec (Proper xs)
decProper [] = No absurd
decProper (x :- xs) = Yes ProperCons
decProper (xs -: x) = Yes ProperSnoc
