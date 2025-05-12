--------------------
-- Module definition
--------------------

module Data.AList.NAList

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Data.AList.AList

-----------------------
-- Nullable append list
-----------------------

public export
data NAList : Type -> Type where
  Empty : NAList a
  Proper : AList a -> NAList a

----------------
-- Show instance
----------------

export
Show a => Show (NAList a) where
  show Empty = "[]"
  show (Proper xs) = show xs

----------------------
-- List representation
----------------------

export
repr : Show a => NAList a -> String
repr Empty = "()"
repr (Proper xs) = repr xs

---------------------
-- Decidable Equality
---------------------

Uninhabited (Empty = Proper ys) where
  uninhabited _ impossible

Uninhabited (Proper xs = Empty) where
  uninhabited _ impossible

{eqContra : Not (xs = ys)} -> Uninhabited (Proper xs = Proper ys) where
  uninhabited Refl = eqContra Refl

public export
DecEq a => DecEq (NAList a) where
  decEq Empty Empty = Yes Refl
  decEq Empty (Proper ys) = No absurd
  decEq (Proper xs) Empty = No absurd
  decEq (Proper xs) (Proper ys) = case decEq xs ys of
    No eqContra => No absurd
    Yes eqPrf => Yes (rewrite eqPrf in Refl)

-----------
-- Theorems
-----------

export
injProper : Proper xs = Proper ys -> xs = ys
injProper Refl = Refl
