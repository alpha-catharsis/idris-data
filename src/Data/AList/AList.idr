--------------------
-- Module definition
--------------------

module Data.AList.AList

-------------------
-- External imports
-------------------

import Decidable.Equality

--------------
-- Append list
--------------

export infixr 7 ++

public export
data AList : Type -> Type where
  N : a -> AList a
  (++) : AList a -> AList a -> AList a

----------------
-- Show instance
----------------

showAList : Show a => AList a -> String
showAList (N x) = show x
showAList (xs ++ ys) = showAList xs ++ ", " ++ showAList ys

export
Show a => Show (AList a) where
  show xs = "[" ++ showAList xs ++ "]"

----------------------
-- List representation
----------------------

export
repr : Show a => AList a -> String
repr (N x) = show x
repr (xs ++ ys) = "(" ++ repr xs ++ " ++ " ++ repr ys ++ ")"

---------------------
-- Decidable Equality
---------------------

{eqContra : Not (x = y)} -> Uninhabited (N x = N y) where
  uninhabited Refl = eqContra Refl

Uninhabited (N x = ys ++ ys') where
  uninhabited _ impossible

Uninhabited (xs ++ xs' = N y) where
  uninhabited _ impossible

{0 xs, xs', ys, ys' : AList a} -> {contra : Either (Not (xs = ys)) (Not (xs' = ys'))} -> Uninhabited (xs ++ xs' = ys ++ ys') where
  uninhabited Refl = case contra of
    Left leftEqContra => leftEqContra Refl
    Right rightEqContra => rightEqContra Refl

public export
DecEq a => DecEq (AList a) where
  decEq (N x) (N y) = case decEq x y of
    No eqContra => No absurd
    Yes eqPrf => Yes (rewrite eqPrf in Refl)
  decEq (N x) (ys ++ ys') = No absurd
  decEq (xs ++ xs') (N y) = No absurd
  decEq (xs ++ xs') (ys ++ ys') = case decEq xs ys of
    No leftEqContra => No absurd
    Yes leftEqPrf => case decEq xs' ys' of
      No rightEqContra => No absurd
      Yes rightEqPrf => rewrite leftEqPrf in rewrite rightEqPrf in Yes Refl

-----------
-- Theorems
-----------

export
injNode : S x = S y -> x = y
injNode Refl = Refl

export
injLeftAppend : {0 xs, xs', ys, ys' : AList a} -> xs ++ xs' = ys ++ ys' -> xs = ys
injLeftAppend Refl = Refl

export
injRightAppend : {0 xs, xs', ys, ys' : AList a} -> xs ++ xs' = ys ++ ys' -> xs' = ys'
injRightAppend Refl = Refl
