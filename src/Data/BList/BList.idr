--------------------
-- Module definition
--------------------

module Data.BList.BList

-------------------
-- External imports
-------------------

import Decidable.Equality

---------------------
-- Bidirectional list
---------------------

export infixr 7 :-
export infixl 7 -:

public export
data BList : Type -> Type where
  Nil : BList a
  (:-) : a -> BList a -> BList a
  (-:) : BList a -> a -> BList a

----------------
-- Show instance
----------------

showBList : Show a => BList a -> String
showBList [] = ""
showBList (x :- []) = show x
showBList (x :- xs) = show x ++ ", " ++ showBList xs
showBList ([] -: x) = show x
showBList (xs -: x) = showBList xs ++ ", " ++ show x

export
Show a => Show (BList a) where
  show [] = "[" ++ showBList [] {a} ++ "]"
  show (x :- xs) = "[" ++ show x ++ ", " ++ showBList xs ++ "]"
  show (xs -: x) = "[" ++ showBList xs ++ ", " ++ show x ++ "]"

----------------------
-- List representation
----------------------

export
repr : Show a => BList a -> String
repr [] = "[]"
repr (x :- xs) = case xs of
  [] => show x
  (_ :- _) => show x ++ " :- " ++ repr xs
  ([] -: _) => show x ++ " :- " ++ repr xs
  (_ -: _) => show x ++ " :- (" ++ repr xs ++ ")"
repr (xs -: x) = case xs of
  [] => show x
  (_ -: _) => repr xs  ++ " -: " ++ show x
  (_ :- []) => repr xs  ++ " -: " ++ show x
  (_ :- _) => "(" ++ repr xs ++ ") -: " ++ show x

---------------------
-- Decidable Equality
---------------------

Uninhabited (Nil = y :- ys) where
  uninhabited _ impossible

Uninhabited (Nil = ys -: y) where
  uninhabited _ impossible

Uninhabited (x :- xs = Nil) where
  uninhabited _ impossible

{contra : Either (Not (x = y)) (Not (xs = ys))} -> Uninhabited (x :- xs = y :- ys) where
  uninhabited Refl = case contra of
    Left headEqContra => headEqContra Refl
    Right tailEqContra => tailEqContra Refl

Uninhabited (x :- xs = ys -: y) where
  uninhabited _ impossible

Uninhabited (xs -: x = Nil) where
  uninhabited _ impossible

Uninhabited (xs -: x = y :- ys) where
  uninhabited _ impossible

{contra : Either (Not (x = y)) (Not (xs = ys))} -> Uninhabited (xs -: x = ys -: y) where
  uninhabited Refl = case contra of
    Left lastEqContra => lastEqContra Refl
    Right initEqContra => initEqContra Refl

public export
DecEq a => DecEq (BList a) where
  decEq Nil Nil = Yes Refl
  decEq Nil (y :- ys) = No absurd
  decEq Nil (ys -: y) = No absurd
  decEq (x :- xs) Nil = No absurd
  decEq (x :- xs) (y :- ys) = case decEq x y of
    No headEqContra => No absurd
    Yes headEqPrf => case decEq xs ys of
      No tailEqContra => No absurd
      Yes tailEqPrf => Yes (rewrite headEqPrf in rewrite tailEqPrf in Refl)
  decEq (x :- xs) (ys -: y) = No absurd
  decEq (xs -: x) Nil = No absurd
  decEq (xs -: x) (y :- ys) = No absurd
  decEq (xs -: x) (ys -: y) = case decEq x y of
    No lastEqContra => No absurd
    Yes lastEqPrf => case decEq xs ys of
      No initEqContra => No absurd
      Yes initEqPrf => Yes (rewrite lastEqPrf in rewrite initEqPrf in Refl)

----------------------------
-- Cons and snoc injectivity
----------------------------

export
injConsLeft : x :- xs = y :- xs -> x = y
injConsLeft Refl = Refl

export
injConsRight : x :- xs = x :- ys -> xs = ys
injConsRight Refl = Refl

export
injSnocLeft : xs -: x = ys -: x -> xs = ys
injSnocLeft Refl = Refl

export
injSnocRight : xs -: x = xs -: y -> x = y
injSnocRight Refl = Refl
