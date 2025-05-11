--------------------
-- Module definition
--------------------

module Data.BList.ElemOf

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Proper

------------------
-- ElemOf property
------------------

data ElemOf : a -> BList a -> Type where
  ElemHereCons : ElemOf x (x :- xs)
  ElemHereSnoc : ElemOf x (xs -: x)
  ElemFarCons : ElemOf x xs -> ElemOf x (y :- xs)
  ElemFarSnoc : ElemOf x xs -> ElemOf x (xs -: y)

Uninhabited (ElemOf x []) where
  uninhabited _ impossible

{eqContra : Not (x = y)} -> {elemContra : Not (ElemOf x ys)} -> Uninhabited (ElemOf x (y :- ys)) where
  uninhabited ElemHereCons = eqContra Refl
  uninhabited (ElemFarCons elemPrf) = elemContra elemPrf

{eqContra : Not (x = y)} -> {elemContra : Not (ElemOf x ys)} -> Uninhabited (ElemOf x (ys -: y)) where
  uninhabited ElemHereSnoc = eqContra Refl
  uninhabited (ElemFarSnoc elemPrf) = elemContra elemPrf

-------------------
-- Decidable ElemOf
-------------------

public export
decElemOf : DecEq a => (x : a) -> (xs : BList a) -> Dec (ElemOf x xs)
decElemOf x [] = No absurd
decElemOf x (y :- ys) = case decEq x y of
  No eqContra => case decElemOf x ys of
    No elemContra => No absurd
    Yes elemPrf => Yes (ElemFarCons elemPrf)
  Yes eqPrf => Yes (rewrite eqPrf in ElemHereCons)
decElemOf x (ys -: y) = case decEq x y of
  No eqContra => case decElemOf x ys of
    No elemContra => No absurd
    Yes elemPrf => Yes (ElemFarSnoc elemPrf)
  Yes eqPrf => Yes (rewrite eqPrf in ElemHereSnoc)
