--------------------
-- Module definition
--------------------

module Data.BList.Proper

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Equiv

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

------------------
-- Proper theorems
------------------

export
EquivProp Proper where
  equivProp ProperCons (EquivC equivPrf) = ProperCons
  equivProp ProperCons (EquivSC equivPrf) = ProperSnoc
  equivProp ProperSnoc (EquivS equivPrf) = ProperSnoc
  equivProp ProperSnoc (EquivCS equivPrf) = ProperCons

export
notProperNil : {xs : BList a} -> Not (Proper xs) -> xs = []
notProperNil {xs=[]} propContra = Refl
notProperNil {xs=x' :- xs'} propContra = void (propContra ProperCons)
notProperNil {xs=xs' -: x'} propContra = void (propContra ProperSnoc)

export
diffProperNotEq : Not (Proper xs) -> Proper xs' -> Not (xs = xs')
diffProperNotEq propContra propPrf Refl = propContra propPrf
