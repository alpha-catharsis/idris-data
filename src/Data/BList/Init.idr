--------------------
-- Module definition
--------------------

module Data.BList.Init

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Data.BList.Append
import Data.BList.BList
import Data.BList.Equiv
import Data.BList.Proper

------------------
-- InitOf property
------------------

public export
data InitOf : BList a -> BList a -> Type where
  SnocInit : InitOf xs (xs -: x)
  ConsInit : InitOf [] (x :- [])
  FarInit : InitOf ys xs -> InitOf (x' :- ys) (x' :- xs)

export
Uninhabited (InitOf ys []) where
  uninhabited _ impossible

export
{eqContra : Not (ys = xs)} -> Uninhabited (InitOf ys (xs -: x)) where
  uninhabited SnocInit = eqContra Refl

export
{propPrf : Proper xs} -> Uninhabited (InitOf [] (x :- xs)) where
  uninhabited ConsInit impossible

export
{contra : Either (Not (y = x)) (Not (InitOf ys xs))} -> Uninhabited (InitOf (y :- ys) (x :- xs)) where
  uninhabited (FarInit initPrf) = case contra of
    Left eqContra => eqContra Refl
    Right initContra => initContra initPrf

export
Uninhabited (InitOf (ys -: y) (x :- xs)) where
  uninhabited _ impossible

------------------
-- InitOf function
------------------

public export
initOf : (xs : BList a) -> (0 propPrf : Proper xs) -> (ys : BList a ** InitOf ys xs)
initOf (x :- xs) propPrf = case decProper xs of
  No propContra => ([] ** rewrite notProperNil propContra in ConsInit)
  Yes propPrf' => let (xs' ** propPrf'') = initOf xs propPrf' in (x :- xs' ** FarInit propPrf'')
initOf (xs -: x) propPrf = (xs ** SnocInit)

-------------------
-- Decidable InitOf
-------------------

public export
decInitOf : DecEq a => (ys : BList a) -> (xs : BList a) -> Dec (InitOf ys xs)
decInitOf ys [] = No absurd
decInitOf ys (xs -: x) = case decEq ys xs of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in SnocInit)
decInitOf [] (x :- xs) = case decProper xs of
  No propContra => Yes (rewrite notProperNil propContra in ConsInit)
  Yes propPrf => No absurd
decInitOf (y :- ys) (x :- xs) = case decEq y x of
  No eqContra => No absurd
  Yes eqPrf => case decInitOf ys xs of
    No initConta => No absurd
    Yes initPrf => Yes (rewrite eqPrf in FarInit initPrf)
decInitOf (ys -: y) (x :- xs) = No absurd

----------------
-- Init function
----------------

public export
init : (xs : BList a) -> (0 propPrf : Proper xs) -> BList a
init (x :- xs) propPrf = case decProper xs of
  No propContra => []
  Yes propPrf' => x :- init xs propPrf'
init (xs -: x) propPrf = xs

-----------
-- Theorems
-----------

-- export
-- EquivRightRel InitOf where
--   equivRightRel ConsInit (EquivC equivPrf) = ConsInit
--   equivRightRel ConsInit (EquivSC equivPrf) = FarInit ConsInit
--   equivRightRel SnocInit (EquivS equivPrf) = ?c
--   equivRightRel (FarInit initPrf) (EquivS equivPrf) = ?d
--   equivRightRel (FarInit initPrf) (EquivCS equivPrf) = ?e

export
prfToInitEq : DecEq a => {xs : BList a} -> {0 propPrf : Proper xs} -> InitOf ys xs -> init xs propPrf = ys
prfToInitEq {xs=x' :- xs'} initPrf with (decProper xs')
  prfToInitEq {xs=x' :-  xs'} initPrf | No propContra' with (notProperNil propContra')
    prfToInitEq {xs=x' :- []} ConsInit | No propContra' | Refl = Refl
  prfToInitEq {xs=x' :- xs'} (FarInit initPrf) | Yes propPrf' = cong (x' :-) (prfToInitEq initPrf)
prfToInitEq {xs=xs' -: x'} SnocInit = Refl

export
initEqToPrf : {xs : BList a} -> {0 propPrf : Proper xs} -> init xs propPrf = ys -> InitOf ys xs
initEqToPrf {xs=x' :- xs'} Refl with (decProper xs')
  initEqToPrf {xs=x' :- xs'} Refl | No propContra with (notProperNil propContra)
    initEqToPrf {xs=x' :- []} Refl | No propContra | Refl = ConsInit
  initEqToPrf {xs=x' :- xs'} Refl | Yes propPrf' = FarInit (initEqToPrf {propPrf=propPrf'} Refl)
initEqToPrf {xs=xs' -: x'} Refl = SnocInit

export
initOfProper : InitOf x xs -> Proper xs
initOfProper SnocInit = ProperSnoc
initOfProper ConsInit = ProperCons
initOfProper (FarInit _) = ProperCons
