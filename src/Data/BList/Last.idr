--------------------
-- Module definition
--------------------

module Data.BList.Last

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
-- LastOf property
------------------

public export
data LastOf : a -> BList a -> Type where
  SnocLast : LastOf x (xs -: x)
  ConsLast : LastOf x (x :- [])
  FarLast : LastOf x xs -> LastOf x (x' :- xs)

export
Uninhabited (LastOf x []) where
  uninhabited _ impossible

export
{eqContra : Not (x = x')} -> Uninhabited (LastOf x (xs -: x')) where
  uninhabited SnocLast = eqContra Refl

export
{lastContra : Not (LastOf x xs)} -> {eqContra : Not (xs = [])} -> Uninhabited (LastOf x (x' :- xs)) where
  uninhabited ConsLast = eqContra Refl
  uninhabited (FarLast lastPrf) = lastContra lastPrf

export
{eqContra : Not (x = x')} -> Uninhabited (LastOf x (x' :- [])) where
  uninhabited ConsLast = eqContra Refl

export
{propContra : Not (Proper xs)} -> Uninhabited (LastOf x xs) where
  uninhabited SnocLast = propContra ProperSnoc
  uninhabited ConsLast = propContra ProperCons
  uninhabited (FarLast lastPrf) = propContra ProperCons


------------------
-- LastOf function
------------------

public export
lastOf : (xs : BList a) -> (0 propPrf : Proper xs) -> (x : a ** LastOf x xs)
lastOf (x :- xs) propPrf = case decProper xs of
  No propContra => (x ** rewrite notProperNil propContra in ConsLast)
  Yes propPrf'' => let (x' ** propPrf') = lastOf xs propPrf'' in (x' ** FarLast propPrf')
lastOf (xs -: x) propPrf = (x ** SnocLast)

-------------------
-- Decidable LastOf
-------------------

public export
decLastOf : DecEq a => (x : a) -> (xs : BList a) -> Dec (LastOf x xs)
decLastOf x [] = No absurd
decLastOf x (x' :- xs) = case decLastOf x xs of
    No lastContra => case decEq xs [] of
      No eqContra => No absurd
      Yes eqPrf => case decEq x x' of
        No eqContra' => rewrite eqPrf in No absurd
        Yes eqPrf' => Yes (rewrite eqPrf in rewrite eqPrf' in ConsLast)
    Yes lastPrf => Yes (FarLast lastPrf)
decLastOf x (xs -: x') = case decEq x x' of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in SnocLast)

----------------
-- Last function
----------------

public export
last : (xs : BList a) -> (0 propPrf : Proper xs) -> a
last (x :- xs) _ = case decProper xs of
  No propContra => x
  Yes propPrf => last xs propPrf
last (xs -: x) _ = x

-----------
-- Theorems
-----------

export
lastOfProper : LastOf x xs -> Proper xs
lastOfProper SnocLast = ProperSnoc
lastOfProper ConsLast = ProperCons
lastOfProper (FarLast _) = ProperCons

export
prfToLastEq : DecEq a => {xs : BList a} -> {0 propPrf : Proper xs} -> LastOf x xs -> last xs propPrf = x
prfToLastEq {xs=x' :- xs'} lastPrf with (decProper xs')
  prfToLastEq {xs=x' :- xs'} lastPrf | No propContra with (notProperNil propContra)
    prfToLastEq {xs=x' :- []} ConsLast | No propContra | Refl = Refl
  prfToLastEq {xs=x' :- xs'} (FarLast lastPrf) | Yes propPrf' = prfToLastEq lastPrf
prfToLastEq {xs=xs' -: x'} SnocLast = Refl

export
lastEqToPrf : {xs : BList a} -> {0 propPrf : Proper xs} -> last xs propPrf = x -> LastOf x xs
lastEqToPrf {xs=x' :- xs'} Refl with (decProper xs')
  lastEqToPrf {xs=x' :- xs'} Refl | No propContra with (notProperNil propContra)
    lastEqToPrf {xs=x' :- []} Refl | No propContra | Refl = ConsLast
  lastEqToPrf {xs=x' :- xs'} Refl | Yes propPrf' = FarLast (lastEqToPrf {propPrf=propPrf'} Refl)
lastEqToPrf {xs=xs' -: x'} Refl = SnocLast

export
snocLast : LastOf x xs -> LastOf x (z :- xs)
snocLast SnocLast = FarLast SnocLast
snocLast ConsLast = FarLast ConsLast
snocLast (FarLast lastPrf) = FarLast (snocLast lastPrf)
