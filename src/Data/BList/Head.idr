--------------------
-- Module definition
--------------------

module Data.BList.Head

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
-- HeadOf property
------------------

public export
data HeadOf : a -> BList a -> Type where
  ConsHead : HeadOf x (x :- xs)
  SnocHead : HeadOf x ([] -: x)
  FarHead : HeadOf x xs -> HeadOf x (xs -: x')

export
Uninhabited (HeadOf x []) where
  uninhabited _ impossible

export
{eqContra : Not (x = x')} -> Uninhabited (HeadOf x (x' :- xs)) where
  uninhabited ConsHead = eqContra Refl

export
{headContra : Not (HeadOf x xs)} -> {eqContra : Not (xs = [])} -> Uninhabited (HeadOf x (xs -: x')) where
  uninhabited SnocHead = eqContra Refl
  uninhabited (FarHead headPrf) = headContra headPrf

export
{eqContra : Not (x = x')} -> Uninhabited (HeadOf x ([] -: x')) where
  uninhabited SnocHead = eqContra Refl

export
{propContra : Not (Proper xs)} -> Uninhabited (HeadOf x xs) where
  uninhabited ConsHead = propContra ProperCons
  uninhabited SnocHead = propContra ProperSnoc
  uninhabited (FarHead headPrf) = propContra ProperSnoc

------------------
-- HeadOf function
------------------

public export
headOf : (xs : BList a) -> (0 propPrf : Proper xs) -> (x : a ** HeadOf x xs)
headOf (x :- xs) propPrf = (x ** ConsHead)
headOf (xs -: x) propPrf = case decProper xs of
  No propContra => (x ** rewrite notProperNil propContra in SnocHead)
  Yes propPrf'' => let (x' ** propPrf') = headOf xs propPrf'' in (x' ** FarHead propPrf')

-------------------
-- Decidable HeadOf
-------------------

public export
decHeadOf : DecEq a => (x : a) -> (xs : BList a) -> Dec (HeadOf x xs)
decHeadOf x [] = No absurd
decHeadOf x (x' :- xs) = case decEq x x' of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in ConsHead)
decHeadOf x (xs -: x') = case decHeadOf x xs of
    No headContra => case decEq xs [] of
      No eqContra => No absurd
      Yes eqPrf => case decEq x x' of
        No eqContra' => rewrite eqPrf in No absurd
        Yes eqPrf' => Yes (rewrite eqPrf in rewrite eqPrf' in SnocHead)
    Yes headPrf => Yes (FarHead headPrf)

----------------
-- Head function
----------------

public export
head : (xs : BList a) -> (0 propPrf : Proper xs) -> a
head (x :- xs) propPrf = x
head (xs -: x) propPrf = case decProper xs of
  No propContra => x
  Yes propPrf' => head xs propPrf'

-----------
-- Theorems
-----------

export
headOfProper : HeadOf x xs -> Proper xs
headOfProper ConsHead = ProperCons
headOfProper SnocHead = ProperSnoc
headOfProper (FarHead _) = ProperSnoc

export
prfToHeadEq : DecEq a => {xs : BList a} -> {0 propPrf : Proper xs} -> HeadOf x xs -> head xs propPrf = x
prfToHeadEq {xs=x' :- xs'} ConsHead = Refl
prfToHeadEq {xs=xs' -: x'} headPrf with (decProper xs')
  prfToHeadEq {xs=xs' -: x'} headPrf | No propContra with (notProperNil propContra)
    prfToHeadEq {xs=[] -: x'} SnocHead | No propContra | Refl = Refl
  prfToHeadEq {xs=xs' -: x'} (FarHead headPrf) | Yes propPrf' = prfToHeadEq headPrf

export
headEqToPrf : {xs : BList a} -> {0 propPrf : Proper xs} -> head xs propPrf = x -> HeadOf x xs
headEqToPrf {xs=x' :- xs'} Refl = ConsHead
headEqToPrf {xs=xs' -: x'} Refl with (decProper xs')
  headEqToPrf {xs=xs' -: x'} Refl | No propContra with (notProperNil propContra)
    headEqToPrf {xs=[] -: x'} Refl | No propContra | Refl = SnocHead
  headEqToPrf {xs=xs' -: x'} Refl | Yes propPrf' = FarHead (headEqToPrf {propPrf=propPrf'} Refl)

export
snocHead : HeadOf x xs -> HeadOf x (xs -: z)
snocHead ConsHead = FarHead ConsHead
snocHead SnocHead = FarHead SnocHead
snocHead (FarHead headPrf) = FarHead (snocHead headPrf)














-------
-- Last
-------

-- public export
-- last : (xs : BList a) -> (0 propPrf : Proper xs) -> a
-- last (x :- xs) _ = case decProper xs of
--   No propContra => x
--   Yes propPrf => last xs propPrf
-- last (xs -: x) _ = x

------------------
-- LastOf property
------------------

-- public export
-- data LastOf : a -> BList a -> Type where
--   SnocLast : {x : a} -> LastOf x (xs -: x)
--   ConsLast : {x : a} -> LastOf x (x :- [])
--   FarLast : {x : a} -> LastOf x xs -> LastOf x (x' :- xs)

-- export
-- Uninhabited (LastOf x []) where
--   uninhabited _ impossible

-- export
-- {eqContra : Not (x = x')} -> Uninhabited (LastOf x (xs -: x')) where
--   uninhabited SnocLast = eqContra Refl

-- export
-- {lastContra : Not (LastOf x xs)} -> {eqContra : Not (xs = [])} -> Uninhabited (LastOf x (x' :- xs)) where
--   uninhabited ConsLast = eqContra Refl
--   uninhabited (FarLast lastPrf) = lastContra lastPrf

-- export
-- {eqContra : Not (x = x')} -> Uninhabited (LastOf x (x' :- [])) where
--   uninhabited ConsLast = eqContra Refl

-- export
-- {propContra : Not (Proper xs)} -> Uninhabited (LastOf x xs) where
--   uninhabited SnocLast = propContra ProperSnoc
--   uninhabited ConsLast = propContra ProperCons
--   uninhabited (FarLast lastPrf) = propContra ProperCons

-- public export
-- lastOf : {0 x : a} -> LastOf x xs -> a
-- lastOf (SnocLast {x}) = x
-- lastOf (ConsLast {x}) = x
-- lastOf (FarLast _ {x}) = x

-- public export
-- decLastOf : DecEq a => (x : a) -> (xs : BList a) -> Dec (LastOf x xs)
-- decLastOf x [] = No absurd
-- decLastOf x (x' :- xs) = case decLastOf x xs of
--     No lastContra => case decEq xs [] of
--       No eqContra => No absurd
--       Yes eqPrf => case decEq x x' of
--         No eqContra' => rewrite eqPrf in No absurd
--         Yes eqPrf' => Yes (rewrite eqPrf in rewrite eqPrf' in ConsLast)
--     Yes lastPrf => Yes (FarLast lastPrf)
-- decLastOf x (xs -: x') = case decEq x x' of
--   No eqContra => No absurd
--   Yes eqPrf => Yes (rewrite eqPrf in SnocLast)

------------------
-- LastOf theorems
------------------

-- export
-- lastOfProper : LastOf x xs -> Proper xs
-- lastOfProper SnocLast = ProperSnoc
-- lastOfProper ConsLast = ProperCons
-- lastOfProper (FarLast _) = ProperCons

-- export
-- prfToLastEq : DecEq a => {xs : BList a} -> {0 propPrf : Proper xs} -> LastOf x xs -> last xs propPrf = x
-- prfToLastEq {xs=x' :- xs'} lastPrf with (decProper xs')
--   prfToLastEq {xs=x' :- xs'} lastPrf | No propContra with (notProperNil propContra)
--     prfToLastEq {xs=x' :- []} ConsLast | No propContra | Refl = Refl
--   prfToLastEq {xs=x' :- xs'} (FarLast lastPrf) | Yes propPrf' = prfToLastEq lastPrf
-- prfToLastEq {xs=xs' -: x'} SnocLast = Refl

-- export
-- lastEqToPrf : {xs : BList a} -> {0 propPrf : Proper xs} -> last xs propPrf = x -> LastOf x xs
-- lastEqToPrf {xs=x' :- xs'} Refl with (decProper xs')
--   lastEqToPrf {xs=x' :- xs'} Refl | No propContra with (notProperNil propContra)
--     lastEqToPrf {xs=x' :- []} Refl | No propContra | Refl = ConsLast
--   lastEqToPrf {xs=x' :- xs'} Refl | Yes propPrf' = FarLast (lastEqToPrf {propPrf=propPrf'} Refl)
-- lastEqToPrf {xs=xs' -: x'} Refl = SnocLast

-- export
-- snocLast : LastOf x xs -> LastOf x (z :- xs)
-- snocLast SnocLast = FarLast SnocLast
-- snocLast ConsLast = FarLast ConsLast
-- snocLast (FarLast lastPrf) = FarLast (snocLast lastPrf)
