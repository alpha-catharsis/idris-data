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

import Data.BList.Append
import Data.BList.BList
import Data.BList.Equiv
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

-- export
-- EquivRightRel HeadOf where
--   equivRightRel ConsHead (EquivC equivPrf) = ConsHead
--   equivRightRel ConsHead (EquivSC equivPrf) = FarHead ConsHead
--   equivRightRel SnocHead (EquivS equivPrf) = ?c
--   equivRightRel (FarHead headPrf) (EquivS equivPrf) = ?d
--   equivRightRel (FarHead headPrf) (EquivCS equivPrf) = ?e

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
headOfProper : HeadOf x xs -> Proper xs
headOfProper ConsHead = ProperCons
headOfProper SnocHead = ProperSnoc
headOfProper (FarHead _) = ProperSnoc

export
snocHead : HeadOf x xs -> HeadOf x (xs -: z)
snocHead ConsHead = FarHead ConsHead
snocHead SnocHead = FarHead SnocHead
snocHead (FarHead headPrf) = FarHead (snocHead headPrf)

