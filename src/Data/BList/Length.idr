--------------------
-- Module definition
--------------------

module Data.BList.Length

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Proper
import Data.BList.Equiv

--------------------
-- LengthOf property
--------------------

public export
data LengthOf : BList a -> Nat -> Type where
  NilLen : LengthOf [] 0
  ConsLen : LengthOf xs m -> LengthOf (x :- xs) (S m)
  SnocLen : LengthOf xs m -> LengthOf (xs -: x) (S m)

Uninhabited (LengthOf [] (S m)) where
  uninhabited _ impossible

Uninhabited (LengthOf (x :- xs) Z) where
  uninhabited _ impossible

{lenContra : Not (LengthOf xs m)} -> Uninhabited (LengthOf (x :- xs) (S m)) where
  uninhabited (ConsLen lenPrf) = lenContra lenPrf

Uninhabited (LengthOf (xs -: x) Z) where
  uninhabited _ impossible

{lenContra : Not (LengthOf xs m)} -> Uninhabited (LengthOf (xs -: x) (S m)) where
  uninhabited (SnocLen lenPrf) = lenContra lenPrf

--------------------
-- LengthOf function
--------------------

public export
lengthOf : (xs : BList a) -> (m : Nat ** LengthOf xs m)
lengthOf [] = (Z ** NilLen)
lengthOf (x :- xs) = let (m ** lenPrf) = lengthOf xs in (S m ** ConsLen lenPrf)
lengthOf (xs -: x) = let (m ** lenPrf) = lengthOf xs in (S m ** SnocLen lenPrf)

---------------------
-- Decidable LengthOf
---------------------

public export
decLength : (xs : BList a) -> (m : Nat) -> Dec (LengthOf xs m)
decLength [] Z = Yes NilLen
decLength [] (S m) = No absurd
decLength (x :- xs) Z = No absurd
decLength (x :- xs) (S m) = case decLength xs m of
  No lenContra => No absurd
  Yes lenPrf => Yes (ConsLen lenPrf)
decLength (xs -: x) Z = No absurd
decLength (xs -: x) (S m) = case decLength xs m of
  No lenCotra => No absurd
  Yes lenPrf => Yes (SnocLen lenPrf)

------------------
-- Length function
------------------

public export
length : BList a -> Nat
length [] = 0
length (x :- xs) = S (length xs)
length (xs -: x) = S (length xs)

-----------
-- Theorems
-----------

export
prfToLengthEq : LengthOf xs m -> length xs = m
prfToLengthEq NilLen = Refl
prfToLengthEq (ConsLen lenPrf) = cong S (prfToLengthEq lenPrf)
prfToLengthEq (SnocLen lenPrf) = cong S (prfToLengthEq lenPrf)

export
lengthEqToPrf : {xs : BList a} -> length xs = m -> LengthOf xs m
lengthEqToPrf {xs=[]} Refl = NilLen
lengthEqToPrf {xs=x :- xs'} Refl = ConsLen (lengthEqToPrf Refl)
lengthEqToPrf {xs=xs' -: x} Refl = SnocLen (lengthEqToPrf Refl)

export
zeroLengthNotProper : LengthOf xs 0 -> Not (Proper xs)
zeroLengthNotProper NilLen ProperCons impossible
zeroLengthNotProper NilLen ProperSnoc impossible

export
succLengthProper : LengthOf xs (S m) -> Proper xs
succLengthProper (ConsLen lenPrf) = ProperCons
succLengthProper (SnocLen lenPrf) = ProperSnoc

export
lengthConsSucc : LengthOf (x :- xs) (S m) -> LengthOf xs m
lengthConsSucc (ConsLen lenPrf) = lenPrf

export
lengthSnocSucc : LengthOf (xs -: x) (S m) -> LengthOf xs m
lengthSnocSucc (SnocLen lenPrf) = lenPrf

export
lengthConsSnoc : LengthOf (z :- xs) m -> LengthOf (xs -: w) m
lengthConsSnoc (ConsLen lenPrf) = SnocLen lenPrf

export
lengthSnocCons : LengthOf (xs -: w) m -> LengthOf (z :- xs) m
lengthSnocCons (SnocLen lenPrf) = ConsLen lenPrf

export
lengthConsSnocInv : LengthOf ((z :- xs) -: w) m -> LengthOf (z :- (xs -: w)) m
lengthConsSnocInv (SnocLen (ConsLen lenPrf)) = ConsLen (SnocLen lenPrf)

export
lengthSnocConsInv : LengthOf (z :- (xs -: w)) m -> LengthOf ((z :- xs) -: w) m
lengthSnocConsInv (ConsLen (SnocLen lenPrf)) = SnocLen (ConsLen lenPrf)

export
consLengthSucc : LengthOf xs m -> LengthOf (x :- xs) (S m)
consLengthSucc NilLen = ConsLen NilLen
consLengthSucc (ConsLen lenPrf) = ConsLen (consLengthSucc lenPrf)
consLengthSucc (SnocLen lenPrf) = ConsLen (SnocLen lenPrf)

export
snocLengthSucc : LengthOf xs m -> LengthOf (xs -: x) (S m)
snocLengthSucc NilLen = SnocLen NilLen
snocLengthSucc (ConsLen lenPrf) = SnocLen (ConsLen lenPrf)
snocLengthSucc (SnocLen lenPrf) = SnocLen (snocLengthSucc lenPrf)

export
EquivLeftRel LengthOf where
  equivLeftRel NilLen EquivN = NilLen
  equivLeftRel (ConsLen lenPrf) EquivNCS = SnocLen lenPrf
  equivLeftRel (ConsLen lenPrf) (EquivC equivPrf) = consLengthSucc (equivLeftRel {Rel=LengthOf} lenPrf equivPrf)
  equivLeftRel (ConsLen lenPrf) (EquivSC equivPrf) =
    lengthSnocConsInv (consLengthSucc (equivLeftRel {Rel=LengthOf} lenPrf (EquivS equivPrf)))
  equivLeftRel (SnocLen lenPrf) EquivNSC = ConsLen lenPrf
  equivLeftRel (SnocLen lenPrf) (EquivS equivPrf) = snocLengthSucc (equivLeftRel {Rel=LengthOf} lenPrf equivPrf)
  equivLeftRel (SnocLen lenPrf) (EquivCS equivPrf) =
    lengthConsSnocInv (snocLengthSucc (equivLeftRel {Rel=LengthOf} lenPrf (EquivC equivPrf)))
