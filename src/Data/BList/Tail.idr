--------------------
-- Module definition
--------------------

module Data.BList.Tail

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
-- TailOf property
------------------

public export
data TailOf : BList a -> BList a -> Type where
  ConsTail : TailOf xs (x :- xs)
  SnocTail : TailOf [] ([] -: x)
  FarTail : TailOf ys xs -> TailOf (ys -: x') (xs -: x')

export
Uninhabited (TailOf ys []) where
  uninhabited _ impossible

export
{eqContra : Not (ys = xs)} -> Uninhabited (TailOf ys (x :- xs)) where
  uninhabited ConsTail = eqContra Refl

export
{propPrf : Proper xs} -> Uninhabited (TailOf [] (xs -: x)) where
  uninhabited SnocTail impossible

export
{contra : Either (Not (y = x)) (Not (TailOf ys xs))} -> Uninhabited (TailOf (ys -: y) (xs -: x)) where
  uninhabited (FarTail tailPrf) = case contra of
    Left eqContra => eqContra Refl
    Right tailContra => tailContra tailPrf

export
Uninhabited (TailOf (y :- ys) (xs -: x)) where
  uninhabited _ impossible

------------------
-- TailOf function
------------------

public export
tailOf : (xs : BList a) -> (0 propPrf : Proper xs) -> (ys : BList a ** TailOf ys xs)
tailOf (x :- xs) propPrf = (xs ** ConsTail)
tailOf (xs -: x) propPrf = case decProper xs of
  No propContra => ([] ** rewrite notProperNil propContra in SnocTail)
  Yes propPrf' => let (xs' ** propPrf'') = tailOf xs propPrf' in (xs' -: x ** FarTail propPrf'')

-------------------
-- Decidable TailOf
-------------------

public export
decTailOf : DecEq a => (ys : BList a) -> (xs : BList a) -> Dec (TailOf ys xs)
decTailOf ys [] = No absurd
decTailOf ys (x :- xs) = case decEq ys xs of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in ConsTail)
decTailOf [] (xs -: x) = case decProper xs of
  No propContra => Yes (rewrite notProperNil propContra in SnocTail)
  Yes propPrf => No absurd
decTailOf (y :- ys) (xs -: x) = No absurd
decTailOf (ys -: y) (xs -: x) = case decEq y x of
  No eqContra => No absurd
  Yes eqPrf => case decTailOf ys xs of
    No tailConta => No absurd
    Yes tailPrf => Yes (rewrite eqPrf in FarTail tailPrf)

----------------
-- Tail function
----------------

public export
tail : (xs : BList a) -> (0 propPrf : Proper xs) -> BList a
tail (x :- xs) propPrf = xs
tail (xs -: x) propPrf = case decProper xs of
  No propContra => []
  Yes propPrf' => tail xs propPrf' -: x

-----------
-- Theorems
-----------

-- export
-- EquivRightRel TailOf where
--   equivRightRel ConsTail (EquivC equivPrf) = ConsTail
--   equivRightRel ConsTail (EquivSC equivPrf) = FarTail ConsTail
--   equivRightRel SnocTail (EquivS equivPrf) = ?c
--   equivRightRel (FarTail tailPrf) (EquivS equivPrf) = ?d
--   equivRightRel (FarTail tailPrf) (EquivCS equivPrf) = ?e

export
prfToTailEq : DecEq a => {xs : BList a} -> {0 propPrf : Proper xs} -> TailOf ys xs -> tail xs propPrf = ys
prfToTailEq {xs=x' :- xs'} ConsTail = Refl
prfToTailEq {xs=xs' -: x'} tailPrf with (decProper xs')
  prfToTailEq {xs=xs' -: x'} tailPrf | No propContra' with (notProperNil propContra')
    prfToTailEq {xs=[] -: x'} SnocTail | No propContra' | Refl = Refl
  prfToTailEq {xs=xs' -: x'} (FarTail tailPrf) | Yes propPrf' = cong (-: x') (prfToTailEq tailPrf)

export
tailEqToPrf : {xs : BList a} -> {0 propPrf : Proper xs} -> tail xs propPrf = ys -> TailOf ys xs
tailEqToPrf {xs=x' :- xs'} Refl = ConsTail
tailEqToPrf {xs=xs' -: x'} Refl with (decProper xs')
  tailEqToPrf {xs=xs' -: x'} Refl | No propContra with (notProperNil propContra)
    tailEqToPrf {xs=[] -: x'} Refl | No propContra | Refl = SnocTail
  tailEqToPrf {xs=xs' -: x'} Refl | Yes propPrf' = FarTail (tailEqToPrf {propPrf=propPrf'} Refl)

export
tailOfProper : TailOf x xs -> Proper xs
tailOfProper ConsTail = ProperCons
tailOfProper SnocTail = ProperSnoc
tailOfProper (FarTail _) = ProperSnoc

