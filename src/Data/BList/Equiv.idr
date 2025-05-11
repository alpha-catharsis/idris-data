--------------------
-- Module definition
--------------------

module Data.BList.Equiv

-------------------
-- External imports
-------------------

import Control.Relation
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Data.BList.BList

--------------
-- Equivalence
--------------

public export
data Equiv : BList a -> BList a -> Type where
  EquivN : Equiv [] []
  EquivNCS : Equiv (z :- []) ([] -: z)
  EquivNSC : Equiv ([] -: z) (z :- [])
  EquivC : Equiv xs ys -> Equiv (z :- xs) (z :- ys)
  EquivS : Equiv xs ys -> Equiv (xs -: w) (ys -: w)
  EquivCS : Equiv xs ys -> Equiv ((z :- xs) -: w) (z :- (ys -: w))
  EquivSC : Equiv xs ys -> Equiv (z :- (xs -: w)) ((z :- ys) -: w)

export
Uninhabited (Equiv [] (y :- ys)) where
  uninhabited _ impossible

export
Uninhabited (Equiv [] (ys -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- xs) []) where
  uninhabited _ impossible

export
Uninhabited (Equiv (xs -: x) []) where
  uninhabited _ impossible

export
{eqContra : Not (x = y)} -> Uninhabited (Equiv (x :- []) ([] -: y)) where
  uninhabited EquivNCS = eqContra Refl

export
{eqContra : Not (x = y)} -> Uninhabited (Equiv ([] -: x) (y :- [])) where
  uninhabited EquivNSC = eqContra Refl

export
Uninhabited (Equiv (x :- []) ((y' :- ys') -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- []) ((ys' -: y') -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- (x' :- xs')) ([] -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- (xs' -: x')) ([] -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- (x' :- xs')) ((y' :- ys') -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- (x' :- xs')) ((ys' -: y') -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv (x :- (xs' -: x')) ((ys' -: y') -: y)) where
  uninhabited _ impossible

export
Uninhabited (Equiv ([] -: x) (y :- (y' :- ys'))) where
  uninhabited _ impossible

export
Uninhabited (Equiv ([] -: x) (y :- (ys' -: y'))) where
  uninhabited _ impossible

export
Uninhabited (Equiv ((x' :- xs') -: x) (y :- [])) where
  uninhabited _ impossible

export
Uninhabited (Equiv ((x' :- xs') -: x) (y :- (y' :- ys'))) where
  uninhabited _ impossible

export
Uninhabited (Equiv ((xs' -: x') -: x) (y :- [])) where
  uninhabited _ impossible

export
Uninhabited (Equiv ((xs' -: x') -: x) (y :- (y' :- ys'))) where
  uninhabited _ impossible

export
Uninhabited (Equiv ((xs' -: x') -: x) (y :- (ys' -: y'))) where
  uninhabited _ impossible

export
{contra : Either (Not (x = y)) (Not (Equiv xs ys))} -> Uninhabited (Equiv (x :- xs) (y :- ys)) where
  uninhabited (EquivC equivPrf) = case contra of
    Left eqContra => eqContra Refl
    Right equivContra => equivContra equivPrf

export
{contra : Either (Not (x = y)) (Not (Equiv xs ys))} -> Uninhabited (Equiv (xs -: x) (ys -: y)) where
  uninhabited (EquivS equivPrf) = case contra of
    Left eqContra => eqContra Refl
    Right equivContra => equivContra equivPrf

export
{contra : Either (Not (x = y')) (Either (Not (x' = y)) (Not (Equiv xs' ys')))} ->
Uninhabited (Equiv (x :- (xs' -: x')) ((y' :- ys') -: y)) where
  uninhabited (EquivSC equivPrf) = case contra of
    Left eqContra => eqContra Refl
    Right (Left eqContra') => eqContra' Refl
    Right (Right equivContra) => equivContra equivPrf

export
{contra : Either (Not (x' = y)) (Either (Not (x = y')) (Not (Equiv xs' ys')))} ->
Uninhabited (Equiv ((x' :- xs') -: x) (y :- (ys' -: y'))) where
  uninhabited (EquivCS equivPrf) = case contra of
    Left eqContra => eqContra Refl
    Right (Left eqContra') => eqContra' Refl
    Right (Right equivContra) => equivContra equivPrf

------------------------
-- Decidable equivalence
------------------------

public export
decEquiv : DecEq a => (xs, ys : BList a) -> Dec (Equiv xs ys)
decEquiv [] [] = Yes EquivN
decEquiv [] (y :- ys) = No absurd
decEquiv [] (ys -: y) = No absurd
decEquiv (x :- xs) [] = No absurd
decEquiv (x :- xs) (y :- ys) = case decEq x y of
  No eqContra => No absurd
  Yes eqPrf =>  case decEquiv xs ys of
    No equivContra => No absurd
    Yes equivPrf => Yes (rewrite eqPrf in EquivC equivPrf)
decEquiv (x :- []) ([] -: y) = case decEq x y of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in EquivNCS)
decEquiv (x :- []) ((y' :- ys') -: y) = No absurd
decEquiv (x :- []) ((ys' -: y') -: y) = No absurd
decEquiv (x :- (x' :- xs')) ([] -: y) = No absurd
decEquiv (x :- (x' :- xs')) ((y' :- ys') -: y) = No absurd
decEquiv (x :- (x' :- xs')) ((ys' -: y') -: y) = No absurd
decEquiv (x :- (xs' -: x')) ([] -: y) = No absurd
decEquiv (x :- (xs' -: x')) ((y' :- ys') -: y) = case decEq x y' of
  No eqContra => No absurd
  Yes eqPrf => case decEq x' y of
    No eqContra' => No absurd
    Yes eqPrf' => case decEquiv xs' ys' of
      No equivContra => No absurd
      Yes equivPrf => Yes (rewrite eqPrf in rewrite eqPrf' in EquivSC equivPrf)
decEquiv (x :- (xs' -: x')) ((ys' -: y') -: y) = No absurd
decEquiv (xs -: x) [] = No absurd
decEquiv ([] -: x) (y :- []) = case decEq x y of
  No eqContra => No absurd
  Yes eqPrf => Yes (rewrite eqPrf in EquivNSC)
decEquiv ([] -: x) (y :- (y' :- ys')) = No absurd
decEquiv ([] -: x) (y :- (ys' -: y')) = No absurd
decEquiv ((x' :- xs') -: x) (y :- []) = No absurd
decEquiv ((x' :- xs') -: x) (y :- (y' :- ys')) = No absurd
decEquiv ((x' :- xs') -: x) (y :- (ys' -: y')) = case decEq x' y of
  No eqContra => No absurd
  Yes eqPrf => case decEq x y' of
    No eqContra' => No absurd
    Yes eqPrf' => case decEquiv xs' ys' of
      No equivContra => No absurd
      Yes equivPrf => Yes (rewrite eqPrf in rewrite eqPrf' in EquivCS equivPrf)
decEquiv ((xs' -: x') -: x) (y :- []) = No absurd
decEquiv ((xs' -: x') -: x) (y :- (y' :- ys')) = No absurd
decEquiv ((xs' -: x') -: x) (y :- (ys' -: y')) = No absurd
decEquiv (xs -: x) (ys -: y) = case decEq x y of
  No eqContra => No absurd
  Yes eqPrf =>  case decEquiv xs ys of
    No equivContra => No absurd
    Yes equivPrf => Yes (rewrite eqPrf in EquivS equivPrf)

----------------
-- Baic theorems
----------------

-- export
-- equivCons : Equiv (x :- xs) (x :- ys) -> Equiv xs ys
-- equivCons (EquivC equivPrf) = equivPrf

-- export
-- equivSnoc : Equiv (xs -: x) (ys -: x) -> Equiv xs ys
-- equivSnoc (EquivS equivPrf) = equivPrf

-- export
-- equivConsSnoc : Equiv ((x :- xs) -: y) (x :- (ys -: y)) -> Equiv xs ys
-- equivConsSnoc (EquivCS equivPrf) = equivPrf

-- export
-- equivSnocCons : Equiv (x :- (xs -: y)) ((x :- ys) -: y) -> Equiv xs ys
-- equivSnocCons (EquivSC equivPrf) = equivPrf

-------------------------
-- Equivalence interfaces
-------------------------

-- public export
-- interface EquivProp (Prop : BList a -> Type) where
--   equivProp : Prop xs -> Equiv xs ys -> Prop ys

-- public export
-- interface EquivRel (Rel : BList a -> BList a -> Type) where
--   equivRel : Rel xs ys -> Equiv xs xs' -> Equiv ys ys' -> Rel xs' ys'

-- public export
-- interface EquivLeftRel (Rel : BList a -> b -> Type) where
--   equivLeftRel : Rel xs z -> Equiv xs ys -> Rel ys z

-- public export
-- interface EquivRightRel (Rel : b -> BList a -> Type) where
--   equivRightRel : Rel z xs -> Equiv xs ys -> Rel z ys

------------------------
-- Equivalence reflexive
------------------------

-- export
-- Reflexive (BList a) Equiv where
--   reflexive {x=[]} = EquivN
--   reflexive {x=x' :- xs} = EquivC reflexive
--   reflexive {x=xs -: x'} = EquivS reflexive

-- export
-- equivSameCS : {xs : BList a} -> Equiv ((z :- xs) -: w) (z :- (xs -: w))
-- equivSameCS = EquivCS reflexive

-- export
-- equivSameSC : {xs : BList a} -> Equiv (z :- (xs -: w)) ((z :- xs) -: w)
-- equivSameSC = EquivSC reflexive

------------------------
-- Equivalence symmetric
------------------------

-- equivSymmetric : Equiv xs ys -> Equiv ys xs
-- equivSymmetric EquivN = EquivN
-- equivSymmetric (EquivC equivPrf) = EquivC (equivSymmetric equivPrf)
-- equivSymmetric (EquivS equivPrf) = EquivS (equivSymmetric equivPrf)
-- equivSymmetric (EquivCS equivPrf) = EquivSC (equivSymmetric equivPrf)
-- equivSymmetric (EquivSC equivPrf) = EquivCS (equivSymmetric equivPrf)

-- export
-- Symmetric (BList a) Equiv where
--   symmetric = equivSymmetric

-------------------------------
-- Snoc/cons existence theorems
-------------------------------

-- export
-- equivConsExist : {xs, ys : BList a} -> Equiv xs (y :- ys) -> (xs' : BList a ** Equiv xs (y :- xs'))
-- equivConsExist {xs=x :- xs'} (EquivC equivPrf) = (xs' ** reflexive)
-- equivConsExist {xs=xs' -: x} equivPrf = (ys ** equivPrf)

-- export
-- equivSnocExist : {xs, ys : BList a} -> Equiv xs (ys -: y) -> (xs' : BList a ** Equiv xs (xs' -: y))
-- equivSnocExist {xs=x :- xs'} equivPrf = (ys ** equivPrf)
-- equivSnocExist {xs=xs' -: x} (EquivS equivPrf) = (xs' ** reflexive)

-------------------------
-- Equivalence transitive
-------------------------

-- equivTransitive : {xs, ys, zs : BList a} -> Equiv xs ys -> Equiv ys zs -> Equiv xs zs
-- equivTransitive EquivN EquivN = EquivN
-- equivTransitive (EquivC equivPrf) (EquivC equivPrf') = EquivC (equivTransitive equivPrf equivPrf')
-- equivTransitive (EquivC equivPrf {xs} {ys=ys -: w}) (EquivSC equivPrf' {xs=ys} {ys=zs}) = ?aa
-- equivTransitive (EquivS equivPrf) (EquivS equivPrf') = EquivS (equivTransitive equivPrf equivPrf')
-- equivTransitive (EquivS equivPrf {xs} {ys= z :- ys}) (EquivCS equivPrf' {xs=ys} {ys=zs}) = ?bb
-- equivTransitive (EquivCS equivPrf {xs} {ys}) (EquivC equivPrf' {xs=ys -: w} {ys=zs}) =
--   let (zs' ** prf) = equivSnocExist (symmetric equivPrf')
--       prf' = EquivC prf
--       xxx = EquivS equivPrf
--       yyy = transitive xxx prf'
--   in ?cc
-- equivTransitive (EquivCS equivPrf) (EquivSC equivPrf') = EquivS (EquivC (equivTransitive equivPrf equivPrf'))
-- equivTransitive (EquivSC equivPrf {xs} {ys}) (EquivS equivPrf' {xs=z :- ys} {ys=zs}) = ?dd
-- equivTransitive (EquivSC equivPrf) (EquivCS equivPrf') = EquivC (EquivS (equivTransitive equivPrf equivPrf'))
-- equivTransitive _ _ = ?z

-- export
-- Transitive (BList a) Equiv where
--   transitive = equivTransitive
