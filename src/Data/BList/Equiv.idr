--------------------
-- Module definition
--------------------

module Data.BList.Equiv

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
  EquivC : Equiv xs ys -> Equiv (z :- xs) (z :- ys)
  EquivS : Equiv xs ys -> Equiv (xs -: w) (ys -: w)
  EquivCS : Equiv xs ys -> Equiv ((z :- xs) -: w) (z :- (xs -: w))
  EquivSC : Equiv xs ys -> Equiv (z :- (xs -: w)) ((z :- xs) -: w)

-------------------------
-- Equivalence interfaces
-------------------------

public export
interface EquivProp (Prop : BList a -> Type) where
  equivProp : Prop xs -> Equiv xs ys -> Prop ys

public export
interface EquivRel (Rel : BList a -> BList a -> Type) where
  equivRel : Rel xs ys -> Equiv xs xs' -> Equiv ys ys' -> Rel xs' ys'

public export
interface EquivLeftRel (Rel : BList a -> b -> Type) where
  equivLeftRel : Rel xs z -> Equiv xs ys -> Rel ys z

public export
interface EquivRighttRel (Rel : b -> BList a -> Type) where
  equivRightRel : Rel z xs -> Equiv xs ys -> Rel z ys
