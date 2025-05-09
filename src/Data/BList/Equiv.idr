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
