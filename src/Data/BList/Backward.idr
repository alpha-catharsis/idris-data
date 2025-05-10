--------------------
-- Module definition
--------------------

module Data.BList.Backward

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Equiv

-------------------
-- Backward property
-------------------

public export
data Backward : BList a -> Type where
  BwdNil : Backward []
  BwdSnoc : Backward xs -> Backward (xs -: x)

export
Uninhabited (Backward (xs :- x)) where
  uninhabited _ impossible

export
{bwdContra : Not (Backward xs)} -> Uninhabited (Backward (xs -: x)) where
  uninhabited (BwdSnoc bwdPrf) = bwdContra bwdPrf

--------------------
-- Decidable Backward
--------------------

public export
decBackward : (xs : BList a) -> Dec (Backward xs)
decBackward [] = Yes BwdNil
decBackward (x :- xs) = No absurd
decBackward (xs -: x) = case decBackward xs of
  No bwdContra => No absurd
  Yes bwdPrf => Yes (BwdSnoc bwdPrf)

-----------
-- Theorems
-----------

export
EquivProp Backward where
  equivProp BwdNil EquivN = BwdNil
  equivProp (BwdSnoc bwdPrf) (EquivS equivPrf) = BwdSnoc (equivProp bwdPrf equivPrf)

export
snocBackward : Backward xs -> Backward (xs -: x)
snocBackward BwdNil = BwdSnoc BwdNil
snocBackward (BwdSnoc bwdPrf) = BwdSnoc (snocBackward bwdPrf)
