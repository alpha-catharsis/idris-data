--------------------
-- Module definition
--------------------

module Data.BList.Backward

-------------------
-- Internal imports
-------------------

import Data.BList.BList

-------------------
-- Backward property
-------------------

public export
data Backward : BList a -> Type where
  BwdNil : Backward []
  BwdSnoc : Backward (xs -: x)

export
Uninhabited (Backward (xs :- x)) where
  uninhabited _ impossible

--------------------
-- Decidable Backward
--------------------

public export
decBackward : (xs : BList a) -> Dec (Backward xs)
decBackward [] = Yes BwdNil
decBackward (x :- xs) = No absurd
decBackward (xs -: x) = Yes BwdSnoc

-----------
-- Theorems
-----------

export
snocBackward : Backward xs -> Backward (xs -: x)
snocBackward BwdNil = BwdSnoc
snocBackward BwdSnoc = BwdSnoc
