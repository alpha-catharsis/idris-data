--------------------
-- Module definition
--------------------

module Data.BList.Forward

-------------------
-- Internal imports
-------------------

import Data.BList.BList

-------------------
-- Forward property
-------------------

public export
data Forward : BList a -> Type where
  FwdNil : Forward []
  FwdCons : Forward (x :- xs)

export
Uninhabited (Forward (xs -: x)) where
  uninhabited _ impossible

--------------------
-- Decidable Forward
--------------------

public export
decForward : (xs : BList a) -> Dec (Forward xs)
decForward [] = Yes FwdNil
decForward (x :- xs) = Yes FwdCons
decForward (xs -: x) = No absurd

-----------
-- Theorems
-----------

export
consForward : Forward xs -> Forward (x :- xs)
consForward FwdNil = FwdCons
consForward FwdCons = FwdCons
