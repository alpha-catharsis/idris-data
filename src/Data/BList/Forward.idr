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
  FwdCons : Forward xs -> Forward (x :- xs)

export
Uninhabited (Forward (xs -: x)) where
  uninhabited _ impossible

export
{fwdContra : Not (Forward xs)} -> Uninhabited (Forward (x :- xs)) where
  uninhabited (FwdCons fwdPrf) = fwdContra fwdPrf

--------------------
-- Decidable Forward
--------------------

public export
decForward : (xs : BList a) -> Dec (Forward xs)
decForward [] = Yes FwdNil
decForward (x :- xs) = case decForward xs of
  No fwdContra => No absurd
  Yes fwdPrf => Yes (FwdCons fwdPrf)
decForward (xs -: x) = No absurd

-----------
-- Theorems
-----------

export
consForward : Forward xs -> Forward (x :- xs)
consForward FwdNil = FwdCons FwdNil
consForward (FwdCons fwdPrf) = FwdCons (consForward fwdPrf)
