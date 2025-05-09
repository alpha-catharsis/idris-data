--------------------
-- Module definition
--------------------

module Data.BList.MakeForward

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Forward
import Data.BList.Prepend

------------------------
-- Make forward function
------------------------

public export
mkForward : BList a -> BList a
mkForward xs = xs :+ []

-----------
-- Theorems
-----------

export
mkForwardForward : {xs : BList a} -> Forward (mkForward xs)
mkForwardForward = prependForward FwdNil
