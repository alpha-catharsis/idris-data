--------------------
-- Module definition
--------------------

module Data.BList.MakeBackward

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Backward
import Data.BList.Append

------------------------
-- Make backward function
------------------------

public export
mkBackward : BList a -> BList a
mkBackward xs = [] +: xs

-----------
-- Theorems
-----------

export
mkBackwardBackward : {xs : BList a} -> Backward (mkBackward xs)
mkBackwardBackward = appendBackward BwdNil
