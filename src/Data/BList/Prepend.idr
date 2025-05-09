--------------------
-- Module definition
--------------------

module Data.BList.Prepend

-------------------
-- Internal imports
-------------------

import Data.BList.Backward
import Data.BList.BList

-------------------
-- Prepend operator
-------------------

export infixr 7 :+

public export
(:+) : BList a -> BList a -> BList a
[] :+ ys = ys
(x :- xs) :+ ys = x :- (xs :+ ys)
(xs -: x) :+ ys = xs :+ (x :- ys)

-----------
-- Theorems
-----------

export
injPrependRight : {xs : BList a} -> xs :+ ys = xs :+ zs -> ys = zs
injPrependRight {xs=[]} Refl = Refl
injPrependRight {xs=x :- xs'} eqPrf = injPrependRight {xs=xs'} (injConsRight eqPrf)
injPrependRight {xs=xs' -: x} eqPrf = injConsRight (injPrependRight {xs=xs'} eqPrf)

-- export
-- prependRightNilNeutral : Backward xs -> xs :+ [] = xs
-- prependRightNilNeutral BwdNil = Refl
-- prependRightNilNeutral BwdSnoc = ?b
