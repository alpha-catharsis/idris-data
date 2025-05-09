--------------------
-- Module definition
--------------------

module Data.BList.Prepend

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Forward

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

export
prependRightNilNeutral : Forward xs -> xs :+ [] = xs
prependRightNilNeutral FwdNil = Refl
prependRightNilNeutral (FwdCons fwdPrf {x}) = cong (x :-) (prependRightNilNeutral fwdPrf)

export
prependForward : {xs : BList a} -> Forward ys -> Forward (xs :+ ys)
prependForward {xs=[]} fwdPrf = fwdPrf
prependForward {xs=x :- xs'} fwdPrf = FwdCons (prependForward fwdPrf)
prependForward {xs=xs' -: x} fwdPrf = prependForward (FwdCons fwdPrf)
