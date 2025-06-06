--------------------
-- Module definition
--------------------

module Data.BList.Prepend

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Data.BList.BList
import Data.BList.Forward
import Data.BList.Head
import Data.BList.Last
import Data.BList.Length
import Data.BList.Proper

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

export
prependSameHead : HeadOf x xs -> HeadOf x (xs :+ ys)
prependSameHead ConsHead = ConsHead
prependSameHead SnocHead = ConsHead
prependSameHead (FarHead headPrf) = prependSameHead headPrf

export
prependSameLast : {ys : BList a} -> LastOf x xs -> LastOf x (ys :+ xs)
prependSameLast {ys=[]} SnocLast = SnocLast
prependSameLast {ys=y' :- ys'} SnocLast = FarLast (prependSameLast SnocLast)
prependSameLast {ys=ys' -: y'} SnocLast = prependSameLast (FarLast SnocLast)
prependSameLast {ys=[]} ConsLast = ConsLast
prependSameLast {ys=y' :- ys'} ConsLast = FarLast (prependSameLast ConsLast)
prependSameLast {ys=ys' -: y'} ConsLast = prependSameLast (FarLast ConsLast)
prependSameLast {ys=[]} (FarLast lastPrf) = FarLast lastPrf
prependSameLast {ys=y' :- ys'} (FarLast lastPrf) = FarLast (prependSameLast (FarLast lastPrf))
prependSameLast {ys=ys' -: y'} (FarLast lastPrf) = prependSameLast (FarLast (FarLast lastPrf))

export
prependLengthSum : LengthOf xs m -> LengthOf ys n -> LengthOf (xs :+ ys) (m + n)
prependLengthSum NilLen NilLen = NilLen
prependLengthSum NilLen (ConsLen lenPrf') = ConsLen lenPrf'
prependLengthSum NilLen (SnocLen lenPrf') = SnocLen lenPrf'
prependLengthSum (ConsLen lenPrf) NilLen = ConsLen (prependLengthSum lenPrf NilLen)
prependLengthSum (ConsLen lenPrf) (ConsLen lenPrf') = ConsLen (prependLengthSum lenPrf (ConsLen lenPrf'))
prependLengthSum (ConsLen lenPrf) (SnocLen lenPrf') = ConsLen (prependLengthSum lenPrf (SnocLen lenPrf'))
prependLengthSum (SnocLen lenPrf {m}) NilLen = rewrite plusZeroRightNeutral m in
                                               rewrite sym (plusOneSucc m) in
                                               rewrite plusCommutative 1 m in prependLengthSum lenPrf (ConsLen NilLen)
prependLengthSum (SnocLen lenPrf {xs} {m}) (ConsLen lenPrf' {xs=ys} {m=n}) = rewrite plusSuccRightSucc m (S n)
                                                                             in prependLengthSum lenPrf (ConsLen (ConsLen lenPrf'))
prependLengthSum (SnocLen lenPrf {xs} {m}) (SnocLen lenPrf' {xs=ys} {m=n}) = rewrite plusSuccRightSucc m (S n)
                                                                             in prependLengthSum lenPrf (ConsLen (SnocLen lenPrf'))
