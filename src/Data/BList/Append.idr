--------------------
-- Module definition
--------------------

module Data.BList.Append

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Data.BList.Backward
import Data.BList.BList
import Data.BList.Head
import Data.BList.Last
import Data.BList.Length

-------------------
-- Append operator
-------------------

export infixl 7 +:

public export
(+:) : BList a -> BList a -> BList a
xs +: [] = xs
xs +: (y :- ys) = (xs -: y) +: ys
xs +: (ys -: y) = (xs +: ys) -: y

-----------
-- Theorems
-----------

export
injAppendLeft : {ys : BList a} -> xs +: ys = zs +: ys -> xs = zs
injAppendLeft {ys=[]} Refl = Refl
injAppendLeft {ys=y :- ys'} eqPrf = injSnocLeft (injAppendLeft {ys=ys'} eqPrf)
injAppendLeft {ys=ys' -: y} eqPrf = injAppendLeft {ys=ys'} (injSnocLeft eqPrf)

export
appendLeftNilNeutral : Backward xs -> xs = [] +: xs
appendLeftNilNeutral BwdNil = Refl
appendLeftNilNeutral (BwdSnoc bwdPrf {x}) = cong (-: x) (appendLeftNilNeutral bwdPrf)

export
appendBackward : {xs : BList a} -> Backward ys -> Backward (ys +: xs)
appendBackward {xs=[]} bwdPrf = bwdPrf
appendBackward {xs=x :- xs'} bwdPrf = appendBackward (BwdSnoc bwdPrf)
appendBackward {xs=xs' -: x} bwdPrf = BwdSnoc (appendBackward bwdPrf)

export
prependSameLast : LastOf x xs -> LastOf x (ys +: xs)
prependSameLast SnocLast = SnocLast
prependSameLast ConsLast = SnocLast
prependSameLast (FarLast lastPrf) = prependSameLast lastPrf

export
prependSameHead : {ys : BList a} -> HeadOf x xs -> HeadOf x (xs +: ys)
prependSameHead {ys=[]} ConsHead = ConsHead
prependSameHead {ys=y' :- ys'} ConsHead = prependSameHead (FarHead ConsHead)
prependSameHead {ys=ys' -: y'} ConsHead = FarHead (prependSameHead ConsHead)
prependSameHead {ys=[]} SnocHead = SnocHead
prependSameHead {ys=y' :- ys'} SnocHead = prependSameHead (FarHead SnocHead)
prependSameHead {ys=ys' -: y'} SnocHead = FarHead (prependSameHead SnocHead)
prependSameHead {ys=[]} (FarHead headPrf) = FarHead headPrf
prependSameHead {ys=y' :- ys'} (FarHead headPrf) = prependSameHead (FarHead (FarHead headPrf))
prependSameHead {ys=ys' -: y'} (FarHead headPrf) = FarHead (prependSameHead (FarHead headPrf))

-- export
-- appendLengthSum : {n : Nat} -> LengthOf xs m -> LengthOf ys n -> LengthOf (ys +: xs) (m + n)
-- appendLengthSum NilLen NilLen = NilLen
-- appendLengthSum NilLen (ConsLen lenPrf') = ConsLen lenPrf'
-- appendLengthSum NilLen (SnocLen lenPrf') = SnocLen lenPrf'
-- appendLengthSum (ConsLen lenPrf) NilLen = rewrite plusZeroRightNeutral m in ?a4
-- appendLengthSum (ConsLen lenPrf) (ConsLen lenPrf') = ?a5
-- appendLengthSum (ConsLen lenPrf) (SnocLen lenPrf') = ?a6
-- appendLengthSum (SnocLen lenPrf) NilLen = SnocLen (appendLengthSum lenPrf NilLen)
-- appendLengthSum (SnocLen lenPrf {xs} {m}) (ConsLen lenPrf' {xs=ys} {m=n}) = SnocLen (appendLengthSum lenPrf (ConsLen lenPrf'))
-- appendLengthSum (SnocLen lenPrf {xs} {m}) (SnocLen lenPrf' {xs=ys} {m=n}) = SnocLen (appendLengthSum lenPrf (SnocLen lenPrf'))
