--------------------
-- Module definition
--------------------

module Data.BList.Append

-------------------
-- Internal imports
-------------------

import Data.BList.BList

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

