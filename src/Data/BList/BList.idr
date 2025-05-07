module Data.BList.BList

---------------------
-- Bidirectional list
---------------------

export infixr 7 :-
export infixl 7 -:

public export
data BList : Type -> Type where
  Nil : BList a
  (:-) : a -> BList a -> BList a
  (-:) : BList a -> a -> BList a

----------------
-- Show instance
----------------

showBList : Show a => BList a -> String
showBList [] = ""
showBList (x :- []) = show x
showBList (x :- xs) = show x ++ ", " ++ showBList xs
showBList ([] -: x) = show x
showBList (xs -: x) = showBList xs ++ ", " ++ show x

export
Show a => Show (BList a) where
  show [] = "[" ++ showBList [] {a} ++ "]"
  show (x :- xs) = "[" ++ show x ++ ", " ++ showBList xs ++ "]"
  show (xs -: x) = "[" ++ showBList xs ++ ", " ++ show x ++ "]"

----------------------
-- List representation
----------------------

export
repr : Show a => BList a -> String
repr [] = "[]"
repr (x :- xs) = case xs of
  [] => show x
  (_ :- _) => show x ++ " :- " ++ repr xs
  ([] -: _) => show x ++ " :- " ++ repr xs
  (_ -: _) => show x ++ " :- (" ++ repr xs ++ ")"
repr (xs -: x) = case xs of
  [] => show x
  (_ -: _) => repr xs  ++ " -: " ++ show x
  (_ :- []) => repr xs  ++ " -: " ++ show x
  (_ :- _) => "(" ++ repr xs ++ ") -: " ++ show x

----------------------------
-- Cons and snoc injectivity
----------------------------

export
injConsLeft : x :- xs = y :- xs -> x = y
injConsLeft Refl = Refl

export
injConsRight : x :- xs = x :- ys -> xs = ys
injConsRight Refl = Refl

export
injSnocLeft : xs -: x = ys -: x -> xs = ys
injSnocLeft Refl = Refl

export
injSnocRight : xs -: x = xs -: y -> x = y
injSnocRight Refl = Refl
