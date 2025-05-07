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
