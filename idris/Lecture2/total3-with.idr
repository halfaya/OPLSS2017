listTail : List a -> Maybe (List a)
listTail []        = Nothing
listTail (x :: xs) = Just xs

listInit : List a -> Maybe (List a)
listInit []        = Nothing
listInit (x :: []) = Nothing
listInit (x :: (y :: xs)) = case listInit (y :: xs) of
  Nothing => Just [x]
  Just ys => Just (x :: ys)

listInit' : List a -> Maybe (List a)
listInit' []        = Nothing
listInit' (x :: []) = Nothing
listInit' (x :: (y :: xs)) with (listInit (y :: xs))
  | Nothing = Just [x]
  | Just ys = Just (x :: ys)

data SnocList : List a -> Type where
     Empty : SnocList []
     Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])
     
snocListHelp : (snoc : SnocList input) ->
               (rest : List a) -> SnocList (input ++ rest)
snocListHelp {input} snoc []
    = rewrite appendNilRightNeutral input in snoc
snocListHelp {input} snoc (x :: xs)
    = rewrite appendAssociative input [x] xs in
              snocListHelp (Snoc snoc) xs

snocList : (xs : List a) -> SnocList xs
snocList xs = snocListHelp Empty xs

snocListToReversedList : {a : Type} -> {xs : List a } -> SnocList xs -> List a
snocListToReversedList Empty          = []
snocListToReversedList (Snoc {x} rec) = x :: snocListToReversedList rec

myReverse : List a -> List a
myReverse xs = snocListToReversedList (snocList xs)

myReverse' : List a -> List a
myReverse' [] = []
myReverse' (x :: xs) = myReverse xs ++ [x]

{-

data ListLast : List a -> Type where
     LEmpty : ListLast []
     LNonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

listLast : (xs : List a) -> ListLast xs

listInitHelp : (xs : List a) -> ListLast xs -> Maybe (List a)
listInitHelp [] LEmpty = Nothing
listInitHelp (ys ++ [x]) (LNonEmpty ys x) = Just ys

-}
