merge : Ord a => (List a, List a) -> List a
merge ([], cs) = cs
merge (bs, []) = bs
merge (b :: bs, c :: cs) =
  if (b < c)
  then b :: merge (bs, c :: cs)
  else c :: merge (b :: bs, cs)

mergeSort : Ord a => List a -> List a
mergeSort []        = []
mergeSort (x :: []) = [x]
mergeSort ys@(x :: (y :: xs)) =
  case splitAt (length ys `div` 2) ys of
  (bs, cs) => merge (mergeSort bs) (mergeSort cs)

{-
data SplitRec : List a -> Type where
     SplitRecNil : SplitRec []
     SplitRecOne : {x : a} -> SplitRec [x]
     SplitRecPair : {lefts, rights : List a} ->
                    (lrec : Lazy (SplitRec lefts)) ->
                    (rrec : Lazy (SplitRec rights)) ->
                    SplitRec (lefts ++ rights)
-}
