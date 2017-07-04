data Elem : a -> List a -> Type where
     Here : Elem x (x :: xs)
     There : Elem x ys -> Elem x (y :: ys)

Beatles : List String
Beatles = ["John", "Paul", "George", "Ringo"]

georgeInBeatles : Elem "George" Beatles
georgeInBeatles = There (There Here)

peteNotInBeatles : Not (Elem "Pete" Beatles)
peteNotInBeatles = \x => case x of
  There a => case a of
    There b => case b of
      There c => case c of
        There d => case d of
          There impossible

peteNotInBeatles' : Not (Elem "Pete" Beatles)
peteNotInBeatles' (There (There (There (There Here))))      impossible
peteNotInBeatles' (There (There (There (There (There _))))) impossible

isElem : DecEq a => (x : a) -> (xs : List a) -> Maybe (Elem x xs)
isElem x []        = Nothing
isElem x (y :: xs) = case decEq x y of
  Yes Refl => Just Here
  No  p => case isElem x xs of
    Nothing => Nothing
    Just x  => Just (There x)
