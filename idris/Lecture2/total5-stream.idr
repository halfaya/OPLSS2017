{- Productivity: streams -}

{- Stream is defined in the Prelude:

data Stream : Type -> Type where
  (::) : (value : elem) -> Inf (Stream elem) -> Stream elem

-}

countFrom : Nat -> Stream Nat
countFrom n = n :: Main.countFrom (S n)

firstn : Nat -> Stream Nat -> List Nat
firstn Z     xs        = []
firstn (S k) (x :: xs) = x :: firstn k xs
