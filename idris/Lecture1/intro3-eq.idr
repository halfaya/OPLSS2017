import Data.Vect

data EqNat : Nat -> Nat -> Type where
     SameNat : (num : Nat) -> EqNat num num

smallProofEq : EqNat (2 + 2) 4
smallProofEq = SameNat 4

{-
jEqNat : (P : (x, y : Nat) -> SameNat x y -> Type) ->
         (x1 : Nat) ->
         (m : (y : Nat) -> (p : SameNat x1 y) -> P x1 y (Sam
-}         

successorEq : EqNat x y -> EqNat (S x) (S y)
successorEq (SameNat x) = SameNat (S x)

{- Built in equality type:

data (=) : a -> b -> Type where
     Refl : x = x

-}

smallProof : 2 + 2 = 4
smallProof = Refl

{- Equality in action! -}

myZip : Vect n a -> Vect n b -> Vect n (a, b)
myZip []        []        = []
myZip (x :: xs) (y :: ys) = (x, y) :: myZip xs ys

tryZip : Vect n a -> Vect m b -> Maybe (Vect n (a, b))
tryZip [] []        = Just []
tryZip [] (x :: xs) = Nothing
tryZip (x :: xs) [] = Nothing
tryZip (x :: xs) (y :: ys) = case tryZip xs ys of
                               Nothing => Nothing
                               Just zs => Just ((x , y) :: zs)
