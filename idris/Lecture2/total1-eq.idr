import Data.Vect

%default total

data EqNat : Nat -> Nat -> Type where
     SameNat : (num : Nat) -> EqNat num num

smallProofEq : EqNat (2 + 2) 4
smallProofEq = SameNat 4

successorEq : EqNat x y -> EqNat (S x) (S y)
successorEq (SameNat x) = SameNat (S x)

{- Built in equality type:

data (=) : a -> b -> Type where
     Refl : x = x

-}

smallProof : 2 + 2 = 4
smallProof = Refl

notTrue : 2 + 2 = 5 -> Void
notTrue Refl impossible

{- Equality in action! -}

myZip : Vect n a -> Vect n b -> Vect n (a, b)
myZip [] [] = []
myZip (x :: xs) (y :: ys) = (x, y) :: myZip xs ys


tryZip : Vect n a -> Vect m b -> Maybe (Vect n (a, b))
tryZip [] [] = Just []
tryZip [] (x :: xs) = Nothing
tryZip (x :: xs) [] = Nothing
tryZip (x :: xs) (y :: ys) = case tryZip xs ys of
  Nothing => Nothing
  Just zs => Just ((x,y) :: zs)
  
zeroNotSucc : (0 = S k) -> Void
zeroNotSucc Refl impossible

succNotZero : (S k = 0) -> Void
succNotZero Refl impossible

successorFail : (contra : (k = j) -> Void) -> (S k = S j) -> Void
successorFail contra Refl = contra Refl

checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (n = m)
checkEqNat Z     Z     = Just Refl
checkEqNat Z     (S k) = Nothing
checkEqNat (S k) Z     = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing   => Nothing
                              Just Refl => Just Refl
                              
checkEqNat' : (n : Nat) -> (m : Nat) -> Dec (n = m)
checkEqNat' Z     Z     = Yes Refl
checkEqNat' Z     (S k) = No zeroNotSucc
checkEqNat' (S k) Z     = No succNotZero
checkEqNat' (S k) (S j) =
  case checkEqNat' k j of
    (Yes Refl)  => Yes Refl
    (No contra) => No (successorFail contra)

tryZip' : Vect n a -> Vect m b -> Maybe (Vect n (a, b))
tryZip' {n} {m} xs ys = case checkEqNat n m of
  Nothing => Nothing
  Just Refl => Just (myZip xs ys)

headNotEq : (contra : (x = y) -> Void) -> (with List (x :: xs) = (y :: xs)) -> Void
headNotEq contra Refl = contra Refl

tailNotEq : (contra : (xs = ys) -> Void) -> (with List (x :: xs) = (y :: ys)) -> Void
tailNotEq contra Refl = contra Refl

checkEqList : DecEq a => (l : List a) -> (m : List a) -> Dec (l = m)
checkEqList [] [] = Yes Refl
checkEqList [] (x :: xs) = No (\(Refl) impossible)
checkEqList (x :: xs) [] = No (\(Refl) impossible)
checkEqList (x :: xs) (y :: ys) =
  case checkEqList xs ys of
    (Yes Refl)  => (case decEq x y of
                         (Yes Refl)  => Yes Refl
                         (No contra) => No (headNotEq contra))
    (No contra) => No (tailNotEq contra)

vFoldl : (a : Nat -> Type) ->
         (f : {m : Nat} -> a m -> b -> a (succ m)) -> a 0 -> Vect n b -> a n
vFoldl a f x []        = x
vFoldl a f x (y :: ys) = vFoldl (\n => a (succ n)) f (f x y) ys

myReverseFold : Vect n a -> Vect n a
myReverseFold xs = vFoldl (\n => Vect n a) (\ys, y => y :: ys) Data.Vect.Nil xs

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse {n = S k} (x :: xs) = rewrite (plusCommutative 1 k) in (myReverse xs ++ [x])
--myReverse ((::) {len = len} x xs) = rewrite (plusCommutative 1 len) in (myReverse xs ++ [x])

buildEqVect : (p : x = y) -> (p1 : xs = ys) -> (with Vect (x :: xs) = (y :: ys))
buildEqVect Refl Refl = Refl

tailNotEqV : (contra : (xs = ys) -> Void) -> (with Vect (x :: xs) = (y :: ys)) -> Void
tailNotEqV contra Refl = contra Refl

headNotEqV : (contra : (x = y) -> Void) -> (with Vect (x :: xs) = (y :: ys)) -> Void
headNotEqV contra Refl = contra Refl

checkEqVect : DecEq a => (k : Vect n a) -> (l : Vect n a) -> Maybe (k = l)
checkEqVect []        []        = Nothing
checkEqVect (x :: xs) (y :: ys) =
  case decEq x y of
    Yes p => case checkEqVect xs ys of
      Nothing => Nothing
      Just p1 => Just (buildEqVect p p1)
    No  p => Nothing

checkEqVect' : DecEq a => (k : Vect n a) -> (l : Vect n a) -> Dec (k = l)
checkEqVect' [] [] = Yes Refl
checkEqVect' (x :: xs) (y :: ys) =
  case decEq x y of
    Yes p => case checkEqVect' xs ys of
      Yes p1 => Yes (buildEqVect p p1)
      No  p1 => No (tailNotEqV p1)
    No  p => No (headNotEqV p)

lengthNotEq : (k : Vect m a) -> (l : Vect n a) -> (contra : (m = n) -> Void) -> (k = l) -> Void
lengthNotEq l l contra Refl = contra Refl

checkEqVect2 : {m : Nat} -> {n : Nat} -> DecEq a => (k : Vect m a) -> (l : Vect n a) -> Dec (k = l)
checkEqVect2 {m = m} {n = n} k l =
  case decEq m n of
    (Yes Refl)   => checkEqVect' k l
    (No contra)  => No (lengthNotEq k l contra)

 
