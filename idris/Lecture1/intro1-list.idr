{- Definition from the Prelude:

infixr 5 ::

data List a = Nil | (::) a (List a)
-}

my_append : List a -> List a -> List a
my_append []        ys = ys
my_append (x :: xs) ys = x :: (my_append xs ys)

my_map : (a -> b) -> List a -> List b
my_map f []        = []
my_map f (x :: xs) = f x :: my_map f xs

my_zipWith : (a -> b -> c) -> List a -> List b -> List c
my_zipWith f [] _ = []
my_zipWith f _ [] = []
my_zipWith f (x :: xs) (y :: ys) = f x y :: my_zipWith f xs ys
