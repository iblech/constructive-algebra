module Stream where

import Prelude hiding (zipWith)

data Stream a = a :~: Stream a
    deriving (Show,Eq)
infixr 5 :~:

zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f (x :~: xs) (y :~: ys) = f x y :~: zipWith f xs ys

everyN :: Integer -> Stream a -> Stream a
everyN n = go 0
    where
    go 0 (x :~: xs) = x :~: go (n-1) xs
    go i (x :~: xs) = go (i-1) xs
