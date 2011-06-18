module Zero where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum)
import Polynomial
import Ring
import Field
import NumericHelper
import Complex
import Algebraic
import Polynomial
import Control.Monad
import Euclidean
import ComplexRational
import Real

-- Zählt die doppelte Anzahl von Vorzeichenänderungen
doubledSignChanges :: (Ring a, Ord a) => [a] -> Integer
doubledSignChanges xs = sum $ map f (pairs xs)
    where
    pairs []       = []
    pairs [x]      = []
    pairs (x:y:zs) = (x,y) : pairs (y:zs)
    f (x,y)
        | signum (x*y) == N      = 2
        | x == zero && y /= zero = 1
        | x /= zero && y == zero = 1
        | otherwise              = 0

doubledSignChanges' :: (Ring a, Ord a) => a -> a -> [Poly a] -> Integer
doubledSignChanges' a b ps = doubledSignChanges (map (eval a) ps) - doubledSignChanges (map (eval b) ps)

sturmChain :: (Field a, Eq a, IntegralDomain a) => Poly a -> Poly a -> [Poly a]
sturmChain r s
    | degree r > degree s = error "sturmChain"
    | otherwise           = euclidChain s r

doubledIndex :: (Field a, Eq a, IntegralDomain a, Ord a) => a -> a -> Poly a -> Poly a -> Integer
doubledIndex a b r s = doubledSignChanges' a b (sturmChain r s)

quadrupledWindingNumber :: ComplexRational -> ComplexRational -> Poly (Alg QinC) -> Integer
quadrupledWindingNumber (x :+: y) (x' :+: y') p
    = doubledIndex zero unit (fmap realComponent $ realPart gamma) (fmap realComponent $ imagPart gamma)
    where
    gamma = undefined

ex :: Poly (Alg QinC)
ex = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 2 + fromInteger 4 * Polynomial.constant imagUnit))
