module Ring where

import qualified Prelude as P
import Prelude (Maybe, (&&), (||), (==), (/=), abs, signum, otherwise)
import Data.Ratio

class Ring a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a
    zero   :: a
    unit   :: a
    negate :: a -> a
    fromInteger :: P.Integer -> a
    x - y = x + negate y
    infixl 6 +
    infixl 6 -
    infixl 7 *

    -- Zur Effizienzsteigerung, damit Null-Koeffizienten bei Polynomen
    -- gestrichen werden können.
    -- Es muss gelten: couldBeNonZero x == False  ==>  x == zero.
    couldBeNonZero :: a -> P.Bool
    couldBeNonZero = P.const P.True

class (Ring a) => IntegralDomain a

-- x ~ y :<=> ex. u inv'bar: y = u x
class (Ring a) => TestableAssociatedness a where
    areAssociated :: a -> a -> Maybe a
    -- Nothing, oder Just u (mit y = u x, in der Reihenfolge)

-- direkt ausm Prelude kopiert
(^) :: (Ring a) => a -> P.Integer -> a
x ^ 0           = unit
x ^ n | n P.> 0 = f x (n-1) x
    where f _ 0 y = y
          f x n y = g x n  where
                    g x n | P.even n  = g (x*x) (n `P.quot` 2)
                          | P.otherwise = f x (n-1) (x*y)
_ ^ _           = P.error "Prelude.^: negative exponent"
infixr 8 ^

instance Ring P.Int where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)

instance Ring P.Integer where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance IntegralDomain P.Integer
instance TestableAssociatedness P.Integer where
    areAssociated x y
        | abs x == abs y = P.Just (signum x * signum y)
        | otherwise      = P.Nothing

instance (IntegralDomain a, P.Integral a) => Ring (Ratio a) where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance (IntegralDomain a, P.Integral a) => IntegralDomain (Ratio a)
instance (IntegralDomain a, P.Integral a) => TestableAssociatedness (Ratio a) where
    areAssociated x y
        | x == zero && y == zero = P.Just 1
        | x /= zero && y /= zero = P.Just (y * P.recip x)
        | otherwise              = P.Nothing
