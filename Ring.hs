module Ring where

import qualified Prelude as P
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

class (Ring a) => IntegralDomain a

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

instance Ring P.Integer where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
instance IntegralDomain P.Integer

instance (IntegralDomain a, P.Integral a) => Ring (Ratio a) where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
instance (IntegralDomain a, P.Integral a) => IntegralDomain (Ratio a)
