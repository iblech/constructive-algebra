{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, StandaloneDeriving #-}
module Euclidean where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/))
import qualified Prelude as P
import Ring
import Field
import Nat
import Data.Ratio

class (IntegralDomain a) => EuclideanRing a where
    degree  :: a -> Nat
    -- muss auf 0 nicht definiert sein

    quotRem :: a -> a -> (a,a)
    -- muss für zweites Argument null nicht definiert sein

-- Dummytyp, um das Typsystem davon zu überzeugen, dass ein ER-Typ vorliegt
newtype (EuclideanRing a) => ER a = ER { unER :: a }
    deriving (Eq,Ring,IntegralDomain,Field,EuclideanRing,Num,Fractional,TestableAssociatedness)
instance (Show a, EuclideanRing a) => Show (ER a) where
    show        = show . unER
    showsPrec i = showsPrec i . unER
    showList    = showList . map unER

deriving instance (EuclideanRing a, Field a) => EuclideanRing (F a)

instance EuclideanRing Integer where
    degree  = abs
    quotRem = P.quotRem

instance (IntegralDomain a, P.Integral a) => EuclideanRing (Ratio a) where
    degree x
        | x == zero = error "degree zero"
        | otherwise = 1
    quotRem x y = (x/y, zero)
{-
instance (Field a, Eq a, IntegralDomain a) => EuclideanRing a where
    degree x
        | x == zero = error "degree zero"
        | otherwise = 1
    quotRem x y = (x/y, zero)
-}

gcd :: (EuclideanRing a, Eq a) => a -> a -> (a,a,a,a)
gcd = gcd_ (\_ _ -> Nothing)

gcd' :: (EuclideanRing a, Eq a, TestableAssociatedness a) => a -> a -> (a,a,a,a)
gcd' = gcd_ areAssociated

gcd_ :: (EuclideanRing a, Eq a) => (a -> a -> Maybe a) -> a -> a -> (a,a,a,a)
gcd_ associatednessTest a b
    | b == zero
    = (unit, zero, unit, zero)
    | Just u <- associatednessTest a b
    = (unit, zero, unit, u)
    | otherwise
    = (u,v,s,t)
        where
        (u',v',s',t') = gcd_ associatednessTest b r
        (q,r)         = a `quotRem` b
        u             = v'
        v             = u' - q * v'
        s             = t' + q * s'
        t             = s'
