module Euclidean where

import Prelude hiding (gcd, quotRem, (+), (*), (-))
import qualified Prelude as P
import Ring
import Nat

class (IntegralDomain a) => EuclideanRing a where
    degree  :: a -> Nat
    -- muss auf 0 nicht definiert sein

    quotRem :: a -> a -> (a,a)
    -- muss für zweites Argument null nicht definiert sein

instance EuclideanRing Integer where
    degree  = abs
    quotRem = P.quotRem

gcd :: (EuclideanRing a, Eq a) => a -> a -> (a,a,a,a)
gcd a b
    | b == zero
    = (unit, zero, unit, zero)
    | otherwise
    = (u,v,s,t)
        where
        (u',v',s',t') = gcd b r
        (q,r)         = a `quotRem` b
        u             = v'
        v             = u' - q * v'
        s             = t' + q * s'
        t             = s'
