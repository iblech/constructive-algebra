module ComplexRational where

import Data.List (genericIndex)
import qualified Prelude as P
import Prelude hiding (fromInteger, (+), (*), (-), (/), (^), negate, recip)

import Debug.Trace
import NumericHelper
import Ring
import Field

data ComplexRational = Rational :+: Rational
    deriving (Eq)

instance Show ComplexRational where
    show (x :+: y)
	| y == 0    = show x
	| otherwise = show x ++ " + i*" ++ show y

instance Ring ComplexRational where
    (x :+: y) + (x' :+: y') = (x + x') :+: (y + y')
    (x :+: y) * (x' :+: y') = (x*x' - y*y') :+: (x*y' + y*x')
    negate (x :+: y)        = negate x :+: negate y
    fromInteger i = fromInteger i :+: 0
    zero = fromInteger 0
    unit = fromInteger 1

instance Num ComplexRational where
    (+) = (+)
    (*) = (*)
    negate      = negate
    fromInteger = fromInteger
    signum      = error "signum on ComplexRational"
    abs         = error "abs on ComplexRational"

instance Field ComplexRational where
    recip (x :+: y)
	| sq == 0   = error "division by zero (ComplexRational)"
	| otherwise = (x/sq) :+: (-y/sq)
	where sq = x^2 + y^2

magnitudeSq :: ComplexRational -> Rational
magnitudeSq (x :+: y) = x^2 + y^2

magnitudeBound :: ComplexRational -> Integer
magnitudeBound = succ . round . sqrt . fromRational . magnitudeSq
-- Hack, sollte ohne sqrt auskommen!

-- Die Folge mit
--   a_1 = 1, a_(n+1) = 1 + 1/a_n
-- erfüllt |a_n - a| < (4/9)^n für alle n >= 2.
-- Diese Folge hier wird künstlich verlangsamt, sie erfüllt |x_n - x| < 1/n für
-- alle n >= 1.
goldenRatioSeq :: Integer -> ComplexRational
goldenRatioSeq n = xs `genericIndex` (ilogb 2 n + 2)
    where xs = iterate ((1 +) . recip) 1

-- Die Folge mit
--   a_1 = 1, a_(n+1) = 1/2 * (a_n + 2/a_n)
-- erfüllt |a_n - a| < 0.86^n für alle n >= 1.
-- Die Folge hier wird entsprechend künstlich verlangsamt.
-- Der Faktor 5 resultiert von -ld(0.86).
sqrt2Seq :: Integer -> ComplexRational
sqrt2Seq n = xs `genericIndex` (5 * ilogb 2 n + 1)
    where xs = iterate (\x -> (x + 2/x) / 2) 1
-- Konvergenz nur heuristisch überlegt!
