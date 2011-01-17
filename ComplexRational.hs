module ComplexRational where

import Data.List (genericIndex)

import NumericHelper

data ComplexRational = Rational :+: Rational
    deriving (Eq)

instance Show ComplexRational where
    show (x :+: y)
	| y == 0    = show x
	| otherwise = show x ++ " + i*" ++ show y

instance Num ComplexRational where
    (x :+: y) + (x' :+: y') = (x + x') :+: (y + y')
    (x :+: y) * (x' :+: y') = (x*x' - y*y') :+: (x*y' + y*x')
    negate (x :+: y)        = negate x :+: negate y
    abs    = error "abs on ComplexRational"
    signum = error "signum on ComplexRational"
    fromInteger i = fromInteger i :+: 0

instance Fractional ComplexRational where
    recip (x :+: y)
	| sq == 0   = error "division by zero (ComplexRational)"
	| otherwise = (x/sq) :+: (-y/sq)
	where sq = x^2 + y^2
    fromRational r = r :+: 0

magnitudeSq :: ComplexRational -> Rational
magnitudeSq (x :+: y) = x^2 + y^2

magnitudeBound :: ComplexRational -> Integer
magnitudeBound = succ . round . sqrt . fromRational . magnitudeSq
-- Hack, sollte ohne sqrt auskommen!

-- konvergiert viel zu schnell!, |a_n - a| < 1/2^n
-- konvergiert jetzt richtig.
goldenRatioSeq :: Integer -> ComplexRational
goldenRatioSeq n = iterate ((1 +) . recip) 1 `genericIndex` (ilogb 2 n + 1)

sqrt2Seq :: Integer -> ComplexRational
sqrt2Seq n = iterate (\x -> (x + 2/x) / 2) 1 `genericIndex` n
-- konvergiert wie schnell?
