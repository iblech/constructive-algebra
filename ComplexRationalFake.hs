module ComplexRationalFake where

data ComplexRational = Double :+: Double
    deriving (Show,Eq)

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
    fromRational r = fromRational r :+: 0

magnitudeSq :: ComplexRational -> Double
magnitudeSq (x :+: y) = x^2 + y^2

magnitudeBound :: ComplexRational -> Integer
magnitudeBound = succ . round . sqrt . magnitudeSq
-- Hack, sollte ohne sqrt auskommen!

goldenRatioSeq :: Integer -> ComplexRational
goldenRatioSeq n = (phi :+: 0) + 1 / (fromInteger n + 1) where phi = (1 + sqrt 5) / 2

sqrt2Seq :: Integer -> ComplexRational
sqrt2Seq n = (sqrt 2 :+: 0) + 1 / (fromInteger n + 1)
