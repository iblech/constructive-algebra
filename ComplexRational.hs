module ComplexRational where

data ComplexRational = Rational :+: Rational
    deriving (Show,Eq)

instance Num ComplexRational where
    (x :+: y) + (x' :+: y') = (x + x') :+: (y + y')
    (x :+: y) * (x' :+: y') = (x*x' - y*y') :+: (x*y' + y*x')
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
