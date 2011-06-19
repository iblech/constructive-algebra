{-# LANGUAGE PatternGuards, TupleSections #-}
module Zero where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, quotRem, gcd)
import Polynomial
import Ring
import Field
import NumericHelper
import Complex hiding (constant)
import Algebraic
import Polynomial
import Control.Monad
import Euclidean
import ComplexRational
import Real
import IntegralClosure
import Debug.Trace

-- Zählt die Anzahl von Vorzeichenänderungen, Wechsel von/auf 0 zählen 1/2
signChanges :: (Ring a, Ord a) => [a] -> Rational
signChanges xs = sum $ map f (pairs xs)
    where
    pairs []       = []
    pairs [x]      = []
    pairs (x:y:zs) = (x,y) : pairs (y:zs)
    f (x,y)
        | signum (x*y) == N      = 1
        | x == zero && y /= zero = 1/2
        | x /= zero && y == zero = 1/2
        | otherwise              = 0

signChanges' :: (Ring a, Ord a) => a -> a -> [Poly a] -> Rational
signChanges' a b ps = signChanges (map (eval a) ps) - signChanges (map (eval b) ps)

sturmChain :: (Field a, Eq a, IntegralDomain a) => Poly a -> Poly a -> [Poly a]
sturmChain r s
    | degree r > degree s = error "sturmChain"
    | otherwise           = euclidChain s r

index :: (Field a, Eq a, IntegralDomain a, Ord a) => a -> a -> Poly a -> Poly a -> Rational
index a b r s
    | degree r <= degree s = signChanges' a b (sturmChain r s)
    | otherwise            = signChanges' a b [r,s] - index a b s r

windingNumber :: ComplexRational -> ComplexRational -> Poly (Alg QinC) -> Rational
windingNumber z z' p
    = index zero unit (toRealPoly $ realPart gamma) (toRealPoly $ imagPart gamma) / 2
    where
    gamma = compose p alpha
    alpha = fromComplexRational z + iX * fromComplexRational (z' - z)

toRealPoly :: Poly (Alg QinC) -> Poly (Alg QinR)
toRealPoly = fmap toReal

toReal :: Alg QinC -> Alg QinR
toReal (MkAlg (MkIC z p)) = MkAlg (MkIC (realComponent z) p)

-- FIXME: Codeduplikation
windingNumber' :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
windingNumber' z z' p
    = index zero unit (fmap toReal $ realPart gamma) (fmap toReal $ imagPart gamma) / 2
    where
    gamma = compose p alpha
    alpha = fromComplexRational z + iX * fromComplexRational (z' - z)
    toReal (x :+: y) = x

ex :: Poly (Alg QinC)
ex = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3 + fromInteger 4 * Polynomial.constant imagUnit))

ex' :: Poly ComplexRational
ex' = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3))  -- + fromInteger 4 * Polynomial.constant imagUnit))

data Cell
    = Cell0 ComplexRational
    | Cell1 ComplexRational ComplexRational  -- Anfangs- und Endpunkt
    | Cell2 ComplexRational ComplexRational  -- untere linke und obere rechte Ecke
    deriving (Show,Eq)

-- keine spez. Voraussetzungen, ohne Vielfachheit (1/2 auf Ecke)
rootsOnSegment :: ComplexRational -> ComplexRational -> Poly (Alg QinC) -> Rational
rootsOnSegment z0 z1 p = index zero unit (derivative f) f
    where
    gamma = compose p alpha
    alpha = fromComplexRational z0 + iX * fromComplexRational (z1 - z0)
    p1    = toRealPoly (realPart gamma)
    p2    = toRealPoly (imagPart gamma)
    f     = let (u,v,_,_) = gcd p1 p2 in u*p1 + v*p2

-- keine Nullstellen auf Ecken, mit Vielfachheit (1/2 auf Kante)
rootsOnRectangle :: ComplexRational -> ComplexRational -> Poly (Alg QinC) -> Rational
rootsOnRectangle z0 z1 p = sum
    [ windingNumber (realPart z0 + imagUnit * imagPart z0) (realPart z1 + imagUnit * imagPart z0) p
    , windingNumber (realPart z1 + imagUnit * imagPart z0) (realPart z1 + imagUnit * imagPart z1) p
    , windingNumber (realPart z1 + imagUnit * imagPart z1) (realPart z0 + imagUnit * imagPart z1) p
    , windingNumber (realPart z0 + imagUnit * imagPart z1) (realPart z0 + imagUnit * imagPart z0) p
    ]

fromComplexRational :: (Ring a, AllowsRationalEmbedding a, AllowsConjugation a) => ComplexRational -> a
fromComplexRational (u :+: v) = fromRational u + imagUnit * fromRational v

divide :: Poly (Alg QinC) -> Cell -> [(Poly (Alg QinC), Cell)]
divide p (Cell0 z0)    = [(undefined, Cell0 z0)]
divide p (Cell1 z0 z1) = rs
    where
    mid = (z0 + z1) / 2
    n1  = rootsOnSegment z0  mid p
    n2  = rootsOnSegment mid z1  p
    rs  = concat
        [ guard (n1 /= 0) >> return (p, Cell1 z0  mid)
        , guard (n2 /= 0) >> return (p, Cell1 mid z1)
        ]
divide p c@(Cell2 z0 z1)
    | (v:_) <- zeros = (undefined, Cell0 v) : divide (fst $ p `quotRem` (iX - fromComplexRational v)) c
    | otherwise = map (p,) $ concat
        [ guard (n1245 /= 0) >> return (Cell2 u1 u5)
        , guard (n2356 /= 0) >> return (Cell2 u2 u6)
        , guard (n4578 /= 0) >> return (Cell2 u4 u8)
        , guard (n5689 /= 0) >> return (Cell2 u5 u9)
        , guard (n25   /= 0) >> return (Cell1 u2 u5)
        , guard (n56   /= 0) >> return (Cell1 u5 u6)
        , guard (n58   /= 0) >> return (Cell1 u5 u8)
        , guard (n45   /= 0) >> return (Cell1 u4 u5)
        ]
    where
    mid   = (z0 + z1) / 2
    zeros = filter ((== zero) . (flip eval p) . fromComplexRational) [u2, u4, u5, u6, u8]
    p'    = fst $ p `quotRem` (iX - fromComplexRational mid)
    (u1,u2,u3,u4,u5,u6,u7,u8,u9) =
        ( realPart z0  + imagUnit * imagPart z0
        , realPart mid + imagUnit * imagPart z0
        , realPart z1  + imagUnit * imagPart z0
        , realPart z0  + imagUnit * imagPart mid
        , realPart mid + imagUnit * imagPart mid
        , realPart z1  + imagUnit * imagPart mid
        , realPart z0  + imagUnit * imagPart z1
        , realPart mid + imagUnit * imagPart z1
        , realPart z1  + imagUnit * imagPart z1
        )
    n1245 = rootsOnRectangle u1 u5 p - (n12 + n25 + n45 + n14) / 2
    n2356 = rootsOnRectangle u2 u6 p - (n23 + n36 + n56 + n25) / 2
    n4578 = rootsOnRectangle u4 u8 p - (n45 + n58 + n78 + n47) / 2
    n5689 = rootsOnRectangle u5 u9 p - (n56 + n69 + n89 + n58) / 2
    n12   = rootsOnSegment u1 u2 p
    n25   = rootsOnSegment u2 u5 p
    n45   = rootsOnSegment u4 u5 p
    n14   = rootsOnSegment u1 u4 p
    n23   = rootsOnSegment u2 u3 p
    n36   = rootsOnSegment u3 u6 p
    n56   = rootsOnSegment u5 u6 p
    n58   = rootsOnSegment u5 u8 p
    n78   = rootsOnSegment u7 u8 p
    n47   = rootsOnSegment u4 u7 p
    n69   = rootsOnSegment u6 u9 p
    n89   = rootsOnSegment u8 u9 p

-- Für normierte Polynome!
cauchyRadius :: Poly Complex -> R Rational
cauchyRadius (MkPoly zs) = liftM ((1 +) . maximum) (mapM Complex.magnitudeUpperBound zs)
-- erfüllt: |z| <= cauchyRadius f für alle Nullstellen z von f

-- für normierte Polynome (müssen nicht separabel sein)
subdivisions :: Rational -> Poly (Alg QinC) -> [[ComplexRational]]
subdivisions radius p =
    map (map (mid . snd)) $ iterate (concatMap (uncurry divide)) [(p', Cell2 z0 (-z0))]
    where
    z0         = -(radius :+: radius)
    (_,_,p',_) = gcd p (derivative p)
    mid (Cell0 z0)    = z0
    mid (Cell1 z0 z1) = (z0 + z1) / 2
    mid (Cell2 z0 z1) = (z0 + z1) / 2

-- muss normiert, aber nicht unbedingt separabel sein
roots :: Poly (Alg QinC) -> R (Nat -> [Alg QinC])
roots f = return . roots' f' =<< cauchyRadius (fmap (number . unAlg) f)
    where
    (_,_,f',_) = gcd f (derivative f)

-- muss separabel, aber nicht unbed. normiert sein
roots' :: Poly (Alg QinC) -> Rational -> Nat -> [Alg QinC]
roots' f radius n =
    map snd . head $ filter (all (\(b,x) -> b <= 1/fromInteger n)) iters
    where
    iters = subdivisions' radius f

subdivisions' :: Rational -> Poly (Alg QinC) -> [[(Rational, Alg QinC)]]
subdivisions' radius f = go (17/12 * radius) [(f, Cell2 ((-radius) :+: (-radius)) (radius :+: radius))]  -- 17/12 > sqrt 2
    where
    go :: Rational -> [(Poly (Alg QinC), Cell)] -> [[(Rational, Alg QinC)]]
    go r cs = map ((r,) . mid . snd) cs : merge (concatMap (uncurry process) cs)
	where
	process :: Poly (Alg QinC) -> Cell -> [[(Rational, Alg QinC)]]
	process f' (Cell0 z0) = [repeat (0, fromComplexRational z0)]
	process f' c
	    | newtonPrecondition f' (mid c)
	    = tail $ zipWith (\n x -> [(r / 2^(2^n - 1), x)]) [0..] (newton f' (mid c))
	    | otherwise
	    = go (r/2) $ divide f' c
    mid (Cell0 z0)    = fromComplexRational $ z0
    mid (Cell1 z0 z1) = fromComplexRational $ (z0 + z1) / 2
    mid (Cell2 z0 z1) = fromComplexRational $ (z0 + z1) / 2
    merge :: [[a]] -> [[a]]
    merge xss = map head xss : merge (map tail xss)

newton :: Poly (Alg QinC) -> Alg QinC -> [Alg QinC]
newton f = iterate step
    where
    step x = x - eval x f / eval x (derivative f)

-- Thm. 6.9
newtonPrecondition :: Poly (Alg QinC) -> Alg QinC -> Bool
newtonPrecondition f x = and ineqs
    where
    etaSq    = magnSq (eval x f / eval x (derivative f))
    magnSq z = toReal $ z * conjugate z
    ineqs    = zipWith (\c k -> magnSq c * (fromInteger 8)^(2*k-2) * etaSq^(k-1) <= c1sq) (drop 2 cs) [2..]
    cs       = coeffs f
    c1sq     = magnSq (cs !! 1)
