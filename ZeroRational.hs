{-# LANGUAGE PatternGuards, TupleSections #-}
module ZeroRational where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, quotRem, gcd)
import Polynomial
import Ring
import Field
import NumericHelper
import Complex
import Algebraic hiding (eval)
import Polynomial as Poly
import Control.Monad
import Euclidean
import ComplexRational
import Real
import IntegralClosure hiding (eval)
import Debug.Trace
import Data.List hiding (sum)
import System.IO.Unsafe
import Data.IORef
import qualified Data.Map as M

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

toReal (x :+: y) = x

windingNumber :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
windingNumber z z' p
    = index zero unit (fmap toReal $ realPart gamma) (fmap toReal $ imagPart gamma) / 2
    where
    gamma = compose p alpha
    alpha = fromComplexRational z + iX * fromComplexRational (z' - z)
    toReal (x :+: y) = x

ex :: Poly ComplexRational
ex = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3 + fromInteger 4 * Poly.fromBase imagUnit))

ex2 :: Poly ComplexRational
ex2 = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3 + fromInteger 4 * Poly.fromBase imagUnit)) * (iX + negate (fromInteger 9 + fromInteger 8 * Poly.fromBase imagUnit))

ex' :: Poly ComplexRational
ex' = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 4))  -- + fromInteger 4 * Poly.fromBase imagUnit))

ex3 :: Poly Rational
ex3 = iX^2 + fromInteger 1

ex4 :: Poly Rational
ex4 = iX^2 + iX + fromInteger 1

ex5 :: Poly Rational
ex5 = iX^3 - fromInteger 1

ex6 :: Poly Rational
ex6 = Poly.fromBase (1/8)*iX^3 + Poly.fromBase (1/2)*iX

data Cell
    = Cell0 ComplexRational
    | Cell1 ComplexRational ComplexRational  -- Anfangs- und Endpunkt
    | Cell2 ComplexRational ComplexRational  -- untere linke und obere rechte Ecke
    deriving (Show,Eq)

-- keine spez. Voraussetzungen, ohne Vielfachheit (1/2 auf Ecke)
rootsOnSegment :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
rootsOnSegment z0 z1 p = index zero unit (derivative f) f
    where
    gamma = compose p alpha
    alpha = fromComplexRational z0 + iX * fromComplexRational (z1 - z0)
    p1    = fmap toReal $ realPart gamma
    p2    = fmap toReal $ imagPart gamma
    f     = let (u,v,_,_) = gcd p1 p2 in u*p1 + v*p2

-- keine Nullstellen auf Ecken, mit Vielfachheit (1/2 auf Kante)
rootsOnRectangle :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
rootsOnRectangle z0 z1 p = sum
    [ windingNumber (realPart z0 + imagUnit * imagPart z0) (realPart z1 + imagUnit * imagPart z0) p
    , windingNumber (realPart z1 + imagUnit * imagPart z0) (realPart z1 + imagUnit * imagPart z1) p
    , windingNumber (realPart z1 + imagUnit * imagPart z1) (realPart z0 + imagUnit * imagPart z1) p
    , windingNumber (realPart z0 + imagUnit * imagPart z1) (realPart z0 + imagUnit * imagPart z0) p
    ]

fromComplexRational :: (Ring a, AllowsRationalEmbedding a, AllowsConjugation a) => ComplexRational -> a
fromComplexRational (u :+: v) = fromRational u + imagUnit * fromRational v

-- Voraussetzung:
-- Bei 1- und 2-Zellen liegen keine Nullstellen auf den Eckpunkten.
-- Das Polynom ist separabel.
-- Liefert:
-- Liste von Zellen derart, dass:
-- (1) Die Voraussetzung für diese wieder erfüllt sind,
-- (2) jede Zelle in ihrem Inneren mindestens eine Nullstelle enthält und
-- (3) jede Nullstelle des Inneren der Ausgangszelle in einem
--     der Inneren der Zellen liegt.
-- Dabei ist das "Innere" einer 0-Zelle sie selbst, das einer 1- und
-- 2-Zelle sie ohne ihren Rand.
-- Speziell: Liegen auf dem Rand einer 2-Zelle Nullstellen, werden keine
-- Zellen für den Rand erzeugt.
divide :: Poly ComplexRational -> Cell -> [(Poly ComplexRational, Cell)]
divide p (Cell0 z0)
    | eval z0 p == zero = [(p, Cell0 z0)]
    | otherwise      = []
divide p c@(Cell1 z0 z1)
    | eval mid p == zero = (p, Cell0 mid) : divide (fst $ p `quotRem` (iX - fromComplexRational mid)) c
    | otherwise       = rs
    where
    zeros = filter ((== zero) . (flip eval p) . fromComplexRational) [z0, mid, z1]
    mid = (z0 + z1) / fromInteger 2
    n1  = rootsOnSegment z0  mid p
    n2  = rootsOnSegment mid z1  p
    rs  = concat
        [ guard (n1 /= 0) >> return (p, Cell1 z0  mid)
        , guard (n2 /= 0) >> return (p, Cell1 mid z1)
        ]
divide p c@(Cell2 z0 z1)
    | eval mid p == zero = (p, Cell0 mid) : divide (fst $ p `quotRem` (iX - fromComplexRational mid)) c
    -- Hier nicht die 0-Zelle generieren! Denn diese liegen ja auf dem Rand, dafür
    -- dürfen keine Zellen generiert werden.
    | (v:_) <- zeros = divide (fst $ p `quotRem` (iX - fromComplexRational v)) c
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
    mid   = (z0 + z1) / fromInteger 2
    zeros = filter ((== zero) . (flip eval p) . fromComplexRational) [u2, u4, u6, u8]
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
-- XXX Fehler bei Nicht-Normiertheit bringen
cauchyRadius :: NormedPoly ComplexRational -> Rational
cauchyRadius (MkNormedPoly (MkPoly zs)) = ((1 +) . maximum) $ map ComplexRational.magnitudeUpperBound zs
-- erfüllt: |z| <= cauchyRadius f für alle Nullstellen z von f

-- für normierte Polynome (müssen nicht separabel sein)
subdivisions :: Rational -> Poly ComplexRational -> [[ComplexRational]]
subdivisions radius p =
    map (map (mid . snd)) $ iterate (concatMap (uncurry divide)) [(p', Cell2 z0 (negate z0))]
    where
    z0         = negate (radius :+: radius)
    (_,_,p',_) = gcd p (derivative p)
    mid (Cell0 z0)    = z0
    mid (Cell1 z0 z1) = (z0 + z1) / fromInteger 2
    mid (Cell2 z0 z1) = (z0 + z1) / fromInteger 2

{-
-- muss normiert, aber nicht unbedingt separabel sein
roots :: Poly ComplexRational -> R [[ComplexRational]]
roots f = return . roots' f' =<< cauchyRadius f
    where
    (_,_,f',_) = gcd f (derivative f)
-}

-- muss separabel, aber nicht unbed. normiert sein
roots' :: Poly ComplexRational -> Rational -> [[ComplexRational]]
roots' f radius = go 1 iters
    where
    go n (cs:css)
	| all ((<= 1 / fromInteger n) . fst) cs = map snd cs : go (succ n) (cs:css)
	| otherwise                             = go n css
    iters = subdivisions' radius f

-- muss weder normiert noch separabel sein; liefert aber die Nst. ohne Vf.
rootsA :: Poly Rational -> [Alg QinC]
rootsA f = unsafePerformIO $ do
    table <- readIORef rootsMemoTable
    case canonCoeffs f `M.lookup` table of
        Just zs -> return zs
        Nothing -> do
            let zs = rootsA_ f
            writeIORef rootsMemoTable (M.insert (canonCoeffs f) zs table)
            return zs

{-# NOINLINE rootsMemoTable #-}
rootsMemoTable :: IORef (M.Map ([Rational]) [Alg QinC])
rootsMemoTable = unsafePerformIO (newIORef M.empty)

rootsA_ :: Poly Rational -> [Alg QinC]
rootsA_ f = trace ("Suche Nullstellen von (r=" ++ show radius ++ "): " ++ show f) $ flip map [0..n-1] $ \i ->
    let iters' = go i 1 iters in MkAlg $ MkIC (traceEvals ("zero" ++ show i) $ MkComplex (return . (genericIndex iters'))) (fmap F f'')
    where
    (_,_,f',_) = gcd f (derivative f)
    f''        = normalize' f'
    n          = fromIntegral (degree f') :: Int
    radius     = cauchyRadius $ fmap fromRational f''
    iters      = subdivisions' radius $ unNormedPoly $ fmap fromRational f''
    go :: Int -> Integer -> [[(Rational,ComplexRational)]] -> [ComplexRational]
    go i j (cs:css)
	| length cs /= n
	= go i j css
	| fst (cs !! i) <= 1 / fromInteger j
	= snd (cs !! i) : go i (j + 1) (cs:css)
	| otherwise
	= go i j css 

{-
-- muss weder normiert noch separabel sein; liefert die Nst. mit Vf.
rootsA' :: Poly Rational -> [Alg QinC]
rootsA' f = concatMap (\x -> replicate (multiplicity x (fmap fromRational f)) x) (rootsA f)
-}

{-
rootsEx :: Poly Rational -> Int -> [[ComplexRational]] -> [ComplexRational]
rootsEx f n = go 1
    where
    go :: Int -> [[ComplexRational]] -> [ComplexRational]
    go i xss
        | length (head xss) == n
        = flip map [0..n-1] $ \i -> MkAlg $ flip MkIC (fmap F f) $ MkComplex $ \j -> do
            R $ putStrLn $ "AAA:" ++ show i ++ "," ++ show j
            let z = number $ unAlg (xss `genericIndex` ((2*j - fromIntegral i) `max` 2) !! i)
            unComplex z (2*j)
        | otherwise
        = go (i + 1) (tail xss)
-}

-- muss separabel sein!
subdivisions' :: Rational -> Poly (ComplexRational) -> [[(Rational, ComplexRational)]]
subdivisions' radius f = go (17/12 * radius) [(f, Cell2 ((-radius) :+: (-radius)) (radius :+: radius))]  -- 17/12 > sqrt 2
    where
    go :: Rational -> [(Poly (ComplexRational), Cell)] -> [[(Rational, ComplexRational)]]
    go r cs = map ((r,) . mid . snd) cs : merge (map (uncurry process) cs)
	where
	process :: Poly (ComplexRational) -> Cell -> [[(Rational, ComplexRational)]]
	process f' (Cell0 z0) = repeat [(0, fromComplexRational z0)]
	process f' c
            -- XXX: Vorerst Newton ausgestellt.
            -- Grund: Zähler und Nenner riesig! Zieht Berechnungstempo enorm runter.
            -- Beispiel: Zerlegung in irred. Faktoren von X^9 - 243 X^3 mit
            -- Newton: etwas mehr als zwei Minuten, ohne Newton: etwa 17 Sekunden.
            -- Außerdem: XXX Falsch angewendet! Darf nur verwendet werden, wenn
            -- die Zelle so klein ist, dass nicht andere Nullstellen verloren
            -- gehen!
            {-
	    | newtonPrecondition f' (mid c)
	    = tail $ zipWith (\n x -> [(r / 2^(2^n - 1), x)]) [0..] (newton f' (mid c))
	    | otherwise
            -}
	    = go (r/2) $ divideTrace f' c
    mid (Cell0 z0)    = fromComplexRational $ z0
    mid (Cell1 z0 z1) = fromComplexRational $ (z0 + z1) / fromInteger 2
    mid (Cell2 z0 z1) = fromComplexRational $ (z0 + z1) / fromInteger 2
    merge :: [[[a]]] -> [[a]]
    merge xsss = concat (map head xsss) : merge (map tail xsss)
    divideTrace f1 c1 = divide f1 c1 --trace ("divide: " ++ show c1) $ divide f1 c1
-- das "lineare" Newton-Verfahren (Thm. 6.7) vielleicht auch einbauen!

newton :: Poly (ComplexRational) -> ComplexRational -> [ComplexRational]
newton f = iterate step
    where
    step x = x - eval x f / eval x (derivative f)

-- Thm. 6.9
-- Vor.: derivative f x != 0, f x != 0.
-- Die Voraussetzungen zeigen dann auch, dass f genau eine Nullstelle im
-- offenen Ball mit Radius 2*eta um x hat.
newtonPrecondition :: Poly ComplexRational -> ComplexRational -> Bool
newtonPrecondition f x = eval x f /= zero && eval x (derivative f) /= zero && and ineqs
    where
    etaSq    = magnSq (eval x f / eval x (derivative f))
    magnSq z = toReal $ z * conjugate z
    ineqs    = zipWith (\c k -> magnSq c * (fromInteger 8)^(2*k-2) * etaSq^(k-1) <= c1sq) (drop 2 cs) [2..]
    -- XXX: okay, dass coeffs Nuller liefert?
    cs       = unsafeCoeffs $ compose f (iX + fromComplexRational x)
    c1sq     = magnSq (cs !! 1)
