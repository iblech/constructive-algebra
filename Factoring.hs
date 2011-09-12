{-# LANGUAGE PatternGuards #-}
module Factoring where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Polynomial
import ZeroRational
import Data.Maybe
import Data.List hiding (product)
import Euclidean
import Algebraic hiding (eval)
import qualified Algebraic as A
import Control.Monad
import Complex hiding (constant)
import IntegralClosure hiding (eval)
import Field
import Debug.Trace
import Data.Ratio
import System.IO.Unsafe
import Cyclotomic

-- soll mind. Grad 1 haben
isIrreducible :: Poly Rational -> Maybe (Poly Rational,Poly Rational)
isIrreducible f
    | n <  1 = error "isIrreducible"
    | n == 1 = Nothing
    | degree d > 0 = Just (s,d)  -- den kleineren Faktor vorne
    | leadingCoeff f /= 1 = do
        (g,h) <- isIrreducible (norm f)
        return (g, leadingCoeff f .* h)
    | eval0 f == 0 = Just (iX,fst (f `quotRem` iX))
    | f `elem` (relevantCyclotomics ++ knownIrreds)
    = Nothing
    | (g,(h,_)):_ <- cyclotomicResiduals
    = Just (g,h)
    | Just (g,h) <- isComposedPoly f, Just (p,q) <- isIrreducible g
    = Just (p `compose` h, q `compose` h)
    | otherwise
    = listToMaybe $ do
	xs <- sortBy (\xs ys -> length xs `compare` length ys) $ subsequences zeros
	guard $ not $ null xs
	guard $ length xs <= fromIntegral n `div` 2
	trace ("BEARBEITE: " ++ show (map approx xs)) $ do
	let p = product $ map ((iX -) . constant) xs
	Just p' <- [isGoodPoly p]
	--trace ("isgood is: " ++ show (map approx xs)) $ do
	let (q,r) = f `quotRem` p'
        -- für isApproxIntegerPoly
        guard $ r == zero
	return (p',q)
    where
    --zeros = zipWith (\z i -> traceEvals' ("root" ++ show i) z) (rootsA f) [0..]
    zeros = rootsA f
    traceEvals' str (MkAlg (MkIC z p)) = MkAlg (MkIC (traceEvals str z) p)
    n         = degree f
    aN        = leadingCoeff f
    (u,v,s,t) = gcd f (derivative f)
    d         = u*f + v*derivative f
    isGoodPoly
        | all isInteger' (coeffs f) && leadingCoeff f == 1
        = fmap (fmap fromInteger) . isApproxIntegerPoly
        | otherwise
        = isRationalPoly
    isInteger' q = numerator q `mod` denominator q == 0
    -- die 3 ist Heuristik
    relevantCyclotomics =
        takeWhile (\p -> degree p <= 3 * degree f) $ map (fmap fromInteger) cyclotomicPolynomials
    cyclotomicResiduals =
        filter ((== zero) . snd . snd) $ map (\p -> (p, f `quotRem` p)) relevantCyclotomics

knownIrreds :: [Poly Rational]
knownIrreds = [iX^6 + fromInteger 108]

-- isComposedPoly f = Just (g,h) ==> g . h = f, isComposedPoly g = Nothing.
isComposedPoly :: Poly Rational -> Maybe (Poly Rational, Poly Rational)
isComposedPoly f 
    | null cands = Nothing
    | otherwise  =
        let n = last cands
            g = MkPoly [ as !! (n*i) | i <- [0..(length as - 1) `div` n] ]
        in  Just (g, iX^fromIntegral n)
    where
    cands    = [ i | i <- [2..length as],     all ((== 0) . (`mod` i)) usedExps ]
    usedExps = [ i | i <- [0..length as - 1], as !! i /= 0 ]
    as       = coeffs f

-- soll mind. Grad 1 haben
irreducibleFactors :: Poly Rational -> [Poly Rational]
irreducibleFactors f
    | Nothing <- test
    = [f]
    | Just (p,q) <- test
    -- = irreducibleFactors p ++ irreducibleFactors q
    = let ps = irreducibleFactors p in ps ++ go p ps q
    where
    test = isIrreducible f
    -- auf gut Glück denselben Faktor nochmal versuchen
    go p ps q =
        let (r,s) = q `quotRem` p
        in  if s == zero
                then (mapFirst ((leadingCoeff q / leadingCoeff p) .*) ps) ++ go p ps r
                else if degree q < 1 then [] else irreducibleFactors q
    mapFirst f (x:xs) = f x:xs

-- sollte dann in allen Vorkommen von z das MP liefern (überschreiben)
{- Spezifikation:
minimalPolynomial :: Alg QinC -> Poly Rational
minimalPolynomial z = go (fmap unF . polynomial . unAlg $ z)
    where
    go f
	| degree f <= 1 = norm f
	| otherwise     = case isIrreducible f of
	    Nothing    -> norm f
	    Just (p,q) -> if eval z (fmap fromRational p) == zero then go p else go q
funktioniert auch, ist aber sehr langsam in der Nullprüfung
(Ganzheitsgleichungen haben hohen Grad...)
-}

-- langsamer als minimalPolynomial
minimalPolynomial' :: Alg QinC -> Poly Rational
minimalPolynomial' z = unsafePerformIO . runR $ go 1
    where
    f         = polynomial . unAlg $ z
    z'        = number     . unAlg $ z
    (u,v,s,t) = gcd f (derivative f)
    -- Normierung schon hier, damit nicht sehr kleine Konstanten viele
    -- Iterationen unten erzwingen
    factors   = map norm $ irreducibleFactors $ fmap unF s
    isApproxZero n g = magnitudeZeroTestR n $ eval z' (fmap fromRational g)
    go n = do
        R $ putStrLn $ "go " ++ show n
        candidates <- filterM (isApproxZero n) factors
        R $ putStrLn $ "candidates: " ++ show candidates
        if length candidates == 1
            then return $ head candidates
            else go (2*n)

minimalPolynomial :: Alg QinC -> Poly Rational
minimalPolynomial z = head $ filter (\p -> zero == A.eval z p) factors
    where
    f         = polynomial . unAlg $ z
    (u,v,s,t) = gcd f (derivative f)
    factors   = fmap norm $ irreducibleFactors $ fmap unF s

-- XXX: besserer name!
simplify' :: Alg QinC -> Alg QinC
simplify' z = MkAlg $ MkIC (number . unAlg $ z) (fmap F $ minimalPolynomial z)
