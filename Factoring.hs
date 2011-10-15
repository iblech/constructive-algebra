-- | Dieses Modul stellt Funktionen zur Faktorisierung von rationalen Polynomen
-- zur Verfügung; das sind hauptsächlich 'isIrreducible' und
-- 'irreducibleFactors'.
{-# LANGUAGE PatternGuards #-}
module Factoring where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import qualified Prelude as P
import Ring
import Polynomial as Poly
import ZeroRational
import Data.Maybe
import Data.List hiding (product)
import Euclidean
import Algebraic hiding (eval)
import qualified Algebraic as A
import Control.Monad
import Complex
import IntegralClosure hiding (eval)
import Field
import Debug.Trace
import Data.Ratio
import Testing

-- | Entscheidet zu einem gegebenen Polynom (welches mindestens Grad 1 haben,
-- sonst aber keine Zusatzvoraussetzungen erfüllen muss), ob es irreduzibel
-- über den rationalen Zahlen ist, und extrahiert im reduziblen Fall
-- zwei Faktoren.
isIrreducible
    :: Poly Rational  -- ^ /f/
    -> Maybe (Poly Rational,Poly Rational)
                      -- ^ entweder Nothing (irreduzibel)
                      -- oder /Just (g,h)/ mit /f = gh/ und
                      -- /deg f, deg g >= 1/.
isIrreducible f = trace ("isIrreducible: " ++ show f) $ isIrreducible' f

isIrreducible' :: Poly Rational -> Maybe (Poly Rational,Poly Rational)
isIrreducible' f
    -- Triviale Fälle
    | n <  1 = error "isIrreducible: Polynom konstant"
    | n == 1 = Nothing

    -- Hat f einen nichttrivialen Faktor mit seiner Ableitung gemein?
    | degree d > 0 = Just (s,d)  -- den kleineren Faktor vorne

    -- Wir normieren f, falls nötig. Denn dann können wir uns im Hauptteil des
    -- Verfahrens darauf beschränken, von gewissen algebraischen Zahlen zu
    -- prüfen, ob sie ganzzahlig sind.
    | leadingCoeff f /= 1 = do
        (g,h) <- isIrreducible (normalize f)
        return (g, leadingCoeff f .* h)

    -- Abkürzung eines häufigen Falls: Können wir X ausklammern?
    | eval0 f == 0 = Just (iX,fst (f `quotRem` iX))

    -- Ist f von der Form g(X^n) für ein n >= 2? Dann versuchen wir zunächst,
    -- g zu zerlegen. Vielleicht haben wir Glück, denn aus einer Zerlegung von
    -- g folgt natürlich auch eine von f -- da die Umkehrung aber nicht gelten
    -- muss, müssen wir, falls g irreduzibel ist, trotzdem noch die eigentliche
    -- Prüfung durchführen.
    | Just (g,h) <- isComposedPoly f, Just (p,q) <- isIrreducible g
    = Just (p `compose` h, q `compose` h)

    -- Das eigentliche Verfahren: Die Nullstellen finden (hier können wir
    -- bereits davon ausgehen, dass f normiert und separabel ist) und Auswahlen
    -- der Nullstellen betrachten.
    | otherwise
    = listToMaybe $ do
        let contentInv = 1 / Poly.content f
        -- alle Auswahlen von Nullstellen; wobei wir kleine Auswahlen
        -- zuerst überprüfen wollen.
	xs <- sortBy (\xs ys -> length xs `compare` length ys) $ subsequences zeros
        -- ...und triviale bzw. unnötige gar nicht.
	guard $ not $ null xs
	guard $ length xs <= fromIntegral n `div` 2

	trace ("BEARBEITE: " ++ show (map unsafeApprox xs)) $ do
	let p = product $ map ((iX -) . Poly.fromBase) xs
	Just p' <- [isApproxIntegerPoly (fromRational contentInv .* p)]
        -- Da wir nicht isIntegerPoly, sondern nur isApproxIntegerPoly
        -- verwendet haben, kann es sein, dass contentInv * p doch gar
        -- kein ganzzahliges Polynom ist. Daher machen wir mithilfe der
        -- Polynomdivision...
	let (q,r) = f `quotRem` fmap fromInteger p'
        -- ...noch die Probe:
        guard $ r == zero
	return (fmap fromInteger p', q)
    where
    zeros     = roots f
    n         = degree f
    (u,v,s,_) = gcd f (derivative f)
    d         = u*f + v*derivative f

-- | Prüft, ob ein übergebenes nichtkonstantes Polynom /f/ von der Form
-- /f = g(X^n)/ für ein /n >= 2/ ist. Wenn nein, wird /Nothing/ zurückgegeben;
-- sonst /Just (g, iX^n)/.
isComposedPoly :: Poly Rational -> Maybe (Poly Rational, Poly Rational)
isComposedPoly f 
    | length as < 2 = error "isComposedPoly: Polynom konstant"
    | null cands = Nothing
    | otherwise  =
        let n = last cands
            g = MkPoly [ as !! (n*i) | i <- [0..(length as - 1) `div` n] ]
        in  Just (g, iX^fromIntegral n)
    where
    cands    = [ i | i <- [2..length as],     all ((== 0) . (`mod` i)) usedExps ]
    usedExps = [ i | i <- [0..length as - 1], as !! i /= 0 ]
    as       = canonCoeffs f

props_isComposedPoly :: [Property]
props_isComposedPoly = (:[]) $ forAll arbitrary $ \f -> forAll (elements [0..30]) $ \n ->
    degree f >= 1 ==>
    let f' = f `compose` (iX^n)
    in  if n >= 2 then isComposedPoly f' == Just (f,iX^n) else isComposedPoly f' == Nothing

-- | Bestimmt die irreduziblen Faktoren eines nichtkonstanten Polynoms.
-- Es gilt folgende Spezifikation:
--
-- > product fs == f && all (isNothing . isIrreducible) fs
-- >     where fs = irreducibleFactors f
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
    mapFirst g (x:xs) = g x:xs
    mapFirst _ _      = error "irreducibleFactors.mapFirst"  -- kann nicht eintreten

props_irreducibleFactors :: [Property]
props_irreducibleFactors = (:[]) $
    forAll (elements [1..5]) $ \n ->
    forAll (replicateM n arbitrary) $ \fs ->
    all ((>= 1) . degree) fs ==>
    let f   = product fs
        fs' = irreducibleFactors f
    in  all (isNothing . isIrreducible) fs' && product fs' == f

-- | Bestimmt das Minimalpolynom einer algebraischen Zahl.
minimalPolynomial :: Alg QinC -> Poly Rational
minimalPolynomial z = head $ filter (\p -> zero == A.eval z p) factors
    where
    f         = unNormedPoly . polynomial . unAlg $ z
    (_,_,s,_) = gcd f (derivative f)
    factors   = fmap normalize $ irreducibleFactors $ fmap unF s

-- | Jedes Element vom Typ /Alg QinC/ führt ja eine seine Algebraizität bezeugende
-- Polynomgleichung mit.
simplify' :: Alg QinC -> Alg QinC
simplify' z = MkAlg $ MkIC (number . unAlg $ z) (mkNormedPoly $ fmap F $ minimalPolynomial z)
