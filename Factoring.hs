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
import System.IO.Unsafe
import Cyclotomic

-- | Berechnet den Inhalt eines Polynoms.
content :: Poly Rational -> Rational
content f
    | abs a == 1 = fromInteger . abs $ foldl1' P.gcd $ map numerator as 
    | abs a /= 1 = content (abs a .* f) / abs a
    where
    as = canonCoeffs f
    a  = fromInteger . foldl1' P.lcm $ map denominator as

-- | Entscheidet zu einem gegebenen Polynom (welches mindestens Grad 1,
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

isIrreducible' f
    -- Triviale Fälle
    | n <  1 = error "isIrreducible"
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

    -- Ist f ein Kreisteilungspolynom, oder ein anderes bekanntes irreduzibles
    -- Polynom? Das ist natürlich eigentlich "cheaten", aber so sehen können
    -- wir ein paar mehr Galoisgruppenbeispiele rechnen.
    | f `elem` (relevantCyclotomics ++ knownIrreds)
    = Nothing

    -- Oder ist f ein Vielfaches eines Kreisteilungspolynoms?
    | (g,(h,_)):_ <- cyclotomicResiduals
    = Just (g,h)

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
        let contentInv = 1 / content f
        trace (show contentInv) $do
        -- alle Auswahlen von Nullstellen;
        -- wir wollen kleinere Auswahlen zuerst überprüfen...
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
    aN        = leadingCoeff f
    (u,v,s,t) = gcd f (derivative f)
    d         = u*f + v*derivative f
    -- Liste relevanter Kreisteilungspolynome. Da der Grad der
    -- Kreisteilungspolynome nicht monoton steigt, und ich zu faul war, mir
    -- genauere Gedanken zu machen, nutzen wir hier eine einfache Heuristik,
    -- um Relevanz zu entscheiden. (Diese Prüfungen dienen eh nur der Effizienz
    -- und ändern nicht die Korrektheit des Verfahrens.)
    relevantCyclotomics = []
        --takeWhile (\p -> degree p <= 3 * degree f) $ map (fmap fromInteger) cyclotomicPolynomials
    -- Für jedes als relevant empfundene Kreisteilungspolynom g, welches auch
    -- ein Teiler von f ist, also für das es ein h mit f = gh gibt, schreiben
    -- wir das h in die Liste 'cyclotomicResiduals'.
    cyclotomicResiduals =
        filter ((== zero) . snd . snd) $ map (\p -> (p, f `quotRem` p)) relevantCyclotomics

-- | Liste bekannter irreduzibler Polynome.
knownIrreds :: [Poly Rational]
knownIrreds = []

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
    as       = canonCoeffs f

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
    f         = unNormedPoly . polynomial . unAlg $ z
    z'        = number . unAlg $ z
    (u,v,s,t) = gcd f (derivative f)
    -- Normierung schon hier, damit nicht sehr kleine Konstanten viele
    -- Iterationen unten erzwingen
    factors   = map normalize $ irreducibleFactors $ fmap unF s
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
    f         = unNormedPoly . polynomial . unAlg $ z
    (u,v,s,t) = gcd f (derivative f)
    factors   = fmap normalize $ irreducibleFactors $ fmap unF s

-- XXX: besserer name!
simplify' :: Alg QinC -> Alg QinC
simplify' z = MkAlg $ MkIC (number . unAlg $ z) (mkNormedPoly $ fmap F $ minimalPolynomial z)
