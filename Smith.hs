-- | Dieses Modul erlaubt es, eine gegebene Matrix über einem euklidischen Ring
-- auf /Smithsche Normalform/ zu bringen.
--
-- Dies verwenden wir unter anderem, um Minimalpolynome von Matrizen
-- auszurechnen.
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Smith
    ( diagonalForm, elementaryDivisors
    , HaveAnnihilatingPolynomial(..)
    , determinant
    , charPoly, minPoly, lambdaMatrix
    ) where

import Matrix as M
import Data.Array
import Prelude hiding (gcd, (!!), (+), (*), (-), (/), negate, quotRem)
import qualified Prelude as P
import Polynomial as Poly
import Ring
import Field
import Euclidean
import TypeLevelNat
import Testing

-- | Führt eine Transformation derart aus, dass das /(0,j)/-Element null wird;
-- dazu wird der größte gemeinsame Teiler vom /(0,0)/- und /(0,j)/-Element
-- genutzt. Die zugehörige Transformationsmatrix hat stets Determinante /1/.
makeZeroInFirstRow
    :: (ReifyNat n, ReifyNat m, EuclideanRing a, Eq a, TestableAssociatedness a)
    => Nat -> Matrix (S n) m a -> Matrix (S n) m a
makeZeroInFirstRow j mtx@(MkMatrix arr) = MkMatrix (arr // updates) `asTypeOf` mtx
    where
    (u,v,s,t) = gcd' (arr ! (0,0)) (arr ! (0,j))
    updates   = do
	i <- [0..n]
	let (x,y) = (arr ! (i,0), arr ! (i,j))
	[ ((i,0), u*x + v*y), ((i,j), s*y - t*x) ]
    ((0,0),(n,_)) = bounds arr
-- Korrektheitsbeweis für den Fall, dass y0 := arr ! (0,j) nicht null ist:
-- a) Transformation hat Determinante 1: (us + vt) d = usd - vtd = ux0 + vy0 = d
-- b) Die versprochene null wird erreicht:
--    (s y0 - t x0) d = x0 y0 - y0 x0 = 0.
-- Sonst gilt (u,v,s,t) = (1,0,1,0), daher findet keine wirkliche
-- Transformation statt.

-- | Führt eine Transformation derart aus, dass das /(j,0)/-Element null wird;
-- dazu wird der größte gemeinsame Teiler vom /(0,0)/- und /(j,0)/-Element
-- genutzt. Die zugehörige Transformationsmatrix hat stets Determinante /1/.
makeZeroInFirstCol
    :: (ReifyNat n, ReifyNat m, EuclideanRing a, Eq a, TestableAssociatedness a)
    => Nat -> Matrix n (S m) a -> Matrix n (S m) a
makeZeroInFirstCol i = transpose . makeZeroInFirstRow i . transpose

-- | Bringt eine gegebene Matrix auf (rechteckige) Diagonalform.
-- Das ist noch nicht die Smithsche Normalform; die zusätzliche Bedingung,
-- dass die aufeinanderfolgende Hauptdiagonalelemente einander teilen,
-- muss hier nicht unbedingt erfüllt sein.
--
-- Die verwendeten Transformationen haben stets Determinante /1/.
diagonalForm :: (ReifyNat n, ReifyNat m, EuclideanRing a, Eq a, TestableAssociatedness a) => Matrix n m a -> [a]
diagonalForm mtx
    | numRows mtx == 0 || numCols mtx == 0
    = []
    | not (null badCols)
    = withNontrivialRows mtx $ diagonalForm . makeZeroInFirstRow (head badCols)
    | not (null badRows)
    = withNontrivialCols mtx $ diagonalForm . makeZeroInFirstCol (head badRows)
    | otherwise
    = mtx !! (0,0) : withNontrivialRowsCols mtx (diagonalForm . deleteRow 0 . deleteColumn 0)
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= zero]
    badRows = [i | i <- [1..numRows mtx - 1], mtx !! (i,0) /= zero]
-- Das Verfahren terminiert, da wir die aufsteigende Kettenbedingung für
-- Hauptideale voraussetzen und in 'makeZeroInFirstRow' darauf achten,
-- im trivialem Fall vorliegender Assoziiertheit die richtige (nichts
-- zerstörende) Transformation durchführen -- darum kümmert sich 'Euclidean.gcd\''.

-- | Liefert die Elementarteiler einer Matrix.
-- Diese werden nicht auf irgendeine Art und Weise normiert (welche sollte
-- das in einem beliebigen euklidischen Ring auch sein?), sollten also
-- nur bis auf Assoziiertheit verstanden werden.
elementaryDivisors
    :: (ReifyNat n, ReifyNat m, EuclideanRing a, Eq a, TestableAssociatedness a)
    => Matrix n m a -> [a]
elementaryDivisors = divisors . diagonalForm

-- | Formt eine gegebene Liste von Ringelementen (die wir uns als
-- Hauptdiagonalelemente einer rechteckigen Diagonalmatrix vorstellen) so um,
-- dass aufeinanderfolgende Elemente einander teilen.
divisors :: (EuclideanRing a, Eq a, TestableAssociatedness a) => [a] -> [a]
divisors [] = []
divisors as = go (length as - 1) as
    where
    go i bs
	| i == 0    = head bs : divisors (tail bs)
	| otherwise = go (i-1) $ d : splice (i-1) p (tail bs)
	where
	(u,v,s,t) = gcd (head bs) (bs P.!! i)
	d         = u*head bs + v*bs P.!! i
	p         = d*s*t

-- | /splice i x ys/ ersetzt in /ys/ das Element an einer Stelle /i ≥ 0/ durch /x/.
-- Dazu muss /ys/ mindestens /i+1/ Elemente enthalten.
splice :: Int -> a -> [a] -> [a]
splice 0 x (_:ys) = x : ys
splice n x (y:ys) = y : splice (n-1) x ys
splice _ _ _      = error "splice"  -- sollte nicht eintreten

-- | Klasse für Ringe, die es unterstützen, zu jeder gegebenen quadratischen
-- Matrix /A/ ein normiertes Polynom /f/ zu finden, welches die Matrix
-- annihiliert, also /f(A) = 0/ erfüllt.
--
-- Wegen (der allgemeinen Form des) Satzes von Cayley--Hamilton sind das
-- natürlich einfach alle Ringe, das charakteristische Polynom einer Matrix
-- ist stets ein normiertes (die richtige Vorzeichendefinition vorausgesetzt)
-- annihilierendes Polynom.
-- 
-- Allerdings ist die Berechnung in allgemeinen Ringen nur naiv über die
-- Leibnizformel durchführbar. Daher soll diese Klasse Ringe auszeichnen,
-- die über eine effizientere Möglichkeit dazu verfügen.
--
-- Insbesondere kann man über Körpern auch das Minimalpolynom nehmen,
-- welches weitere Anwendungen durch seinen geringeren Grad effizienter
-- werden lässt.
class (Ring a) => HaveAnnihilatingPolynomial a where
    -- | Bestimmt ein normiertes Polynom, welches die gegebene Matrix
    -- annihiliert. Das Nullpolynom zählt nicht als normiert.
    annihilatingPolynomial :: (ReifyNat n) => SqMatrix n a -> NormedPoly a

-- XXX: QuickCheck für annihilatingPolynomial!

{-
 - XXX: noch verbessern: Sollte für jeden IntBer. funktionieren. Hat mit ER nichts zu tun!
instance (EuclideanRing a, Integral a, IntegralDomain a, TestableAssociatedness a, Eq a) => HaveAnnihilatingPolynomial (ER a) where
    annihilatingPolynomial = fmap unsafeFromRatio . charPoly . fmap toRatio
	where
	toRatio = (% unit)
	unsafeFromRatio z =
	    let (p,q) = (numerator z, denominator z)
		(r,s) = p `quotRem` q
	    in  if s == 0 then r else error $ "unsafeFromRatio"
-}

-- Über Körpern können wir das Minimalpolynom verwenden.
instance (Field a, IntegralDomain a, Eq a) => HaveAnnihilatingPolynomial (F a) where
    annihilatingPolynomial = minPoly

props_annihilatingPolynomial
    :: (HaveAnnihilatingPolynomial a, Eq a, Show a, Arbitrary a)
    => Proxy a -> [Property]
props_annihilatingPolynomial proxy = (:[]) $ forAll (elements [0..maxDim]) $ \n ->
    reflectNat n $ \n' ->
        forAll arbitrary $ \mtx ->
            let _ = numRows' mtx `asTypeOf` numCols' mtx `asTypeOf` n'
                _ = (undefined :: Matrix n m a -> Proxy a) mtx `asTypeOf` proxy
                MkNormedPoly p = annihilatingPolynomial mtx
            in  leadingCoeff p == unit && eval mtx (fmap M.fromBase p) == zero
    where maxDim = 4

-- | Berechnet die Determinante, indem Determinante-/1/-Transformationen
-- verwendet werden, um die gegebene Matrix auf Dreiecksform zu bringen.
determinant :: (ReifyNat n, EuclideanRing a, Eq a, TestableAssociatedness a) => SqMatrix n a -> a
determinant mtx
    | numRows mtx == 0 = unit
    | null badCols     = (mtx !! (0,0)) * restDet
    | otherwise        =
        withNontrivialRowsCols mtx (flip withSquare determinant . makeZeroInFirstRow (head badCols))
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= zero]
    restDet = withNontrivialRowsCols mtx (flip withSquare determinant . deleteRow 0 . deleteColumn 0)

-- | Berechnet das charakteristische Polynom (normiert) einer gegebenen Matrix.
-- Die Körper-Voraussetzung an den Ring stellen wir, um die effizienten
-- Smith-Umformungen nutzen zu können. Erfüllt folgende Spezifikation:
--
-- > determinant = naiveDeterminant . lambdaMatrix
charPoly :: (ReifyNat n, Field a, IntegralDomain a, Eq a) => SqMatrix n a -> NormedPoly a
charPoly = mkNormedPoly . unER . determinant . fmap ER . lambdaMatrix

-- | Berechnet das Minimalpolynom (normiert) einer gegebenen Matrix /A/
-- über die Smithsche Normalform von /lambda 1 - A/. Das Minimalpolynom
-- der eindeutigen /0x0/-Matrix ist das Einspolynom.
minPoly :: (ReifyNat n, Field a, IntegralDomain a, Eq a) => SqMatrix n a -> NormedPoly a
minPoly = normalize' . last' . map unER . elementaryDivisors . fmap ER . lambdaMatrix
    where
    last' xs = if null xs then unit else last xs
    -- Ausnahme für die 0x0-Matrix

-- | Liefert zu einer gegebenen Matrix /A/ die für die Bestimmung von
-- annihilierenden Polynomen wichtige Matrix /lambda 1 - A/ (mit Einträgen
-- im entsprechenden Polynomring).
lambdaMatrix :: (ReifyNat n, Ring a) => SqMatrix n a -> SqMatrix n (Poly a)
lambdaMatrix (MkMatrix arr) = MkMatrix $
    accum (+) (fmap (negate . Poly.fromBase) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]

props_Smith :: [Property]
props_Smith = props_annihilatingPolynomial (undefined :: Proxy (F Rational))
