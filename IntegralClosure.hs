-- | Dieses Modul stellt Ganzheitsringe zur Verfügung:
-- Zu einem 'RingMorphism' /m/ ist 'IC' /m/ der Ring derjenigen Elemente
-- von 'Codomain' /m/, welche über 'Domain'  /m/ ganz sind, also eine
-- normierte Polynomgleichung mit Koeffizienten aus 'Domain' /m/ erfüllen.
{-# LANGUAGE FlexibleContexts, UndecidableInstances, FlexibleInstances #-}
module IntegralClosure
    ( -- * Typen
      IC(..)
      -- * Funktionen
    , IntegralClosure.fromBase
    , IntegralClosure.eval
      -- * Hilfsfunktionen
    , sumAnnihilator, prodAnnihilator, evalAnnihilator, verifyPolynomial
      -- * Beispiele
    , goldenRatio, sqrt2
      -- * QuickCheck-Eigenschaften
    , props_IntegralClosure
    ) where

import Debug.Trace

import Prelude hiding (fromInteger, fromRational, (+), (*), (-), (^), negate)
import Complex hiding (goldenRatio, sqrt2)
import qualified Complex as C
import NumericHelper
import qualified Polynomial as Poly
import Polynomial as Poly
import Matrix hiding ((!!))
import Ring
import RingMorphism
import Field
import Smith
import ComplexRational
import Proxy
import Testing

import Data.Array

-- | Der Typ der Elemente des Ganzheitsrings des Ringmorphismus /m/.
-- Ein solches ist gegeben durch eine Zahl des Zielrings und einem normierten
-- Polynom mit Koeffizienten des Quellrings des Morphismus, welches die Zahl
-- als Nullstelle besitzt.
--
-- Nun ist die zu einem Element gehörige Ganzheitsgleichung natürlich nicht
-- eindeutig bestimmt, daher ist die hier gewählte Darstellung nicht eindeutig.
-- Man könnte sogar argumentieren, dass die Implementierung hier die
-- mathematische Definition nicht treu abbildet. Denn diese sagt ja nur, dass
-- es zu Elementen des Ganzheitsrings jeweils eine Ganzheitsgleichung /gibt/,
-- nicht aber, dass Elemente des Ganzheitsrings durch Paare von Zahlen und
-- zugehörigen Ganzheitsgleichungen repräsentiert werden.
--
-- (Eine mögliche Alternativdefinition wäre, den Typ von 'polynomial'
-- monadisch zu wählen, damit in der Bestimmung der zugehörigen
-- Ganzheitsgleichung beliebige Nebeneffekte möglich sind.)
data (RingMorphism m) => IC m = MkIC
    { number     :: Codomain m
        -- ^ Element des Zielrings
    , polynomial :: Poly (Domain m)
        -- ^ eine die Zugehörigkeit zum Ganzheitsring beweisende Ganzheitsgleichung
    }

-- | Liftet Elemente /x/ des Quellrings in den Ganzheitsring,
-- mit der trivialen Ganzheitsgleichung /X - x/ als Zeuge der Ganzheit.
fromBase :: (RingMorphism m) => Domain m -> IC m
fromBase x = r
    where
    r    = MkIC (mor' x) (iX - Poly.fromBase x)
    mor' = mor ((undefined :: IC m -> Proxy m) r)


instance (RingMorphism m, HaveAnnihilatingPolynomial (Domain m)) => Ring (IC m) where
    MkIC x p + MkIC x' p' = MkIC (x + x') (sumAnnihilator p p')
    MkIC x p * MkIC x' p'
        | couldBeNotX p  == False = zero
        | couldBeNotX p' == False = zero
        | otherwise               = MkIC (x * x') (prodAnnihilator p p')

    negate (MkIC x p) = MkIC (negate x) (MkPoly as)
	where
	as = reverse $ zipWith (*) (reverse $ unsafeCoeffs p) (cycle [unit,negate unit])

    fromInteger i = MkIC (fromInteger i) (iX - fromInteger i)

    zero = fromInteger zero
    unit = fromInteger unit

instance (RingMorphism m, IntegralDomain (Codomain m), HaveAnnihilatingPolynomial (Domain m)) =>
    IntegralDomain (IC m)

instance (RingMorphism m, HaveAnnihilatingPolynomial (Domain m), AllowsRationalEmbedding (Domain m)) =>
    AllowsRationalEmbedding (IC m) where
    fromRational r = z
        where
        mor' = mor ((undefined :: IC m -> Proxy m) z)
        z    = MkIC (mor' (fromRational r)) (iX - fromRational r)

instance (RingMorphism m, ApproxFloating (Codomain m)) => ApproxFloating (IC m) where
    approx = approx . number


-- | Bestimmt zu zwei gegebenen Ganzheitsgleichungen /f/ (eines Elements /x/)
-- und /g/ (eines Elements /y/) eine, welche die Summe /x + y/ als Nullstelle
-- besitzt.
--
-- Dafür wird die /R/-Algebra /R[x,y]/ als /R/-Modul betrachtet, von dem das
-- Erzeugendensystem /x^i y^j/ bekannt ist, wobei /i/ und /j/ zwischen /0/
-- (eingeschlossen) und dem Grad von /f/ bzw. /g/ (ausgeschlossen) laufen.
--
-- Die Abbildung /Multiplikation mit (x+y)/ besitzt dann ein annihilierendes
-- Polynom; dieses berechnen wir.
sumAnnihilator :: (Ring a, HaveAnnihilatingPolynomial a) => Poly a -> Poly a -> Poly a
sumAnnihilator f g =
    flip fromArray' annihilatingPolynomial $
        listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    elems = [arr ij kl | ij <- indices, kl <- indices ]
    arr (i,j) (k,l) = arr1 (i,j) (k,l) + arr2 (i,j) (k,l)
    arr1 (i,j) (k,l)
	| i < n - 1 = if (k,l) == (i+1,j) then unit else zero
	| otherwise = if l == j then negate (xs !! k) else zero
    arr2 (i,j) (k,l)
	| j < m - 1 = if (k,l) == (i,j+1) then unit else zero
	| otherwise = if k == i then negate (ys !! l) else zero
    indices = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (unsafeCoeffs f, unsafeCoeffs g)

-- sollte nicht mit 'stdArgs' getestet werden, sondern mit einer erheblichen
-- Beschränkung, wie beispielsweise:
--
-- > mapM_ (Test.QuickCheck.quickCheckWith stdArgs{maxSize=4}) $
--       props_sumAnnihilator (undefined :: Proxy (F Rational))
props_sumAnnihilator :: (HaveAnnihilatingPolynomial a, Show a, Eq a, Arbitrary a) => Proxy a -> [Property]
props_sumAnnihilator proxy = (:[]) $ forAll arbitrary $ \(NormedPoly f, NormedPoly g) ->
    let h  = sumAnnihilator f g
        -- Hier evaluieren wir per Hand h(X+Y) im Ring (R[Y]/(g))[X]/(f)...
        h' = compose (fmap Poly.fromBase h) (Poly.fromBase iX + iX)
        r  = snd $ normedQuotRem h' (fmap Poly.fromBase f)
        -- ...null müsste herauskommen:
    in  leadingCoeff h == unit `asTypeOf` unProxy proxy &&
        all ((== zero) . snd . (`normedQuotRem` g)) (canonCoeffs r)

-- | Bestimmt zu zwei gegebenen Ganzheitsgleichungen /f/ (eines Elements /x/)
-- und /g/ (eines Elements /y/) eine, welche das Produkt /x y/ als Nullstelle
-- besitzt. Das Vorgehen ist das gleiche wie bei 'sumAnnihilator'.
prodAnnihilator :: (Ring a, HaveAnnihilatingPolynomial a) => Poly a -> Poly a -> Poly a
prodAnnihilator f g =
    flip fromArray' annihilatingPolynomial $
        listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    elems = [arr ij kl | ij <- indices, kl <- indices ]
    arr (i,j) (k,l)
	| i < n - 1  && j < m - 1
	= if (k,l) == (i+1,j+1) then unit else zero
	| i == n - 1 && j < m - 1
	= if l == j + 1 then negate (xs !! k) else zero
	| i < n - 1  && j == m - 1
	= if k == i + 1 then negate (ys !! l) else zero
	| i == n - 1 && j == m - 1
	= xs !! k * ys !! l
    indices = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (unsafeCoeffs f, unsafeCoeffs g)

props_prodAnnihilator :: (HaveAnnihilatingPolynomial a, Show a, Eq a, Arbitrary a) => Proxy a -> [Property]
props_prodAnnihilator proxy = (:[]) $ forAll arbitrary $ \(NormedPoly f, NormedPoly g) ->
    let h  = prodAnnihilator f g
        h' = compose (fmap Poly.fromBase h) (Poly.fromBase iX * iX)
        r  = snd $ normedQuotRem h' (fmap Poly.fromBase f)
    in  leadingCoeff h == unit `asTypeOf` unProxy proxy &&
        all ((== zero) . snd . (`normedQuotRem` g)) (canonCoeffs r)

-- | Bestimmt zu einer gegebenen Ganzheitsgleichung /f/ (eines Elements /x/)
-- und eines Polynoms /p/ (welches nicht normiert sein muss) eine
-- Ganzheitsgleichung für das Element /p(x)/.
--
-- Dies könnte man natürlich einfach durch Einsetzen von /x/ in /p/ und
-- 'sumAnnihilator' sowie 'prodAnnihilator' nutzen, aber die Funktion hier ist
-- wesentlich effizienter: Sie nutzt die /R/-Algebra /R[x]/ mit dem bekannten
-- Erzeugendensystem /x^i/, wobei /i/ von /0/ (einschließlich) bis zum
-- Grad von /f/ läuft (ausschließlich) -- unabhängig vom Grad von /p/!
evalAnnihilator :: (Ring a, Eq a, HaveAnnihilatingPolynomial a) => Poly a -> Poly a -> Poly a
evalAnnihilator p f =
    flip fromArray' annihilatingPolynomial $ listArray ((0,0), (n-1, n-1)) elems
    where
    elems = concatMap row [0..fromIntegral (n-1)]
    n     = pred . length . unsafeCoeffs $ f
    row i = take n . (++ repeat zero) . unsafeCoeffs . snd $ normedQuotRem (p * iX^i) f

props_evalAnnihilator :: (HaveAnnihilatingPolynomial a, Show a, Eq a, Arbitrary a) => Proxy a -> [Property]
props_evalAnnihilator proxy = (:[]) $ forAll arbitrary $ \(NormedPoly f, p) ->
    let h = evalAnnihilator p f
    in  leadingCoeff h == unit `asTypeOf` unProxy proxy &&
        zero == snd (normedQuotRem (compose h p) f)

-- | Wertet ein Polynom mit Koeffizienten im Quellring in einem Element des
-- Ganzheitsring aus. Semantisch nicht von der Spezifikation
--
-- > eval x f = Poly.eval x (fmap fromBase f)
--
-- zu unterscheiden, aber durch Verwendung von "evalAnnihilator" schneller.
eval 
    :: (RingMorphism m, HaveAnnihilatingPolynomial (Domain m), Eq (Domain m))
    => IC m
    -> Poly (Domain m)
    -> IC m
eval z p =
    MkIC (Poly.eval (number z) (fmap mor' p)) (evalAnnihilator p (polynomial z))
    where mor' = mor ((undefined :: IC m -> Proxy m) z)

-- | Setzt ein Element des Ganzheitsrings im Zielring in seine
-- Ganzheitsgleichung ein. Nützlich in Tests, um sicherzustellen,
-- dass die mitgeführte Gleichung auch in der Tat eine Ganzheitsgleichung
-- für das Element ist.
verifyPolynomial :: (RingMorphism m) => IC m -> Codomain m
verifyPolynomial z@(MkIC x f) = Poly.eval x $ fmap mor' f
    where mor' = mor ((undefined :: IC m -> Proxy m) z)


-- | Konstante für den goldenen Schnitt.
goldenRatio :: IC QinC
goldenRatio = MkIC C.goldenRatio (iX^2 - iX - unit)

-- | Konstante für die Quadratwurzel aus 2.
sqrt2 :: IC QinC
sqrt2 = MkIC C.sqrt2 (iX^2 - unit - unit)

instance AllowsConjugation (IC QinC) where
    conjugate (MkIC z p) = MkIC (conjugate z) p
    imagUnit             = MkIC (C.fromBase imagUnit) (iX^2 + unit)


-- sollte nicht mit 'stdArgs', sondern einer Beschränkung wie
-- > stdArgs{ maxSize = 4 }
-- getestet werden.
props_IntegralClosure :: [Property]
props_IntegralClosure = concat
    [ props_sumAnnihilator  (undefined :: Proxy (F (Rational)))
    , props_prodAnnihilator (undefined :: Proxy (F (Rational)))
    , props_evalAnnihilator (undefined :: Proxy (F (Rational)))
    ]
