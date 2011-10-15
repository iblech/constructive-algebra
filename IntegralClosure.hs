-- | Dieses Modul stellt Ganzheitsringe zur Verfügung:
-- Zu einem 'RingMorphism' /m/ ist 'IC' /m/ der Ring derjenigen Elemente
-- von 'Codomain' /m/, welche über 'Domain' /m/ ganz sind, also eine
-- normierte Polynomgleichung mit Koeffizienten aus 'Domain' /m/ erfüllen.
{-# LANGUAGE FlexibleContexts, UndecidableInstances, FlexibleInstances, TypeFamilies, GADTs #-}
module IntegralClosure
    ( -- * Typen
      IC(..), number, polynomial
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

import Prelude hiding (fromInteger, fromRational, (+), (*), (-), (^), (/), negate)
import Complex hiding (goldenRatio, sqrt2)
import qualified Complex as C
import qualified Polynomial as Poly
import Polynomial as Poly
import Matrix hiding ((!!))
import Ring
import RingMorphism
import Field
import Smith
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
data IC m where
    MkIC
        :: (RingMorphism m)
        => Codomain m  -- Element des Zielrings
        -> NormedPoly (Domain m)
                       -- eine die Zugehörigkeit zum Ganzheitsring bezeugende
                       -- Ganzheitsgleichung
        -> IC m

number :: (RingMorphism m) => IC m -> Codomain m
number (MkIC z _) = z

polynomial :: (RingMorphism m) => IC m -> NormedPoly (Domain m)
polynomial (MkIC _ f) = f

-- | Liftet Elemente /x/ des Quellrings in den Ganzheitsring,
-- mit der trivialen Ganzheitsgleichung /X - x/ als Zeuge der Ganzheit.
fromBase :: (RingMorphism m) => Domain m -> IC m
fromBase x = r
    where
    r    = MkIC (mor' x) $ MkNormedPoly (iX - Poly.fromBase x)
    mor' = mor ((undefined :: IC m -> Proxy m) r)


instance (RingMorphism m, HasAnnihilatingPolynomials (Domain m)) => Ring (IC m) where
    MkIC x p + MkIC x' p' = MkIC (x + x') (sumAnnihilator p p')
    MkIC x p * MkIC x' p'
        {-
        | couldBeNotX (unNormedPoly p)  == False = zero
        | couldBeNotX (unNormedPoly p') == False = zero
        -}
        | otherwise                              = MkIC (x * x') (prodAnnihilator p p')

    negate (MkIC x p) = MkIC (negate x) (MkNormedPoly (MkPoly as))
	where
	as = reverse $ zipWith (*) (reverse $ canonCoeffs' p) (cycle [unit,negate unit])

    fromInteger i = MkIC (fromInteger i) (MkNormedPoly (iX - fromInteger i))

    zero = IntegralClosure.fromBase zero
    unit = IntegralClosure.fromBase unit

instance (RingMorphism m, Eq (Codomain m)) => Eq (IC m) where
    x == y = number x == number y

instance (RingMorphism m, IntegralDomain (Codomain m), HasAnnihilatingPolynomials (Domain m)) =>
    IntegralDomain (IC m)

instance (RingMorphism m, HasAnnihilatingPolynomials (Domain m), HasRationalEmbedding (Domain m)) =>
    HasRationalEmbedding (IC m) where
    fromRational r = z
        where
        mor' = mor ((undefined :: IC m -> Proxy m) z)
        z    = MkIC (mor' (fromRational r)) (MkNormedPoly $ iX - fromRational r)

instance (RingMorphism m, HasFloatingApprox (Codomain m)) => HasFloatingApprox (IC m) where
    unsafeApprox = unsafeApprox . number


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
sumAnnihilator :: (Ring a, HasAnnihilatingPolynomials a) => NormedPoly a -> NormedPoly a -> NormedPoly a
sumAnnihilator f g =
    fromArray' annihilatingPolynomial $
        listArray ((0,0), (length inds - 1, length inds - 1)) elts
    where
    elts = [arr ij kl | ij <- inds, kl <- inds ]
    arr (i,j) (k,l) = arr1 (i,j) (k,l) + arr2 (i,j) (k,l)
    arr1 (i,j) (k,l)
	| i < n - 1 = if (k,l) == (i+1,j) then unit else zero
	| otherwise = if l == j then negate (xs !! k) else zero
    arr2 (i,j) (k,l)
	| j < m - 1 = if (k,l) == (i,j+1) then unit else zero
	| otherwise = if k == i then negate (ys !! l) else zero
    inds = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (canonCoeffs' f, canonCoeffs' g)

-- sollte nicht mit 'stdArgs' getestet werden, sondern mit einer erheblichen
-- Beschränkung, wie beispielsweise:
--
-- > mapM_ (Test.QuickCheck.quickCheckWith stdArgs{maxSize=4}) $
--       props_sumAnnihilator (undefined :: Proxy (F Rational))
props_sumAnnihilator :: (HasAnnihilatingPolynomials a, Show a, Eq a, Arbitrary a) => Proxy a -> [Property]
props_sumAnnihilator proxy = (:[]) $ forAll arbitrary $ \(f@(MkNormedPoly f'), g@(MkNormedPoly g')) ->
    let h  = sumAnnihilator f g `asTypeOf` MkNormedPoly (Poly.fromBase (unProxy proxy))
        -- Hier evaluieren wir per Hand h(X+Y) im Ring (R[Y]/(g))[X]/(f)...
        h' = compose (fmap Poly.fromBase (unNormedPoly h)) (Poly.fromBase iX + iX)
        r  = snd $ normedQuotRem h' (fmap Poly.fromBase f')
        -- ...null müsste herauskommen:
    in  normedPolyProp h && all ((== zero) . snd . (`normedQuotRem` g')) (canonCoeffs r)

-- | Bestimmt zu zwei gegebenen Ganzheitsgleichungen /f/ (eines Elements /x/)
-- und /g/ (eines Elements /y/) eine, welche das Produkt /x y/ als Nullstelle
-- besitzt. Das Vorgehen ist das gleiche wie bei 'sumAnnihilator'.
prodAnnihilator :: (Ring a, HasAnnihilatingPolynomials a) => NormedPoly a -> NormedPoly a -> NormedPoly a
prodAnnihilator f g =
    fromArray' annihilatingPolynomial $
        listArray ((0,0), (length inds - 1, length inds - 1)) elts
    where
    elts = [arr ij kl | ij <- inds, kl <- inds ]
    arr (i,j) (k,l)
	| i < n - 1  && j < m - 1
	= if (k,l) == (i+1,j+1) then unit else zero
	| i == n - 1 && j < m - 1
	= if l == j + 1 then negate (xs !! k) else zero
	| i < n - 1  && j == m - 1
	= if k == i + 1 then negate (ys !! l) else zero
	| i == n - 1 && j == m - 1
	= xs !! k * ys !! l
        | otherwise
        = error "prodAnnihilator: unmöglicher Fall"
    inds = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (canonCoeffs' f, canonCoeffs' g)

props_prodAnnihilator :: (HasAnnihilatingPolynomials a, Show a, Eq a, Arbitrary a) => Proxy a -> [Property]
props_prodAnnihilator proxy = (:[]) $ forAll arbitrary $ \(f@(MkNormedPoly f'), g@(MkNormedPoly g')) ->
    let h  = prodAnnihilator f g `asTypeOf` MkNormedPoly (Poly.fromBase (unProxy proxy))
        h' = compose (fmap Poly.fromBase (unNormedPoly h)) (Poly.fromBase iX * iX)
        r  = snd $ normedQuotRem h' (fmap Poly.fromBase f')
    in  normedPolyProp h && all ((== zero) . snd . (`normedQuotRem` g')) (canonCoeffs r)

-- | Bestimmt zu einer gegebenen Ganzheitsgleichung /f/ (eines Elements /x/)
-- und eines Polynoms /p/ (welches nicht normiert sein muss) eine
-- Ganzheitsgleichung für das Element /p(x)/.
--
-- Dies könnte man natürlich einfach durch geeignetes Einsetzen von /x/ in /p/ und
-- 'sumAnnihilator' sowie 'prodAnnihilator' erreichen, aber die Funktion hier ist
-- wesentlich effizienter: Sie nutzt die /R/-Algebra /R[x]/, die unabhängig von
-- dem Grad von /p/ das bekannte Erzeugendensystem /x^i/, wobei /i/ von /0/
-- (einschließlich) bis zum Grad von /f/ läuft (ausschließlich, besitzt.
--
-- Somit ist der Grad des ermittelten Polynoms dann höchstens (/<=/) der von /f/.
evalAnnihilator :: (Ring a, Eq a, HasAnnihilatingPolynomials a) => Poly a -> NormedPoly a -> NormedPoly a
evalAnnihilator p f =
    fromArray' annihilatingPolynomial $ listArray ((0,0), (n-1, n-1)) elts
    where
    elts  = concatMap row [0..fromIntegral (n-1)]
    n     = pred . length . canonCoeffs' $ f
    row i = take n . (++ repeat zero) . unsafeCoeffs . snd $ normedQuotRem (p * iX^i) (unNormedPoly f)

props_evalAnnihilator :: (HasAnnihilatingPolynomials a, Show a, Eq a, Arbitrary a) => Proxy a -> [Property]
props_evalAnnihilator proxy = (:[]) $ forAll arbitrary $ \(f, p) ->
    let h = evalAnnihilator p f `asTypeOf` MkNormedPoly (Poly.fromBase (unProxy proxy))
    in  normedPolyProp h &&
        zero == snd (normedQuotRem (compose (unNormedPoly h) p) (unNormedPoly f))

-- | Wertet ein Polynom mit Koeffizienten im Quellring in einem Element des
-- Ganzheitsring aus. Semantisch nicht von der Spezifikation
--
-- > eval x f = Poly.eval x (fmap fromBase f)
--
-- zu unterscheiden, aber durch Verwendung von "evalAnnihilator" schneller.
eval 
    :: (RingMorphism m, HasAnnihilatingPolynomials (Domain m), Eq (Domain m))
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
verifyPolynomial z@(MkIC x (MkNormedPoly f)) = Poly.eval x $ fmap mor' f
    where mor' = mor ((undefined :: IC m -> Proxy m) z)


-- | Konstante für den goldenen Schnitt.
goldenRatio :: IC QinC
goldenRatio = MkIC C.goldenRatio $ mkNormedPoly (iX^2 - iX - unit)

-- | Konstante für die Quadratwurzel aus 2.
sqrt2 :: IC QinC
sqrt2 = MkIC C.sqrt2 $ mkNormedPoly (iX^2 - unit - unit)

instance HasConjugation (IC QinC) where
    type RealSubring (IC QinC) = IC QinR
    conjugate (MkIC z p) = MkIC (conjugate z) p
    imagUnit             = MkIC (C.fromBase imagUnit) $ mkNormedPoly (iX^2 + unit)
    realPart  z          = MkIC (realPart (number z')) (polynomial z')
        where z' = fromRational (1/2) * (z + conjugate z)


-- sollte nicht mit 'stdArgs', sondern einer Beschränkung wie
-- > stdArgs{ maxSize = 4 }
-- getestet werden.
props_IntegralClosure :: [Property]
props_IntegralClosure = concat
    [ props_sumAnnihilator  (undefined :: Proxy (F (Rational)))
    , props_prodAnnihilator (undefined :: Proxy (F (Rational)))
    , props_evalAnnihilator (undefined :: Proxy (F (Rational)))
    ]
