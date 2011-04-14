module RootFinding where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip)
import Ring
import Field
import NumericHelper
import ComplexRational hiding (magnitudeUpperBound)
import Complex
import Algebraic
import Polynomial
import Control.Monad

-- Für normierte Polynome!
rootMagnitudeUpperBound :: Poly Complex -> R Rational
rootMagnitudeUpperBound (MkPoly zs) = liftM ((1 +) . maximum) (mapM magnitudeUpperBound zs)
-- erfüllt: |z| <= rootMagnitudeUpperBound f für alle Nullstellen z von f

type Modulus = Rational -> Rational
-- epsilon -> delta

-- liefert einen glm.-Stetigkeitsmodulus auf dem Kompaktum |z| <= r.
polyContinuity :: Poly Complex -> Rational -> R Modulus
polyContinuity p r = do
    p' <- liftM MkPoly $ mapM magnitudeUpperBound $ unPoly $ derivative p
    let lip = eval r p'
    return $ \eps -> eps / lip

-- Gitter hat dann Eigenschaft: Zu jedem beliebigen Punkt z mit |z| <= r gibt
-- es einen Gitterpunkt, dessen Entfernung zu z echt kleiner als delta ist.
mesh :: Rational -> Rational -> [ComplexRational]
mesh r delta = map (uncurry (:+:)) $ filter (\(x,y) -> x^2 + y^2 <= (r+delta)^2) $ zs
    where
    n  = roundUp $ 2 * r / delta
    zs = [ (-r + delta*fromInteger i, -r + delta*fromInteger j) | i <- [0..n], j <- [0..n] ]

-- Vorbedingung: Funktion verschwindet nirgends.
-- Gibt ein (Msq,eps) derart zurück, dass
--     |fx| >= sqrt(Msq) - eps für alle x.
findApartnessBound
    :: (Rational -> [ComplexRational])   -- Meshfunktion
    -> (ComplexRational -> Complex)
    -> Modulus 
    -> R (Rational,Rational)
findApartnessBound mkMesh fun modulus = go 1
    where
    go :: Rational -> R (Rational,Rational)
    go eps = do
        minSq <- liftM minimum . mapM (absSq . fun) $ zs
        if minSq > eps^2
            then return (minSq, eps)
            else go (eps / 2)
        where
        zs      = mkMesh (modulus (eps/2))
        absSq z = liftM magnitudeSq $ approx' (eps/2) z

exPoly :: Poly Complex
exPoly = (iX - fromRational 3) * (iX - fromRational 7)
