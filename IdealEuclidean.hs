-- | Dieses Modul stellt den euklidischen Algorithmus in Ringen der Form /k[X]/
-- bereit, wobei /k/ ein ideeller Körper, also eine Instanz von 'IdealField', ist.
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, StandaloneDeriving #-}
module IdealEuclidean
    ( idealQuotRem, idealGCD, idealNormedGCD
    , idealCanonCoeffs, idealDegree, idealNormalize
    ) where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/), (^), negate, fromInteger)
import Ring
import IdealExtension
import Polynomial
import Control.Monad
import Data.List

-- | Ideelle Entsprechung von 'canonCoeffs': Liste der Koeffizienten ohne
-- abschließende Nuller.
idealCanonCoeffs :: (IdealField a) => Poly a -> Nondet a [a]
idealCanonCoeffs = liftM reverse . dropWhileM (`idealEquals` zero) . reverse . unsafeCoeffs

-- | Ideelle Entsprechung von 'Euclidean.degree': Liefert den Grad eines Polynoms.
idealDegree :: (IdealField a) => Poly a -> Nondet a Integer
idealDegree = liftM pred . liftM genericLength . idealCanonCoeffs

-- | Ideelle Entsprechung von 'normalize': Normiert ein Polynom.
idealNormalize :: (IdealField a) => Poly a -> Nondet a (Poly a)
idealNormalize f = do
    as <- idealCanonCoeffs f
    if null as then error "idealNorm zero" else do
    Just r <- idealRecip (last as)
    return . MkPoly $ map (r *) as

-- | Monadische Version von 'dropWhile': Entfernt so lange Elemente aus der
-- gegebenen Liste, wie das monadische Prädikat erfüllt ist.
dropWhileM :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
dropWhileM _   []     = return []
dropWhileM phi (x:xs) = do
    ok <- phi x
    if ok then dropWhileM phi xs else return (x:xs)

-- | Ideelle Entsprechung von 'Euclidean.quotRem': Teilt zwei Polynome durcheinander.
idealQuotRem
    :: (IdealField a)
    => Poly a  -- ^ Dividend
    -> Poly a  -- ^ Divisor
    -> Nondet a (Poly a, Poly a)
               -- ^ ideelle Aktion, die ein Paar (q,r) mit /f = qg + r/
               -- und /r = 0 oder 'degree' r < 'degree' g/ bestimmt
idealQuotRem f g = do
    as <- idealCanonCoeffs f
    bs <- idealCanonCoeffs g
    if length as < length bs then return (zero, f) else do
    Just u <- idealRecip (last bs)
    let q' = (last as * u) .* (iX^(genericLength as - genericLength bs))
    (q,r) <- idealQuotRem (f - q' * g) g
    return (q + q', r)

{-
--exi :: Nondet (ISE Rational s) (Poly (ISE Rational s), Poly (ISE Rational s))
exi = idealGCD ((iX - Poly.fromBase (adjointedRoot :: ISE Rational ())) * (iX - fromInteger 3)) ((adjointedRoot - unit) .* (iX - Poly.fromBase adjointedRoot) * (iX - fromInteger 5))
-}

-- | Ideelle Entsprechung von 'Euclidean.gcd': Bestimmt einen größten gemeinsamen Teiler
-- zweier Polynome.
idealGCD
    :: (IdealField a)
    => Poly a  -- /f/
    -> Poly a  -- /g/
    -> Nondet a (Poly a,Poly a,Poly a,Poly a)
               -- /(u,v,s,t)/ derart, dass /d = uf + vg/ ein größter gemeinsamer
               -- Teiler von /f/ und /g/ ist, und dass /f = ds/ und /g = dt/.
idealGCD a b = do
    -- b == zero?
    bs <- idealCanonCoeffs b
    if null bs then return (unit, zero, unit, zero) else do
    (q,r) <- a `idealQuotRem` b
    (u',v',s',t') <- idealGCD b r
    let u = v'
        v = u' - q * v'
        s = t' + q * s'
        t = s'
    return (u,v,s,t)

-- | Bestimmt den größten gemeinsamen Teiler zweier Polynome als normiertes
-- Polynom.
idealNormedGCD :: (IdealField a) => Poly a -> Poly a -> Nondet a (Poly a)
idealNormedGCD a b = do
    (u,v,_,_) <- idealGCD a b
    idealNormalize $ u*a + v*b
