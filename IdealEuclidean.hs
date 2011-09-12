{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, StandaloneDeriving #-}
module IdealEuclidean where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/), (^), negate, fromInteger)
import qualified Prelude as P
import Ring
import Field
import Nat
import IdealExtension
import Polynomial
import Control.Monad
import Data.List

idealCanonCoeffs :: (IdealField a) => Poly a -> Nondet a [a]
idealCanonCoeffs = liftM reverse . dropWhileM (`idealEquals` zero) . reverse . unPoly

idealDegree :: (IdealField a) => Poly a -> Nondet a Integer
idealDegree = liftM pred . liftM genericLength . idealCanonCoeffs

idealNorm :: (IdealField a) => Poly a -> Nondet a (Poly a)
idealNorm f = do
    as <- idealCanonCoeffs f
    if null as then error "idealNorm zero" else do
    Just r <- idealRecip (last as)
    return . MkPoly $ map (r *) as

dropWhileM :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
dropWhileM phi []     = return []
dropWhileM phi (x:xs) = do
    ok <- phi x
    if ok then dropWhileM phi xs else return (x:xs)

idealQuotRem :: (IdealField a) => Poly a -> Poly a -> Nondet a (Poly a, Poly a)
idealQuotRem f g = do
    as <- idealCanonCoeffs f
    bs <- idealCanonCoeffs g
    if length as < length bs then return (zero, f) else do
    Just u <- idealRecip (last bs)
    let q' = (last as * u) .* (iX^(genericLength as - genericLength bs))
    (q,r) <- idealQuotRem (f - q' * g) g
    return (q + q', r)

--exi :: Nondet (ISE Rational s) (Poly (ISE Rational s), Poly (ISE Rational s))
exi = idealGCD ((iX - constant (adjointedRoot :: ISE Rational ())) * (iX - fromInteger 3)) ((adjointedRoot - unit) .* (iX - constant adjointedRoot) * (iX - fromInteger 5))

idealGCD :: (IdealField a) => Poly a -> Poly a -> Nondet a (Poly a,Poly a,Poly a,Poly a)
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

idealNormedGCD :: (IdealField a) => Poly a -> Poly a -> Nondet a (Poly a)
idealNormedGCD a b = do
    (u,v,s,t) <- idealGCD a b
    idealNorm $ u*a + v*b
