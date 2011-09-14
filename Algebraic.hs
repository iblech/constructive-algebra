{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, FlexibleContexts,
StandaloneDeriving, UndecidableInstances, FlexibleInstances, PatternGuards #-}
module Algebraic where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger)
import qualified IntegralClosure as IC
import IntegralClosure hiding (goldenRatio,sqrt2)
import Complex hiding (goldenRatio,sqrt2)
import ComplexRational
import Ring
import Field
import RingMorphism
import NumericHelper
import Polynomial
import Data.Maybe
import Control.Monad
import Control.Arrow
import Data.Ratio
import Real
import Euclidean
import Debug.Trace
import Control.Exception

-- früher: newtype (RingMorphism m, Field (Domain m), Codomain m ~ Complex) => Alg m =
-- dann Codomain m ~ Complex weggelassen
-- FIXME
newtype (RingMorphism m, Field (Domain m)) => Alg m =
    MkAlg { unAlg :: IC m }

deriving instance (Ring (IC m)) => Ring (Alg m)
deriving instance (AllowsRationalEmbedding (IC m)) => AllowsRationalEmbedding (Alg m)
deriving instance (RingMorphism m, Field (Domain m), ApproxFloating (Codomain m)) => ApproxFloating (Alg m)
deriving instance AllowsConjugation (Alg QinC)

instance Field (Alg QinC) where
    recip z = unsafeRunR $ do
        Just z' <- invert z
        return z'

instance IntegralDomain (Alg QinC)

-- XXX: effizienz/uneleganz abwiegen
instance Eq (Alg QinC) where
    x == y
        | eval0 (unNormedPoly (polynomial (unAlg z))) /= zero
        = False
        | otherwise
        = unsafeRunR . liftM isNothing $ invert z
        where z = x - y

instance Field (Alg QinR) where
    recip z = unsafeRunR $ do
        Just z' <- invert' z
        return z'

instance IntegralDomain (Alg QinR)

instance Eq (Alg QinR) where
    x == y = unsafeRunR . liftM isNothing $ invert' (x - y)

instance Ord (Alg QinR) where
    compare x y
        | x == y    = EQ
        | otherwise = case signum' . number . unAlg $ x - y of
            N -> LT
            P -> GT

goldenRatio :: Alg QinC
goldenRatio = MkAlg $ IC.goldenRatio

sqrt2 :: Alg QinC
sqrt2 = MkAlg $ IC.sqrt2

invert :: Alg QinC -> R (Maybe (Alg QinC))
invert (MkAlg z) = do
    -- Optimierung
    --trace ("invert: " ++ show (approx z)) $ do
    foundApartness <- go [1,10,100]
    if foundApartness then return $ Just zInv else do
    if null bounds then return Nothing else do
    zeroTest <- magnitudeZeroTestR (roundDownToRecipN $ unF (minimum bounds)) (number z)
    if zeroTest
        then return Nothing
        else return $ Just zInv
    where
    -- XXX: okay, dass coeffs Nuller liefert?
    as     = canonCoeffs' (polynomial z)
    bs     = dropWhile (== 0) as
    k      = length bs
    p'     = normalize' . MkPoly . reverse $ bs
    bounds = 1 : zipWith f (tail bs) [1..]
	where
	f b j
	    | b == 0    = 1  --FIXME
	    | otherwise
	    = abs (head bs) / (fromIntegral k * abs b)
    zInv   = MkAlg $ MkIC (recip (number z)) p'
    go []     = return False
    go (n:ns) = do
        q <- unComplex (number z) n
        if magnitudeSq q >= 1/fromIntegral n^2
            then return True
            else go ns

invert' :: Alg QinR -> R (Maybe (Alg QinR))
invert' (MkAlg (MkIC z p)) = liftM (fmap f) (invert (MkAlg (MkIC (unReal z) p)))
    where
    f :: Alg QinC -> Alg QinR
    f (MkAlg (MkIC z' p')) = MkAlg (MkIC (MkReal z') p')

tr q = trace ("ANTW.: " ++ show q) $ q
-- FIXME: auch isComplexRational implementieren
-- FIXME: UNBEDINGT Korrektheit mit Skript überprüfen!
isRational :: Alg QinC -> Maybe Rational
--isRational z = tr $ trace ("PRÜFE AUF RAT.: " ++ show (approx z, polynomial . unAlg $ z)) $ listToMaybe $ do
isRational z = listToMaybe $ do
    cand <- [zero] ++ nonNegativeCandidates ++ map negate nonNegativeCandidates
    guard $ fromRational cand == z
    return cand
    where
    -- XXX: okay, dass coeffs Nuller liefert?
    as    = dropWhile (== 0) . canonCoeffs' . polynomial . unAlg $ z
    (r,s) = (numerator &&& denominator) $ unF $ head as
    nonNegativeCandidates =
        [ p % q
        | p <- positiveDivisors r, q <- positiveDivisors s
        ]

isInteger :: Alg QinC -> Maybe Integer
isInteger z
    | Nothing <- isApproxInteger z = Nothing
    | otherwise                    = do
        r <- isRational z
        let (n,m) = numerator r `quotRem` denominator r
        if m == 0 then return n else Nothing

-- ist z = a mit a ganzzahlig, dann ist isApproxInteger z = a.
-- liefert sonst näheste ganze Zahl, oder Nothing, falls klar ist, dass z nicht
-- ganzzahlig sein kann.
isApproxInteger :: Alg QinC -> Maybe Integer
isApproxInteger z = unsafeRunR $ do
    --zz <- R $ evaluate (approx z)
    --R $ putStrLn $ "isApproxInteger: " ++ show zz
    z0@(q :+: _) <- unComplex (number . unAlg $ z) 100
    let (a,b) = (floor q, ceiling q)
    --_ <- R $ evaluate a
    --_ <- R $ evaluate b
    --R $ putStrLn $ "isApproxInteger! " ++ show zz ++ ": " ++ show (magnitudeSq (z0 - fromInteger a) <= 1/100^2 || magnitudeSq (z0 - fromInteger b) <= 1/100^2)
    if magnitudeSq (z0 - fromInteger a) <= 1/100^2 then return $ Just a else do
    if magnitudeSq (z0 - fromInteger b) <= 1/100^2 then return $ Just b else do
    return Nothing

isRationalPoly :: Poly (Alg QinC) -> Maybe (Poly Rational)
isRationalPoly = isGoodPoly isRational

isIntegerPoly :: Poly (Alg QinC) -> Maybe (Poly Integer)
isIntegerPoly = isGoodPoly isInteger

isApproxIntegerPoly :: Poly (Alg QinC) -> Maybe (Poly Integer)
isApproxIntegerPoly = isGoodPoly isApproxInteger

isGoodPoly :: (Alg QinC -> Maybe a) -> Poly (Alg QinC) -> Maybe (Poly a)
isGoodPoly isGood p
    | all isJust as = Just . MkPoly $ map fromJust as
    | otherwise     = Nothing
    where
    as = map isGood $ unsafeCoeffs p

eval 
    :: Alg QinC
    -> Poly Rational
    -> Alg QinC
eval z p = MkAlg $ IC.eval (unAlg z) (fmap F p)
