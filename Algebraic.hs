{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, FlexibleContexts,
StandaloneDeriving, UndecidableInstances, FlexibleInstances #-}
module Algebraic where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational)
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

instance Eq (Alg QinC) where
    x == y = unsafeRunR . liftM isNothing $ invert (x - y)

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
    --R $ putStrLn $ "OPTI!: " ++ show (approx z)
    foundApartness <- go [1,10]
    if foundApartness then return $ Just zInv else do
    if null bounds then return Nothing else do
    zeroTest <- magnitudeZeroTestR (roundDownToRecipN $ unF (minimum bounds)) (number z)
    if zeroTest
        then return Nothing
        else return $ Just zInv
    where
    as     = coeffs (polynomial z)
    bs     = dropWhile (== 0) as
    k      = length bs
    p'     = norm . MkPoly . reverse $ bs
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

isRational :: Alg QinC -> Bool
isRational z =
    any (== z) nonNegativeCandidates ||
    any (== z) (map negate nonNegativeCandidates)
    where
    p     = polynomial . unAlg $ z
    (r,s) = (numerator &&& denominator) . unF $ eval 0 p
    nonNegativeCandidates =
        [ fromRational (p % q)
        | p <- positiveDivisors r , q <- positiveDivisors s
        ]
