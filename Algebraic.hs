{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, FlexibleContexts,
StandaloneDeriving, UndecidableInstances, FlexibleInstances #-}
module Algebraic where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip)
import qualified IntegralClosure as IC
import IntegralClosure hiding (goldenRatio,sqrt2)
import Complex hiding (goldenRatio,sqrt2)
import Ring
import Field
import RingMorphism
import NumericHelper
import Polynomial
import Data.Maybe
import Control.Monad

newtype (RingMorphism m, Field (Domain m), Codomain m ~ Complex) => Alg m =
    MkAlg { unAlg :: IC m }

deriving instance (Ring (IC m)) => Ring (Alg m)

instance Field (Alg QinC) where
    recip z = unsafeRunR $ do
        Just z' <- invert z
        return z'

instance Eq (Alg QinC) where
    x == y = unsafeRunR . liftM isNothing $ invert (x - y)
        

goldenRatio :: Alg QinC
goldenRatio = MkAlg $ IC.goldenRatio

sqrt2 :: Alg QinC
sqrt2 = MkAlg $ IC.sqrt2

invert :: Alg QinC -> R (Maybe (Alg QinC))
invert (MkAlg z) =
    if null bounds then return Nothing else do
    zeroTest <- magnitudeZeroTestR (roundDownToRecipN $ unF (minimum bounds)) (number z)
    if zeroTest
        then return Nothing
        else return . Just . MkAlg $ MkIC (recip (number z)) p'
    where
    as     = coeffs (polynomial z)
    bs     = dropWhile (== 0) as
    k      = length bs
    bounds = zipWith f (tail bs) [1..]
	where
	f b j
	    | b == 0    = 17  --FIXME
	    | otherwise
	    = abs (head bs) / (fromIntegral k * abs b)
	approxRoot q a = rootSeq' q a 4
    p'     = norm . MkPoly . reverse $ bs

{-

t x = trace (show x) x


exCheckZero i x = runR $ unComplex (verifyPolynomial x) i



rec :: IC -> IC
rec (MkIC z p) = MkIC (recip z) (norm . MkPoly . reverse . coeffs $ p)
    where
    norm q = recip (leadingCoeff q) .* q
-- XXX mit X kürzen

--instance Fractional IC where
--    fromRational r = MkIC (constant $ fromRational r) (iX - fromRational r)
--    recip = error "recip"
-}
