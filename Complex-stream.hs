{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Complex where

import Prelude hiding (zipWith)
import Control.Monad (liftM, liftM2)

import Stream
import ComplexRational hiding (magnitudeBound)
import qualified ComplexRational

newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)

type Nat = Integer

newtype Complex = MkComplex { unComplex :: Stream (R ComplexRational) }

instance Eq   Complex where (==) = undefined
instance Show Complex where show = undefined

instance Num Complex where
    MkComplex xs + MkComplex ys = MkComplex $ zipWith (liftM2 (+)) (everyN 2 xs) (everyN 2 ys)
    f * g = MkComplex $ \n -> do
	fBound <- magnitudeBound f
	gBound <- magnitudeBound g
	let h = fBound + gBound + 1
	zipWith (liftM2 (*)) (everyN h (unComplex f)) (everyN h (unComplex g))

    abs (MkComplex f) = MkComplex $ map (liftM abs) f

    signum = error "signum on Complex"

    fromInteger = MkComplex . const . return . fromInteger

magnitudeBound :: Complex -> R Integer
magnitudeBound (MkComplex f) = liftM (succ . ComplexRational.magnitudeBound) $ f 1
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f

goldenRatio :: Complex
goldenRatio = MkComplex $ \n -> xs !! fromIntegral n
    where
    xs = iterate (recip . (1 +)) 1
