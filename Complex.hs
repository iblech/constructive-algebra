{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Complex where

import Control.Monad (liftM, liftM2)
import ComplexRational hiding (magnitudeBound)
import qualified ComplexRational as ComplexRational
import System.IO.Unsafe

newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)
unsafeRunR :: R a -> a
unsafeRunR = unsafePerformIO . runR

type Nat = Integer

newtype Complex = MkComplex { unComplex :: Nat -> R ComplexRational }

instance Eq   Complex where (==) = undefined
instance Show Complex where show = undefined

instance Num Complex where
    MkComplex f + MkComplex g = MkComplex $ \n -> liftM2 (+) (f (2*n)) (g (2*n))
    f * g = MkComplex $ \n -> do
	fBound <- magnitudeBound f
	gBound <- magnitudeBound g
	let n' = n * (fBound + gBound + 1)
	liftM2 (*) (unComplex f n') (unComplex g n')
    negate (MkComplex f) = MkComplex $ liftM negate . f

    abs (MkComplex f) = MkComplex $ liftM abs . f

    signum = error "signum on Complex"

    fromInteger = MkComplex . const . return . fromInteger

-- recip-Problematik...
instance Fractional Complex where
    recip        = recip'
    fromRational = constant . fromRational

magnitudeBound :: Complex -> R Integer
magnitudeBound (MkComplex f) = liftM (succ . ComplexRational.magnitudeBound) $ f 1
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f

constant :: ComplexRational -> Complex
constant = MkComplex . const . return

-- Sei x algebraisch und n fest. Dann gilt stets:
--   |x| > 0 oder |x| < 1/n.
-- magnitudeZero n x gibt im ersten Fall False, im zweiten True zurück,
-- es gilt also:
--     magnitudeZero n x == False  ==>  |x| > 0,
-- aber die Umkehrung stimmt nicht.
magnitudeZero :: Nat -> Complex -> R Bool
magnitudeZero n (MkComplex f) = do
    approx <- f (2 * n)
    -- |approx - z| < 1/(2n)
    if magnitudeSq approx < 1 / (2*fromInteger n)^2
	then return True
	else return False  -- sgn z = sgn approx

-- Sei (z_n) von 0 entfernt.
-- Dann ist |z_n| >= 1/N für alle n >= N
-- und |z| >= 2/N mit N = apartnessBound.
apartnessBound :: Complex -> R Integer
apartnessBound (MkComplex f) = go 1
    where
    go i = do
	approx <- f i
	if magnitudeSq approx >= (3/fromInteger i)^2
	    then return i
	    else go (i + 1)

-- Vor.: Argument ist von 0 entfernt
recip' :: Complex -> Complex
recip' z@(MkComplex f) = MkComplex $ \n -> do
    n0 <- apartnessBound z
    let n' = halve $ n * n0^2
    liftM recip $ f n'
    where
    halve i
	| i `mod` 2 == 0 = i `div` 2
	| otherwise      = i `div` 2 + 1

goldenRatio :: Complex
goldenRatio = MkComplex $ return . goldenRatioSeq

sqrt2 :: Complex
sqrt2 = MkComplex $ return . sqrt2Seq
