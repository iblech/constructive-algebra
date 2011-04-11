{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Complex where

import Prelude hiding ((+), (*), (/), (-), (^), fromInteger, recip, negate)
import Control.Monad (liftM, liftM2)
import ComplexRational hiding (magnitudeBound)
import qualified ComplexRational as ComplexRational
import Ring
import Field
import Apartness
import System.IO.Unsafe

newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)
unsafeRunR :: R a -> a
unsafeRunR = unsafePerformIO . runR

type Nat = Integer

newtype Complex = MkComplex { unComplex :: Nat -> R ComplexRational }

instance Ring Complex where
    MkComplex f + MkComplex g = MkComplex $ \n -> liftM2 (+) (f (2*n)) (g (2*n))
    f * g = MkComplex $ \n -> liftM2 (*) (unComplex f (n*k)) (unComplex g (n*k))
	where
	k = unsafeRunR $ do
	    fBound <- magnitudeBound f
	    gBound <- magnitudeBound g
	    return $ fBound + gBound + 1
    negate (MkComplex f) = MkComplex $ liftM negate . f
    fromInteger = MkComplex . const . return . fromInteger
    zero = fromInteger zero
    unit = fromInteger unit

-- recip-Problematik...
instance Field Complex where
    recip = recip'

magnitudeBound :: Complex -> R Integer
magnitudeBound (MkComplex f) = liftM (succ . ComplexRational.magnitudeBound) $ f 1
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f

constant :: ComplexRational -> Complex
constant = MkComplex . const . return

instance Apartness Complex where
    magnitudeZeroTest n = unsafeRunR . magnitudeZeroTestR n

-- Sei x komplex und n fest. Dann gilt stets:
--   |x| > 0 oder |x| < 1/n.
-- magnitudeZero n x gibt im ersten Fall False, im zweiten True zurück,
-- es gilt also:
--     magnitudeZero n x == False  ==>  |x| > 0,
-- aber die Umkehrung stimmt nicht.
magnitudeZeroTestR :: Nat -> Complex -> R Bool
magnitudeZeroTestR n (MkComplex f) = do
    approx <- f (2 * n)
    -- |approx - z| < 1/(2n)
    return $ magnitudeSq approx < 1 / (2*fromInteger n)^2
-- Beweis:
-- Gelte |approx| <  1/(2n). Dann |x| <= |approx| + |x - approx| < 1/n.
-- Gelte |approx| >= 1/(2n). Dann |x| >= |approx| - |approx - x| > 0.

-- Sei (z_n) von 0 entfernt in dem Sinn, dass
-- es eine rationale Zahl q > 0 mit |z_n| > q gibt.
-- Dann ist |z_n| > 1/N für alle n >= N
-- und |z| > 2/N mit N = apartnessBound.
apartnessBound :: Complex -> R Integer
apartnessBound (MkComplex f) = go 1
    where
    go i = do
	approx <- f i
	if magnitudeSq approx >= (3/fromInteger i)^2
	    then return i
	    else go (i + 1)
{-
  Beh.:
    a) |x_N| >= 3/N  ==>  |x_n| >= 1/N f.a. n >= N  und  |x| >= 2/N.
    b) x # 0  ==>  es gibt ein N wie in a)

  Bew.:
    a) nachrechnen
    b) Sei |x| >= q > 0. Sei q >= 1/k.
       Setze dann N := 4k.
-}

-- Vor.: Argument z ist von 0 entfernt
-- Dann: recip' z stellt 1/z dar.
recip' :: Complex -> Complex
recip' z@(MkComplex f) = MkComplex $ \n -> do
    n0 <- apartnessBound z
    let n' = halve $ n * n0^2
    liftM recip $ f n'
    where
    halve i
	| i `mod` 2 == 0 = i `div` 2
	| otherwise      = i `div` 2 + 1
    -- Eigenschaft: halve i = Aufrundung(i / 2).

goldenRatio :: Complex
goldenRatio = MkComplex $ return . goldenRatioSeq

sqrt2 :: Complex
sqrt2 = MkComplex $ return . sqrt2Seq
