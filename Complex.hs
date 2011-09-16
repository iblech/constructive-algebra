{-# LANGUAGE GeneralizedNewtypeDeriving, EmptyDataDecls, TypeFamilies #-}
module Complex where

import Prelude hiding ((+), (*), (/), (-), (^), fromInteger, fromRational, recip, negate, abs, Real)
import qualified Prelude as P
import Control.Monad (liftM, liftM2)
import ComplexRational hiding (magnitudeUpperBound)
import qualified ComplexRational as ComplexRational
import Ring
import Field
import RingMorphism
import NumericHelper
import System.IO.Unsafe
import System.IO
import Control.Exception
import Text.Printf
import Debug.Trace
import System.Time
import Nat
import Data.Maybe

newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)
unsafeRunR :: R a -> a
unsafeRunR = unsafePerformIO . runR

data Complex = MkRat !ComplexRational | MkComplex (Nat -> R ComplexRational)
unComplex :: Complex -> Nat -> R ComplexRational
unComplex (MkRat f) _ = return f
unComplex (MkComplex f) n = f n

newtype Real = MkReal { unReal :: Complex }
    deriving (Ring,HasRationalEmbedding,HasFloatingApprox)
-- Invariante: Alle epsilon-Näherungen müssen reell sein.

instance Ring Complex where
    MkRat f + MkComplex g = MkComplex $ liftM (f +) . g
    MkComplex f + MkRat g = MkComplex $ liftM (+ g) . f
    MkRat f + MkRat g     = MkRat (f + g)
    MkComplex f + MkComplex g = MkComplex $ \n -> liftM2 (+) (f (2*n)) (g (2*n))
    MkRat f * MkRat g = MkRat (f * g)
    f * g = MkComplex $ \n -> liftM2 (*) (unComplex f (n*k)) (unComplex g (n*k))
	where
	k = unsafeRunR $ do
            --R . putStrLn $ "k für " ++ show (approx f)
	    fBound <- magnitudeUpperBound f
	    gBound <- magnitudeUpperBound g
            --R . putStrLn $ "k für-Erg " ++ show (roundUp $ fBound + gBound + 1)
	    return $ roundUp $ fBound + gBound + 1
    negate (MkRat f) = MkRat (negate f)
    negate (MkComplex f) = MkComplex $ liftM negate . f
    fromInteger = MkRat . fromInteger
    zero = fromInteger zero
    unit = fromInteger unit

instance HasConjugation Complex where
    type RealSubring Complex = Real
    conjugate (MkComplex f) = MkComplex $ liftM conjugate . f
    conjugate (MkRat f)     = MkRat (conjugate f)
    realPart  (MkRat f)     = MkReal $ MkRat $ fromRational . realPart $ f
    realPart  (MkComplex f) = MkReal $ MkComplex $ liftM (fromRational . realPart) . f
    imagUnit = MkRat imagUnit

instance HasRationalEmbedding Complex where
    fromRational = MkRat . fromRational

instance HasFloatingApprox Complex where
    approx = approx . unsafeRunR . ($ 100) . unComplex

data QinC
instance RingMorphism QinC where
    type Domain   QinC = F Rational
    type Codomain QinC = Complex
    mor _ = MkRat . fromRational . unF

data QinR
instance RingMorphism QinR where
    type Domain   QinR = F Rational
    type Codomain QinR = Real
    mor _ = MkReal . MkRat . fromRational . unF

magnitudeUpperBound :: Complex -> R Rational
magnitudeUpperBound (MkRat f) = return $ ComplexRational.magnitudeUpperBound f
magnitudeUpperBound (MkComplex f) = liftM ((+1) . ComplexRational.magnitudeUpperBound) $ f 1
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f

fromBase :: ComplexRational -> Complex
fromBase = MkRat

approx' :: Rational -> Complex -> R ComplexRational
approx' eps (MkRat f)     = return f
approx' eps (MkComplex f) = f $ ceiling . fromJust . recip $ eps

traceEvals :: String -> Complex -> Complex
traceEvals _ = id
{-
traceEvals name (MkRat     f) = MkRat f
traceEvals name (MkComplex f) = MkComplex $ \n -> R $ do
    n' <- evaluate n
    hPutStrLn stderr $ printf "%-5s_%2d = ..." ("[" ++ name ++ "]") n' -- (show (x' :+: y'))
    x :+: y <- runR (f n')
    x' <- evaluate x
    y' <- evaluate y
    hPutStrLn stderr $ printf "%-5s_%2d = %s" ("[" ++ name ++ "]") n' (show (x' :+: y'))
    return (x' :+: y')
-}

timeEvals :: String -> Complex -> Complex
timeEvals name (MkRat f)     = MkRat f
timeEvals name (MkComplex f) = MkComplex $ \n -> R $ do
    n' <- evaluate n
    t0 <- getClockTime
    x :+: y <- runR (f n')
    x'      <- evaluate x
    y'      <- evaluate y
    t1 <- getClockTime
    hPutStrLn stderr $ printf "%s: %f\n" name ((P./(10 P.^12 :: Double)) $ P.fromInteger $ tdPicosec $ diffClockTimes t1 t0)
    return (x' :+: y')

-- Sei x komplex und n fest. Dann gilt stets:
--   |x| > 0 oder |x| < 1/n.
-- magnitudeZero n x gibt im ersten Fall False, im zweiten True zurück,
-- es gilt also:
--     magnitudeZero n x == False  ==>  |x| > 0,
-- aber die Umkehrung stimmt nicht.
magnitudeZeroTestR :: Nat -> Complex -> R Bool
magnitudeZeroTestR n (MkRat f) = if f /= zero then return False else return True
magnitudeZeroTestR n (MkComplex f) = do
    appr <- f (2 * n)
    return $ magnitudeSq appr < 1 / (2*fromInteger n)^2
-- |approx - z| < 1/(2n)
-- Beweis:
-- Gelte |approx| <  1/(2n). Dann |x| <= |approx| + |x - approx| < 1/n.
-- Gelte |approx| >= 1/(2n). Dann |x| >= |approx| - |approx - x| > 0.

-- Sei (z_n) von 0 entfernt in dem Sinn, dass
-- es eine rationale Zahl q > 0 mit |z_n| > q gibt.
-- Dann ist |z_n| > 1/N für alle n >= N
-- und |z| > 2/N mit N = apartnessBound.
apartnessBound :: Complex -> R Integer
apartnessBound (MkRat f) = apartnessBound (MkComplex $ const (return f))
apartnessBound (MkComplex f) = go 1
    where
    go i = do
	appr <- f i
	if magnitudeSq appr >= (3/fromInteger i)^2
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
recip' (MkRat f) = MkRat . fromJust . recip $ f
recip' z@(MkComplex f) = MkComplex $ \n -> do
    n0 <- apartnessBound z
    let n' = halve $ n * n0^2
    liftM (fromJust . recip) $ f n'
    where
    halve i
	| i `mod` 2 == 0 = i `div` 2
	| otherwise      = i `div` 2 + 1
    -- Eigenschaft: halve i = Aufrundung(i / 2).

goldenRatio :: Complex
goldenRatio = MkComplex $ return . goldenRatioSeq

sqrt2 :: Complex
sqrt2 = MkComplex $ return . sqrt2Seq
