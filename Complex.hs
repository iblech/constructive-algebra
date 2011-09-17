{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, TypeFamilies, DeriveFunctor, FlexibleContexts, UndecidableInstances, EmptyDataDecls #-}
module Complex
    ( R(..), unsafeRunR, magnitudeUpperBound
    , AST(..)
    , Complex, Real, Approx(..), QinC, QinR, unComplex, dummy
    , sqrt2, goldenRatio
    , fromBase
    , magnitudeZeroTestR, traceEvals
    , recip') where

import Prelude hiding ((+), (*), (/), (-), (^), fromInteger, fromRational, recip, negate, Real)
import qualified Prelude as P
import Control.Monad (liftM, liftM2)
import ComplexRational hiding (magnitudeUpperBound)
import qualified ComplexRational as ComplexRational
import Ring hiding (approx)
import qualified Ring as Ring
import Field
import RingMorphism
import NumericHelper
import System.IO.Unsafe
import System.IO
import Text.Printf
import Debug.Trace
import System.Time
import Nat
import Data.Maybe
import Data.Ratio

unComplex :: Complex -> Integer -> R ComplexRational
unComplex = flip approx

newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)

unsafeRunR :: R a -> a
unsafeRunR = unsafePerformIO . runR

data AST ex
    = Exact ex
    | Add   [AST ex]
    | Mult  (AST ex) (AST ex)
    | Ext   String   (Approx ex)
    deriving (Show,Functor)
-- Vorsicht: Nur Funktoren mit Lipschitzkonstante 1 verwenden!

traceEvals :: String -> Complex -> Complex
traceEvals _ = id

type Complex = AST ComplexRational
type Real    = AST Rational

newtype Approx ex = MkApprox { unApprox :: Nat -> R ex }
    deriving (Functor)

instance Show (Approx ex) where
    show _ = "<<nondet>>"

instance (Ring ex, Eq ex) => Ring (AST ex) where
    z + w       = simplify $ Add [z,w]
    (*)         = (simplify .) . Mult
    negate      = simplify . Mult (Exact (negate unit))
    zero        = Add []
    unit        = Exact unit
    fromInteger = Exact . fromInteger

dummy :: String -> ex -> AST ex
dummy name x = Ext name $ MkApprox $ const $ return x

class (Ring a) => HasMUP a where
    mup :: a -> Rational

instance HasMUP ComplexRational where
    mup = ComplexRational.magnitudeUpperBound

instance HasMUP (Ratio Integer) where
    mup = abs

instance (HasConjugation ex, Eq ex, Eq (RealSubring ex)) => HasConjugation (AST ex) where
    type RealSubring (AST ex) = AST (RealSubring ex)
    conjugate (Exact q)  = Exact (conjugate q)
    conjugate (Add zs)  = Add $ map conjugate zs
    conjugate (Mult z w) = Mult (conjugate z) (conjugate w)
    conjugate (Ext n f)  = Ext n (fmap conjugate f)
    imagUnit = Exact imagUnit
    realPart (Exact q) = Exact (realPart q)
    realPart (Add zs) = Add $ map realPart zs
    realPart (Mult z w) = realPart z * realPart w - imagPart z * imagPart w
    realPart (Ext n f) = Ext n (fmap realPart f)

instance (HasRationalEmbedding ex, Eq ex) => HasRationalEmbedding (AST ex) where
    fromRational = Exact . fromRational

instance (HasFloatingApprox ex, HasMUP ex, Eq ex) => HasFloatingApprox (AST ex) where
    approx = Ring.approx . unsafeRunR . approx 100

data QinC
instance RingMorphism QinC where
    type Domain   QinC = F Rational
    type Codomain QinC = Complex
    mor _ = Exact . fromRational . unF

data QinR
instance RingMorphism QinR where
    type Domain   QinR = F Rational
    type Codomain QinR = Real
    mor _ = Exact . fromRational . unF

approx :: (HasMUP ex) => Integer -> AST ex -> R ex
approx _ (Exact q)           = return q
approx _ (Add   [])          = return zero
approx n (Add   (Exact q : zs)) = liftM (q +) $ approx n $ Add zs
approx n (Add   zs) = do
    let k = length zs
    vs <- mapM (approx (fromIntegral k*n)) zs
    return $ Ring.sum vs
approx n (Mult  (Exact q) z) = liftM (q *) $ approx (roundUp (mup q * fromInteger n)) z
approx n (Mult  z         w) = do
    fBound <- magnitudeUpperBound z
    gBound <- magnitudeUpperBound w
    --R . putStrLn $ "k für-Erg " ++ show (roundUp $ fBound + gBound + 1)
    let k = roundUp $ fBound + gBound + 1
    R . putStrLn $ "fürs produkt(" ++ show n ++ ") brauche ich k=" ++ show k ++ ", also insges. " ++ show (n*k)
    liftM2 (*) (approx (n*k) z) (approx (n*k) w)
approx n (Ext   _         (MkApprox f)) = f n

magnitudeUpperBound :: (HasMUP ex) => AST ex -> R Rational
magnitudeUpperBound (Exact q) = return $ mup q
magnitudeUpperBound z         = liftM ((+1) . mup) $ approx 1 z
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f

simplify :: (Ring ex, Eq ex) => AST ex -> AST ex
simplify (Add (z : Add zs : rs)) = simplify $ Add (z:zs ++ rs)
simplify (Add [z]) = z
simplify (Add (Exact q : Exact r : zs)) = simplify $ Add (Exact (q+r) : zs)
simplify (Add (Exact q : zs)) | q == zero = Add zs
simplify (Add zs) | not (null zs), Exact q <- last zs = simplify $ Add $ Exact q : init zs
simplify (Mult (Exact q) (Exact r)) = Exact (q*r)
simplify (Mult (Exact q) (Mult (Exact r) z)) = Mult (Exact (q*r)) z
simplify (Mult (Exact q) z) | q == zero = zero
simplify (Mult (Exact q) z) | q == unit = z
simplify (Mult (Exact q) (Add zs)) = simplify $
    Add $ map (simplify . (Mult (Exact q))) zs
simplify (Mult z (Exact q)) = simplify $ Mult (Exact q) z
simplify z = z

fromBase :: ex -> AST ex
fromBase = Exact

-- Sei x komplex und n fest. Dann gilt stets:
--   |x| > 0 oder |x| < 1/n.
-- magnitudeZero n x gibt im ersten Fall False, im zweiten True zurück,
-- es gilt also:
--     magnitudeZero n x == False  ==>  |x| > 0,
-- aber die Umkehrung stimmt nicht.
magnitudeZeroTestR :: Nat -> Complex -> R Bool
magnitudeZeroTestR n (Exact f) = if f /= zero then return False else return True
magnitudeZeroTestR n z = do
    appr <- approx (2 * n) z
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
apartnessBound z = go 1
    where
    go i = do
	appr <- approx i z
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
recip' (Exact f) = Exact . fromJust . recip $ f
recip' z = Ext "recip'" $ MkApprox $ \n -> do
    n0 <- apartnessBound z
    let n' = halve $ n * n0^2
    liftM (fromJust . recip) $ approx n' z
    where
    halve i
	| i `mod` 2 == 0 = i `div` 2
	| otherwise      = i `div` 2 + 1
    -- Eigenschaft: halve i = Aufrundung(i / 2).

sqrt2 :: Complex
sqrt2 = Ext "sqrt2" $ MkApprox $ return . sqrt2Seq

goldenRatio :: Complex
goldenRatio = Ext "goldenRatio" $ MkApprox $ return . goldenRatioSeq
