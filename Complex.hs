{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, TypeFamilies, DeriveFunctor, FlexibleContexts, UndecidableInstances, EmptyDataDecls #-}
module Complex
    ( R(..), unsafeRunR
    , AST(..)
    , Complex, Real, Approx(..), QinC, QinR, approx
    , sqrt2, goldenRatio
    , fromBase
    , normUpperBoundR, magnitudeZeroTestR, traceEvals
    , recip') where

import Prelude hiding ((+), (*), (/), (-), (^), fromInteger, fromRational, recip, negate, Real)
import qualified Prelude as P
import Control.Monad (liftM, liftM2)
import ComplexRational
import qualified ComplexRational as ComplexRational
import Ring
import NormedRing
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
import Data.Ratio

-- | Der Typ der komplexen Zahlen.
type Complex = AST ComplexRational

-- | Der Typ der reellen Zahlen.
type Real    = AST Rational

-- | Elemente in /AST ex/ beschreiben Rechnungen, die man mit Werten aus /ex/,
-- den Ringoperationen (Addition und Multiplikation -- Negation kann man als
-- Multiplikation mit /-unit/ gewinnen) und zusätzlichen nur durch
-- Approximationsprozeduren gegebenen ideellen Elementen führen kann.
-- Gleichheit solcher Rechnungen ist natürlich nicht entscheidbar.
--
-- Beispielsweise ist /AST ComplexRational/ der Typ der komplexen Zahlen,
-- /AST Rational/ der der reellen Zahlen.
--
-- /AST ex/ kann man sich auch als die freie Ringerweiterung von /ex/ durch
-- Approximationsprozeduren vorstellen, und man könnte auch kürzer /AST ex/
-- durch
--
-- > data AST ex = Exact ex | Ext String (Approx ex)
--
-- definieren, denn da Prozeduren vom Typ /Approx ex/ beliebige Rechnungen
-- durchführen dürfen, können diese die in dieser Definition fehlenden
-- Konstruktoren emulieren.
--
-- Die hier gegebene Definition hat den Vorteil, dass man einige rudimentäre
-- Optimierungen vornehmen kann. Möchte man beispielsweise /x_1 + ... + x_n/
-- auf Genauigkeit /1\/N/ auswerten, benötigt man bei naiver Klammerung, /x_1 +
-- (x_2 + (x_3 + ...))/, eine Approximation von /x_n/ mit Genauigkeit
-- /1\/(2^n N)/. Bei balancierter Auswertung dagegen benötigt man von jedem
-- Summanden nur eine Approximation mit Genauigkeit /1\/(n N)/.
--
-- /Warnung/: /AST ex/ ist natürlich funktoriell in /ex/. Man kann jedoch
-- von einer allgemeinen Funktion /f/ nicht erwarten, dass
--
-- > approx n (fmap f ast)
--
-- auch eine /1\/n/-Approximation an /liftM f (approx n ast)/ liefert.
-- Damit das garantiert ist, muss /f/ Lipschitz mit Konstante /1/ sein,
-- wie beispielsweise /f = negate/ oder /f = conjugate/.
data AST ex
    = Exact ex                    -- ^ Einbettung exakter Werte
    | Add   [AST ex]              -- ^ Addition beliebig (endlich) vieler Terme
    | Mult  (AST ex) (AST ex)     -- ^ Multiplikation zweier Terme
    | Ext   String   (Approx ex)  -- ^ ideeller Wert, gegeben durch einen
                                  -- Approximationsalgorithmus. Die übergebene
                                  -- Zeichenkette kann als Bezeichner für
                                  -- Debugging-Zwecke dienen.
    deriving (Show,Functor)

-- | Monade für nicht-deterministische Approximationsalgorithmen.
newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)

-- | Typ der Approximationsalgorithmen mit Approximationen aus /ex/.
-- Dabei fordern wir folgende Bedingung (die sich aber leider in Haskell
-- nicht auf Typebene festschreiben ließe):
--
-- Mit einer positiven natürlichen Zahl /n/ aufgerufen, muss der
-- Approximationsalgorithmus eine Näherung produzieren, die von einer gewissen
-- festen Zahl Abstand echt kleiner als /1\/n/ hat.
newtype Approx ex = MkApprox { unApprox :: Nat -> R ex }
    deriving (Functor)

-- | /unsafeRunR m/ lässt die nicht-deterministische Operation /m/ laufen
-- und gibt ihr Ergebnis zurück.
--
-- Das ist im Allgemeinen gefährlich, denn jedes Mal, wenn das Ergebnis dann
-- ausgewertet wird, kann jeweils ein anderer Wert resultieren, da /m/ ja nicht
-- als deterministisch vorausgesetzt wird. Außerdem werden die Nebeneffekte in /m/
-- möglicherweise mehrmals ausgeführt.
--
-- Verwendet man 'unsafeRunR' in einer Funktion, muss man daher darauf achten,
-- dass der Rückgabewert nicht von den verschiedenen Ergebnissen von
-- 'unsafeRunR' abhängt -- sonst verletzt man das Prinzip der referentiellen
-- Transparenz.
unsafeRunR :: R a -> a
unsafeRunR = unsafePerformIO . runR

-- | /traceEvals name z/ ist semantisch nicht von /z/ zu unterscheiden,
-- gibt aber bei jeder Auswertung Debugging-Informationen auf die
-- Standardfehlerkonsole aus.
traceEvals :: (Show ex, NormedRing ex) => String -> AST ex -> AST ex
traceEvals name z = Ext name $ MkApprox $ \n -> do
    n' <- R $ evaluate n
    R $ hPutStrLn stderr $ printf "%-5s_%2d = ..." ("[" ++ name ++ "]") n'
    q  <- approx n' z
    q' <- R $ evaluate q
    R $ hPutStrLn stderr $ printf "%-5s_%2d = %s" ("[" ++ name ++ "]") n' (show q')
    return q'

instance Show (Approx ex) where
    show _ = "<<nondet>>"

instance (Ring ex, Eq ex) => Ring (AST ex) where
    z + w       = simplify $ Add [z,w]
    (*)         = (simplify .) . Mult
    negate      = simplify . Mult (Exact (negate unit))
    zero        = Add []
    unit        = Exact unit
    fromInteger = Exact . fromInteger

instance (HasConjugation ex, Eq ex, Eq (RealSubring ex)) => HasConjugation (AST ex) where
    type RealSubring (AST ex) = AST (RealSubring ex)
    conjugate (Exact q)   = Exact (conjugate q)
    conjugate (Add   zs)  = Add $ map conjugate zs
    conjugate (Mult  z w) = Mult (conjugate z) (conjugate w)
    conjugate (Ext   n f) = Ext n (fmap conjugate f)
    imagUnit = Exact imagUnit
    realPart (Exact q)   = Exact (realPart q)
    realPart (Add   zs)  = Add $ map realPart zs
    realPart (Mult  z w) = realPart z * realPart w - imagPart z * imagPart w
    realPart (Ext   n f) = Ext n (fmap realPart f)

instance (HasRationalEmbedding ex, Eq ex) => HasRationalEmbedding (AST ex) where
    fromRational = Exact . fromRational

instance (NormedRing ex, HasFloatingApprox ex, Eq ex) => HasFloatingApprox (AST ex) where
    unsafeApprox = unsafeApprox . unsafeRunR . approx 100

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

approx :: (NormedRing ex) => Integer -> AST ex -> R ex
approx _ (Exact q)           = return q
approx _ (Add   [])          = return zero
approx n (Add   (Exact q : zs)) = liftM (q +) $ approx n $ Add zs
approx n (Add   zs) = do
    let k = length zs
    vs <- mapM (approx (fromIntegral k*n)) zs
    return $ Ring.sum vs
approx n (Mult  (Exact q) z) = liftM (q *) $ approx (roundUp (normUpperBound q * fromInteger n)) z
approx n (Mult  z         w) = do
    fBound <- normUpperBoundR z
    gBound <- normUpperBoundR w
    --R . putStrLn $ "k für-Erg " ++ show (roundUp $ fBound + gBound + 1)
    let k = roundUp $ fBound + gBound + 1
    R . putStrLn $ "fürs produkt(" ++ show n ++ ") brauche ich k=" ++ show k ++ ", also insges. " ++ show (n*k)
    liftM2 (*) (approx (n*k) z) (approx (n*k) w)
approx n (Ext   _         (MkApprox f)) = f n

normUpperBoundR :: (NormedRing ex) => AST ex -> R Rational
normUpperBoundR (Exact q) = return $ normUpperBound q
normUpperBoundR z         = liftM ((+1) . normUpperBound) $ approx 1 z
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f

simplify :: (Ring ex, Eq ex) => AST ex -> AST ex
simplify (Add (z : Add zs : rs)) = simplify $ Add (z:zs ++ rs)
simplify (Add (Add zs : rs)) = simplify $ Add (zs ++ rs)
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
