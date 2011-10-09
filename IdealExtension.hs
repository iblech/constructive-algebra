-- | Dieses Modul stellt ideelle Körper und ideelle Körpererweiteungen
-- bereit.
--
-- Ein ideeller Körper ist ein Ring, der das Körperaxiom
--
-- > für alle x gilt: entweder x = 0 oder x ist invertierbar
--
-- /beinahe/ erfüllt: Für jedes /x/ des ideellen Körpers gilt
-- entweder /x = 0/, oder /x/ ist invertierbar, oder aber der ideelle Körper
-- muss durch einen verfeinerten ideellen Körper ersetzt werden, in dem
-- dann einer der beiden ersten Fälle eintritt.
--
-- Bezüglich endlich vieler Elemente verhält sich also ein ideeller Körper
-- wie ein richtiger Körper.
--
-- Ist beispielsweise /z/ eine algebraische Zahl und /p/ ein normiertes
-- Polynom, welches /z/ als Nullstelle besitzt aber nicht notwendigerweise
-- das Minimalpolynom von /z/ ist, so kann man /Q[X]\/(p)/ als ideelle 
-- Körpererweiterung von /Q/ ansehen:
--
-- Möchte man ein Element /[f]/ auf Invertierbarkeit testen, muss man den ggT /d/
-- von /f/ und /p/ betrachten. Ist dieser ein konstantes Polynom, ist /[f]/
-- invertierbar; ist er assoziiert zu /p/, so ist /f/ also ein Vielfaches von /p/,
-- womit /[f] = 0/ ist; und sonst hat man in /d/ einen echten Faktor von /p/ gefunden.
--
-- In diesem Fall muss man /p/ durch diesen Faktor (oder seinem Komplement,
-- falls /z/ nicht Nullstelle von /d/ ist) ersetzen und die Rechnung
-- wiederholen.
--
-- Nützlich sind ideelle Erweiterungen in folgenden Situationen:
--
-- 1. Wenn (etwa in einem intuitionistischen Kontext) nicht klar ist, dass+
-- die Zahl /z/ ein Minimalpolynom besitzt,
--
-- 2. wenn man das Minimalpolynom aus Effizienzgründen nicht bestimmen möchte
-- oder
--
-- 3. wenn man das Minimalpolynom nur zur Laufzeit als Wert vorliegen hat und
-- es nicht auf Typebene holen möchte.
{-# LANGUAGE TypeFamilies, FlexibleContexts, GeneralizedNewtypeDeriving, RankNTypes, FlexibleInstances #-}
module IdealExtension where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/), (^), negate, recip, fromInteger)
import Ring
import Field
import Polynomial as Poly
import Euclidean
import Control.Monad.Reader
import Control.Monad.Error
import Debug.Trace
import Algebraic as A
import IntegralClosure
import Complex
import ZeroRational
import Data.Maybe

-- | Monade für /ideelle Berechnungen/, also solche, die eine Umgebung vom
-- Typ /k/ benötigen (in der Anwendung ideeller einfacher Körpererweiterungen
-- etwa das Moduluspolynom) und entweder ein Ergebnis produzieren oder
-- mit einem Fehler vom Typ /k'/ abbrechen.
--
-- Dieser sollte konstruktive Information enthalten, sodass ein Neustart der
-- Berechnung mit einer verfeinerten Umgebung nicht an derselben Stelle
-- abbrechen muss.
type Ideal k k' = ReaderT k (Either k')

-- | /restart x/ ist eine Aktion, die zum Abbruch der Berechnung führt und die
-- übergebene Information /x/ dem Aufrufer (etwa 'runIdeal') zur Verfügung
-- stellt.
restart :: k' -> Ideal k k' a
restart x = ReaderT (const $ Left x)

-- | /runIdeal m x0 f/ lässt die Berechnung /m/ mit der anfänglichen Umgebung
-- /x0/ laufen. Bricht diese nicht ab, wird das Ergebnis zurückgegeben.
-- Wenn sie andernfalls mit einer Fehlerinformation /y/ abbricht, wird sie
-- rekursiv mit der verfeinerten Umgebung /f y/ neugestartet.
--
-- Um Terminierung zu gewährleisten, sollte /f/ die Umgebung auch tatsächlich
-- derart verfeinern, dass nur endlich viele Neustarts erforderlich sind.
runIdeal :: Ideal k k' a -> k -> (k' -> k) -> a
runIdeal m x0 f = case runReaderT m x0 of
    Left  y -> runIdeal m (f y) f
    Right a -> a

-- | Klasse für ideelle Körper /a/. Das sind Ringe, in denen die Inversenbildung
-- anders als in richtigen Körpern keine pure Operation mit Rückgabetyp /Maybe a/
-- (entweder die Nullheit signalisierend oder das Inverse angebend) ist,
-- sondern Werte in einer Monade annimmt.
--
-- Das wichtigste Beispiel ist der Datentyp /ISE k s/, dessen
-- 'idealRecip'-Operation Werte in der 'Ideal'-Monade annimmt und so Neustarts
-- der Berechnung zulässt.
class (Ring a, Monad (Nondet a)) => IdealField a where
    -- | Monade, in der 'idealRecip' seine Werte annimmt.
    type Nondet a :: * -> *

    -- | /idealRecip x/ bestimmt, ob /x/ entweder null (Rückgabewert
    -- /Nothing/) oder invertierbar (Rückgabewert /Just y/, mit /y/ dem
    -- Inversen von /x/) ist. Falls dazu nötig, dürfen beliebige
    -- monadische Aktionen durchgeführt werden.
    idealRecip :: a -> (Nondet a) (Maybe a)

-- | /idealEquals x y/ bestimmt, ob /x/ und /y/ gleich sind.
--
-- Dazu untersuchen wir das Element /x - y/ auf Invertierbarkeit.
idealEquals :: (IdealField a) => a -> a -> Nondet a Bool
idealEquals x y = liftM isNothing $ idealRecip (x - y)

-- | Datentyp für die Elemente einer einfachen ideellen Ringerweiterung
-- /k[X]\/(p)/ des Grundrings /k/.
--
-- Den Phantomtyp /s/ verwenden wir, um unabsichtliche Vermischungen von
-- Elementen verschiedener ideeller Erweiterungen zu verhindern.
newtype ISE k s = S (Poly k)
    deriving (Show,Ring,HasRationalEmbedding)

-- | Hebt ein Element des Grundrings in die ideelle Erweiterung hoch.
fromBase :: k -> ISE k s
fromBase = S . Poly.fromBase

-- | Liefert das Element /[X]/ der ideellen Erweiterung /k[X]\/(p)/, also die
-- künstliche Nullstelle von /p/.
adjointedRoot :: (Field k) => ISE k s
adjointedRoot = S iX

-- Nötig, um die importierte Monadinstanz von /Either (Poly k)/ nutzen zu
-- können.
instance Error (Poly k, Poly k) where
    strMsg msg = error $ "Error (Poly k): " ++ show msg

instance (Field k) => IdealField (ISE k s) where
    -- Die Umgebung enthält das aktuelle Moduluspolynom /p/.
    -- In einem etwaigen Fehlerfall geben wir zwei komplementäre echte Faktoren
    -- von /p/ zurück.
    type Nondet (ISE k s) = Ideal (Poly k) (Poly k, Poly k)
    idealRecip (S g) = do
        -- Vor.: f nicht null.
        p <- ask
        let (u,v,s,_) = gcd p g; d = u*p + v*g

        -- Ist d konstant, so erhalten wir aus d einen Ausdruck fürs Inverse.
        if degree d == 0        then return . Just . S $ fromJust (recip (leadingCoeff d)) .* v else do
        -- Ist g ein Vielfaches von p, ist die Sache auch klar: Das von g
        -- repräsentierte Element ist null.
        if degree d == degree p then return Nothing else do

        -- Andernfalls haben wir die echten Faktoren d uns s von p gefunden;
        -- wir müssen die Rechnung abbrechen.
        trace ("restart!") $ do
        restart (d,s)

canonISE :: (Field k) => ISE k s -> Nondet (ISE k s) (Poly k)
canonISE (S g) = do
    f <- ask
    let (q,r) = quotRem g f
    return r

runISE
    :: (Field k)
    => Poly k -> (Poly k -> Bool)
    -> (forall s. Nondet (ISE k s) a)
    -> a
runISE f phi m =
    case runReaderT m f of
        Right x     -> x
        Left  (d,s) ->
            if phi d
                then runISE d phi m
                else runISE s phi m

ex :: Nondet (ISE Rational s) (Maybe (ISE Rational s))
ex = do
    Just x <- idealRecip $ adjointedRoot - unit
    let z = adjointedRoot^2 - unit - unit
    let y = (x * (adjointedRoot - unit) - unit) * z
    idealRecip z

exF :: Poly Rational
exF = iX^3 - fromInteger 2

runISEwithAlgebraic :: Alg QinC -> (forall s. Nondet (ISE Rational s) a) -> a
runISEwithAlgebraic z = runISE f phi
    where
    f     = unNormedPoly . fmap unF . polynomial . unAlg $ z
    phi g = zero == A.eval z g

--exRun' = exRun (head $ rootsA $ iX^3 - fromInteger 1)
