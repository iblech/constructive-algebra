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
-- 1. Wenn (etwa in einem intuitionistischen Kontext) nicht klar ist, dass
-- die Zahl /z/ ein Minimalpolynom besitzt,
--
-- 2. wenn man das Minimalpolynom aus Effizienzgründen nicht bestimmen möchte
-- oder
--
-- 3. wenn man das Minimalpolynom nur zur Laufzeit als Wert vorliegen hat und
-- es nicht auf Typebene holen möchte. (Ist es statisch bekannt, so sollte man
-- besser das Modul "SimpleExtension" verwenden, welches richtige,
-- nicht-ideelle Körpererweiterungen bietet.)
{-# LANGUAGE TypeFamilies, FlexibleContexts, GeneralizedNewtypeDeriving, RankNTypes, FlexibleInstances #-}
module IdealExtension
    ( -- * Monade für ideelle Berechnungen
      Ideal, runIdeal, restart
    , -- * Typklasse für ideelle Körper
      IdealField(..)
    , idealEquals
      -- * Einfache endliche ideelle Körpererweiterungen
    , ISE(..)
    , IdealExtension.fromBase, adjointedRoot
    , canonRep
    , execISE, execISEwithAlgebraic
      -- * Beispiele
    , IdealExtension.demo
    ) where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/), (^), negate, recip, fromInteger)
import Control.Monad.Error
import Control.Monad.Reader
import Data.Maybe
import Text.Printf

import Algebraic as A
import Complex
import Debug
import Euclidean
import Field
import IntegralClosure
import NormedRing
import Polynomial as Poly
import Ring
import RingMorphism
import Smith (HasAnnihilatingPolynomials)

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
-- /k[X]\/(p)/ des Grundrings /k/. Das dynamische Moduluspolynom /p/
-- kann durch 'ask' der 'Ideal'-Monade erfragt werden.
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
        debug ("IdealExtension: restart!") $ do
        restart (d,s)

-- | Zu jedem gegebenen Zeitpunkt ist die ideelle Körpererweiterung /ISE k s/
-- ein Faktorring /k[X]\/(p)/ modulo eines dynamisch durch 'restart' änderbaren
-- Polynoms /p/.
--
-- Diese Funktion bestimmt zu einem Element des Faktorrings seinen kanonischen
-- Repräsentanten mittels Polynomdivision durch das herausgeteilte Polynom.
--
-- Nützlich ist das beispielsweise dann, wenn man im Körper /Q(x)/ rechnen
-- möchte, wobei /x/ eine algebraische Zahl ist, von der man nur ein normiertes
-- Polynom /f/ mit /f(x) = 0/ (nicht aber das Minimalpolynom) kennt.
--
-- Ist dann /y/ ein Element dieses Körpers (dargestellt als Element von /ISE k s/),
-- so bestimmt /canonRep y/ ein Polynom /g/ derart, dass /g(x) = y/.
--
-- /Kanonisch/ ist dieses Polynom /g/ nur in der Hinsicht, als dass es
-- bezüglich des aktuell bekannten Moduluspolynoms reduziert wurde. Abhängig
-- von zuvor ausgeführten Rechnungen in der 'Ideal'-Monade kann dieses aber
-- ein echter Faktor des Anfangsmodulus /f/ sein.
canonRep :: (Field k) => ISE k s -> Nondet (ISE k s) (Poly k)
canonRep (S g) = do
    f <- ask
    let (_,r) = quotRem g f
    return r

-- | Führt eine Berechnung in der 'Ideal'-Monade aus.
--
-- Bei Neustarts wird die übergebene Funktion genutzt, um zu entscheiden,
-- welcher von zwei gefundenen Faktoren des ursprünglichen Moduluspolynoms für
-- die neu aufgewickelte Rechnung verwendet werden soll.
execISE
    :: (Field k)
    => Poly k
        -- ^ Startwert fürs Moduluspolynom
    -> (Poly k -> Bool)
        -- ^ Funktionen, die zu einem gegebenen Polynom entscheidet, ob es
        -- auch als Moduluspolynom verwendet werden könnte
    -> (forall s. Nondet (ISE k s) a)
        -- ^ die auszuführende Berechnung
    -> a
        -- ^ das Ergebnis der (nötigenfalls mehrfach neugestarteten) Berechnung
execISE f phi m =
    case runReaderT m f of
        -- Hat die Berechnung ein Ergebnis produzieren können, ohne einen
        -- Neustart fordern zu müssen?
        Right x     -> x

        -- Wenn nicht, dann sind d und s Faktoren von f, wir müssen die
        -- Rechnung mit einem dieser Faktoren neustarten.
        Left  (d,s) ->
            if phi d
                then execISE d phi m
                else execISE s phi m

-- | /execISEwithAlgebraic z m/ führt die Berechnung /m/ im Körper /Q(z)/ aus.
-- Da wir das Minimalpolynom von /z/ nicht bestimmen wollen, realisieren wir
-- /Q(z)/ als ideellen Oberkörper /Q[X]\/(f)\/, wobei /f/ das durch die
-- Algebraizität von /z/ gegebene normierte Polynom mit /f(z) = 0/ ist.
--
-- In "Galois" wird das beispielsweise benutzt, um nach Berechnung eines
-- primitiven Elements /t/ zu gegebenen Zahlen /x/ und /y/ durch eine Rechnung
-- in /Q(t)/ ein nichttriviales Polynom /h/ mit /h(t) = x/ zu finden.
execISEwithAlgebraic
    :: ( RingMorphism m
       , Field      (Domain m)
       , HasAnnihilatingPolynomials (Domain m)
       , NormedRing (Domain m)
       , HasMagnitudeZeroTest (Codomain m)
       , PseudoField          (Codomain m)
       , HasDenseSubset (Codomain m)
       , NormedRing (DenseSubset (Codomain m))
       , Field      (DenseSubset (Codomain m))
       )
    => Alg m -> (forall s. Nondet (ISE (Domain m) s) a) -> a
execISEwithAlgebraic z m = execISE f phi m
    where
    f     = unNormedPoly . polynomial . unAlg $ z
    phi g = zero == A.eval z g

demo :: IO ()
demo = do
    let f = (iX^2 - fromInteger 2) * (iX - fromInteger 3)
        z = MkAlg $ MkIC Complex.sqrt2 $ MkNormedPoly f :: Alg QinR
    putStrLn $
        "Rechnungen im ideellen Oberkörper Q(sqrt(2)), wobei wir von sqrt(2)\n" ++
        "nur wissen wollen, dass es Nullstelle von\n\tf = " ++ show f ++ "\nist:"
    
    flip mapM_ [adjointedRoot - fromInteger 2, adjointedRoot - fromInteger 3] $ \u -> do
        printf "` Inverses von %s: %s\n"
            (show u) (show $ execISEwithAlgebraic z (idealRecip u))
    putStrLn $
        "Für die zweite Rechnung wurde dabei ein Neustart benötigt,\n" ++
        "denn 3 ist eine Nullstelle von f."
