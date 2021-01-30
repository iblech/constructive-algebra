-- | Dieses Modul stellt die komplexen Zahlen (und nebenbei auch die reellen
-- Zahlen) bereit.
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, TypeFamilies, DeriveFunctor, FlexibleContexts, UndecidableInstances, EmptyDataDecls, PatternGuards #-}
module Complex
    ( -- * Monade für nicht-deterministische Rechnungen
      R(..), unsafeRunR
      -- * Approximationsalgorithmen
    , Approx(..), HasDenseSubset(..), newInteractiveApprox, newInteractiveApprox'
      -- * Erweiterungen von Ringen durch approximativ gegebene Elemente
    , Complex, Real, AST(..)
    , fromBase
    , QinC, QinR, QIinC
    , normUpperBoundR, HasMagnitudeZeroTest(..)
    , PseudoField(..)
    , signum'
      -- * Debugging
    , traceEvals, logMaxEval
      -- * Beispiele
    , sqrt2, goldenRatio
    , Complex.demo
    )
    where

import Prelude hiding ((+), (*), (/), (-), (^), fromInteger, fromRational, recip, negate, Real, catch)
import Control.Monad (liftM, liftM2)
import Control.Exception
import Data.IORef
import Data.Maybe
import System.IO
import System.IO.Unsafe
import Text.Printf

import ComplexRational
import Field
import Nat
import NormedRing
import NumericHelper
import Ring
import RingMorphism

-- | Monade für nicht-deterministische Rechnungen von
-- Approximationsalgorithmen.
--
-- Wir verwenden dazu einfach die 'IO'-Monade, weil wir beliebige externe
-- Kommunikation (beispielsweise Nutzereingaben oder Zufallszahlen) erlauben
-- wollen.
--
-- Operationen, die den Kontrollfluss beeinflussen (wie beispielsweise
-- 'forkIO'), verbieten wir. (Denn was würde so ein Algorithmus bedeuten?)
newtype R a = R { runR :: IO a }
    deriving (Functor,Applicative,Monad)

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

-- | Typ der Approximationsalgorithmen mit Approximationen aus /ex/.
-- Dabei fordern wir folgende Bedingung (die sich aber leider in Haskell
-- nicht auf Typebene festschreiben lässt):
--
-- Es muss eine bestimmte Zahl /z/ geben, sodass der Algorithmus, mit einer
-- positiven natürlichen Zahl /n/ aufgerufen, eine Näherung an /z/ produziert,
-- deren Abstand zu /z/ echt kleiner als /n^(-1)/ ist.
--
-- Ansonsten ist der Approximationsalgorithmus keinen Beschränkungen
-- unterworfen. Insbesondere darf er beliebige nicht-deterministische Prozesse
-- anstoßen, und kann bei der wiederholten Fragen nach einer /n^(-1)/-Näherung
-- jedes Mal ein anderes Resultat liefern.
newtype Approx ex = MkApprox { unApprox :: PositiveNat -> R ex }
    deriving (Functor)

-- | Klasse für Räume, deren Punkte sich durch Elemente einer gewissen Teilmenge
-- beliebig genau approximieren lassen.
--
-- Damit man die Forderung der Approximation formulieren kann, muss man eigentlich
-- auf dem Typ /a/ eine Norm (oder Metrik) gegeben haben. Dann könnten wir aber unser
-- wichtigstes Beispiel, die komplexen Zahlen 'Complex', nicht mehr
-- unterstützen, denn die Ordnung auf Normen komplexer Zahlen (also gewissen reellen
-- Zahlen) ist nicht entscheidbar.
--
-- Möglicherweise könnte man dieses Problem durch eine bessere Definition
-- normierter Räume beheben.
class HasDenseSubset a where
    -- | Dicht liegende Teilmenge, durch die approximiert werden soll
    type DenseSubset a :: *

    -- | /approx n z/ soll eine Näherung von /z/ bestimmen, die vom wahren Wert im
    -- Betrag um weniger (<) als /n^(-1)/ abweicht. Wiederholte Auswertungen
    -- dürfen andere Näherungen berechnen.
    approx :: PositiveNat -> a -> R (DenseSubset a)

-- | Erzeugt einen interaktiven Approximationsalgorithmus, welcher Näherungen
-- dadurch produziert, indem er den Nutzer auf der Standardkonsole fragt.
newInteractiveApprox
    :: (Read ex)
    => ([(PositiveNat, ex)] -> Bool)
               -- ^ Funktion, die übergebene Genauigkeits/Wertepaare
               -- auf Konsistenz prüft, also prüft, ob diese Approximationen
               -- einer ideellen Zahl sein könnten
    -> String  -- ^ Name der Zahl (für den Nutzer)
    -> IO (Approx ex)
newInteractiveApprox areApproxsConsistent name = do
    val <- newIORef []
    return . MkApprox $ \n -> R $ do
        as@(~((n0,q0):_)) <- readIORef val
        -- Genügt die Genauigkeit des gemerkten Werts?
        if not (null as) && n0 >= n then return q0 else do
        -- Nein; den Benutzer fragen.
        let prompt = do
            putStr $ "Naeherung von " ++ name ++ " auf < 1/" ++ show n ++ ": "
            q <- readLn
            -- Konsistenzcheck
            let as' = (n,q) : as
            if areApproxsConsistent as'
                then writeIORef val as' >> return q
                else fail "Angegebene Approximation nicht konsistent mit vorherigen Werten!"
        let loop = do
            catch prompt $ \e -> do
                putStrLn $ "* Fehler: " ++ show (e :: IOException)
                loop
        loop

-- | Erzeugt wie 'newInteractiveApprox'' einen interaktiven
-- Approximationsalgorithmus, wobei als Konsistenzprüfung
--
-- > |x_n - x_m| <= 1/n + 1/m
--
-- verwendet wird. Diese ist noch zu schwach, aber die Methoden der
-- 'NormedRing'-Klasse erlauben keine Prüfung auf /</.
newInteractiveApprox' :: (Read ex, NormedRing ex) => String -> IO (Approx ex)
newInteractiveApprox' = newInteractiveApprox $ \as -> and $ do
    (n,q)   <- as
    (n',q') <- as
    return $ norm (q - q') (1/fromIntegral n + 1/fromIntegral n')

-- | Der Typ der komplexen Zahlen.
type Complex = AST ComplexRational

-- | Der Typ der reellen Zahlen.
type Real    = AST Rational

-- | Elemente in /AST ex/ beschreiben Rechnungen (abstract syntax trees), die
-- man mit Werten aus /ex/, den Ringoperationen (Addition und Multiplikation --
-- Negation kann man als Multiplikation mit /-unit/ gewinnen) und zusätzlichen nur
-- durch Approximationsprozeduren gegebenen ideellen Elementen führen kann. Die
-- Darstellung ist natürlich nicht eindeutig, und Gleichheit nicht entscheidbar.
--
-- Beispielsweise ist /AST ComplexRational/ der Typ der komplexen Zahlen,
-- /AST Rational/ der der reellen Zahlen -- zumindest wenn man äquivalente
-- Beschreibungen miteinander identifiziert.
--
-- /AST ex/ kann man sich auch als die freie Ringerweiterung von /ex/ durch
-- Approximationsprozeduren vorstellen, und man könnte auch kürzer /AST ex/
-- durch
--
-- > data AST' ex = Exact ex | Ext String (Approx ex)
--
-- definieren, denn da Prozeduren vom Typ /Approx ex/ beliebige Rechnungen
-- durchführen dürfen, können diese die in dieser Alternativdefinition fehlenden
-- Konstruktoren emulieren. Auch möglich wäre
--
-- > data AST'' ex = Ext String (Approx ex).
--
-- Die hier gegebene Definition hat zwei Vorteile. Zum einen können wir so
-- einige rudimentäre Optimierungen vornehmen: Möchte man beispielsweise
-- /x_1 + ... + x_n/ auf Genauigkeit /N^(-1)/ auswerten, benötigt man bei naiver
-- Klammerung, /x_1 + (x_2 + (x_3 + ...))/, eine Approximation von /x_n/ mit
-- Genauigkeit /(2^n N)^(-1)/. Bei balancierter Auswertung dagegen benötigt man von
-- jedem Summanden nur eine Approximation mit Genauigkeit /(n N)^(-1)/.
--
-- Zum anderen ist die Definition in der Praxis effizienter: Denn bei den
-- beiden Alternativdefinitionen häufen sich schon bei kurzen Rechnungen sehr
-- viele Approx-Objekte, welche Bezüge auf ihre Definitionsumgebung enthalten
-- und daher automatische Speicherbereinigung verhindern.
--
-- /Warnung/: Wenn man sich nur für die syntaktische Struktur interessiert,
-- ist /AST ex/ natürlich faktoriell in /ex/. Von einer allgemeinen Funktion /f/
-- kann man aber nicht erwarten, dass
--
-- > approx n (fmap f ast)
--
-- auch eine /n^(-1)/-Approximation an /liftM f (approx n ast)/ liefert.
-- Damit das garantiert ist, muss /f/ ein lipschitzstetiger Ringhomomorphismus
-- mit Lipschitzkonstante kleinergleich /1/ sein, wie beispielsweise
-- /f = conjugate/ oder /f = fromRational/.
data AST ex
    = Exact ex                    -- ^ Einbettung exakter Werte
    | Add   [AST ex]              -- ^ Addition beliebig (endlich) vieler Terme
    | Mult  (AST ex) (AST ex)     -- ^ Multiplikation zweier Terme
    | Ext   String   (Approx ex)  -- ^ ideeller Wert, gegeben durch einen
                                  -- Approximationsalgorithmus. Die
                                  -- Zeichenkette kann als Bezeichner für
                                  -- Debugging-Zwecke dienen.
    deriving (Show,Functor)

-- | Hebt exakte Werte vom Typ /ex/ in den Typ /AST ex/.
fromBase :: ex -> AST ex
fromBase = Exact

-- | Bezeichnung für die Einbettung der rationalen in die komplexen Zahlen
data QinC
instance RingMorphism QinC where
    type Domain   QinC = F Rational
    type Codomain QinC = Complex
    mor _ = Exact . fromRational . unF

-- | Bezeichnung für die Einbettung der rationalen in die reellen Zahlen
data QinR
instance RingMorphism QinR where
    type Domain   QinR = F Rational
    type Codomain QinR = Real
    mor _ = Exact . fromRational . unF

-- | Bezeichnung für die Einbettung der komplexrationalen in die komplexen Zahlen
data QIinC
instance RingMorphism QIinC where
    type Domain   QIinC = F ComplexRational
    type Codomain QIinC = Complex
    mor _ = Exact . unF

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
    conjugate (Ext   n f) = Ext ("conjugate(" ++ n ++ ")") (fmap conjugate f)
    imagUnit = Exact imagUnit
    realPart (Exact q)   = Exact (realPart q)
    realPart (Add   zs)  = Add $ map realPart zs
    realPart (Mult  z w) = realPart z * realPart w - imagPart z * imagPart w
    realPart (Ext   n f) = Ext ("realPart(" ++ n ++ ")") (fmap realPart f)
    imagPart (Exact q)   = Exact (imagPart q)
    imagPart (Add   zs)  = Add $ map imagPart zs
    imagPart (Mult  z w) = realPart z * imagPart w + imagPart z * realPart w
    imagPart (Ext   n f) = Ext ("imagPart(" ++ n ++ ")") (fmap imagPart f)

instance (HasRationalEmbedding ex, Eq ex) => HasRationalEmbedding (AST ex) where
    fromRational = Exact . fromRational

instance (NormedRing ex, HasFloatingApprox ex, Eq ex) => HasFloatingApprox (AST ex) where
    unsafeApprox = unsafeApprox . unsafeRunR . approx 100

instance (NormedRing ex) => HasDenseSubset (AST ex) where
    type DenseSubset (AST ex) = ex
    approx = approx'

approx' :: (NormedRing ex) => PositiveNat -> AST ex -> R ex

-- Einfachster Fall:
approx' _ (Exact q) = return q

-- Addition eines exakten Werts
approx' n (Add (Exact q : zs)) = liftM (q +) $ approx' n $ Add zs
-- Stelle der Prozess (z_i) eine Zahl i dar.
-- Dann gilt in der Tat: |(q + z_n) - (q + z)| = |z_n - z| < 1/n.

-- Addition beliebig (endlich) vieler Terme
approx' n (Add zs) = do
    let k = length zs
    vs <- mapM (approx' (fromIntegral k*n)) zs
    return $ Ring.sum vs
-- Seien die Zahlen z^1, ..., z^k durch (z_i^1), ... (z_i^k) dargestellt.
-- Dann gilt in der Tat: |z^1_(kn) + ... + z^k_(kn) - (z^1 + ... + z^k)| < k * 1/(nk) = 1/n.

-- Multiplikation mit einem exakten Wert
approx' n (Mult (Exact q) z)
    | k == 0    = return zero
    | otherwise = liftM (q *) $ approx' k z
    where k = roundUp (normUpperBound q * fromInteger n)
-- Sei z durch den Prozess (z_i) dargestellt.
-- Sei k = roundUp (normUpperBound q * fromInteger n).
-- Ist k = 0, so muss (wegen n >= 1 und der Eigenschaft von normUpperBound)
-- q = 0 gewesen sein.
-- Andernfalls gilt folgende Abschätzung:
-- |q z_k - q z| < normUpperBound q * 1/k <= 1/n.

-- Multiplikation zweier Terme
approx' n (Mult z w) = do
    zBound <- normUpperBoundR z
    wBound <- normUpperBoundR w
    let k = roundUp $ zBound + wBound + 1
    liftM2 (*) (approx' (n*k) z) (approx' (n*k) w)
-- Sei z durch den Prozess (z_i), w durch (w_i) dargestellt.
-- Sei k wie im Code. Dann gilt:
-- |z_(kn) w_(kn) - z w|
--   <= |z_(kn) w_(kn) - z_(kn) w| + |z_(kn) w - z w|
--   <= |z_(kn)| |w_(kn) - w| + |z_(kn) - z| |w|
--   <  (zBound + 1) 1/(kn) + 1/(kn) wBound
--   <= 1/n.

-- Auswertung einer Zahl, die durch einen Approximationsalgorithmus gegeben ist.
-- Das ist an dieser Stelle einfach, denn der Approximationsalgorithmus steht
-- in der Pflicht, eine geeignete Näherung zu konstruieren.
approx' n (Ext _ (MkApprox f)) = f n

-- | Vereinfacht einen gegebenen Syntaxbaum unter der Annahme, dass er aus
-- einem bereits vereinfachten Baum durch eine einzige Operation in der
-- Implementierung der Ring-Instanz hervorging.
simplify :: (Ring ex, Eq ex) => AST ex -> AST ex

-- Assoziativität ausnutzen
simplify (Add (z : Add zs : rs)) = simplify $ Add (z:zs ++ rs)
simplify (Add (Add zs : rs)) = simplify $ Add (zs ++ rs)
simplify (Add [z]) = z

-- Addition mit exakt gegebenen Summanden sofort durchführen
simplify (Add (Exact q : Exact r : zs)) = simplify $ Add (Exact (q+r) : zs)

-- Addition von 0
simplify (Add (Exact q : zs)) | q == zero = simplify $ Add zs

-- Kommutativität (und Assoziativität) ausnutzen, um die Addition mit
-- exakten Werten von rechts zu vereinfachen
simplify (Add zs) | not (null zs), Exact q <- last zs = simplify $ Add $ Exact q : init zs

-- Multiplikation exakter Werte
simplify (Mult (Exact q) (Exact r)) = Exact (q*r)
simplify (Mult (Exact q) (Mult (Exact r) z)) = simplify $ Mult (Exact (q*r)) z

-- Multiplikation mit 0 und 1 vereinfachen
simplify (Mult   (Add []) _)             = zero
simplify (Mult _ (Add []))               = zero
simplify (Mult (Exact q)  _) | q == zero = zero
simplify (Mult (Exact q)  z) | q == unit = z

-- Multiplikation einer exakt gegebenen Zahl mit einer Summe
simplify (Mult (Exact q) (Add zs)) = simplify $
    Add $ map (simplify . (Mult (Exact q))) zs

-- Kommutativität ausnutzen, um Multiplikation mit exakten Werten von rechts
-- ebenfalls zu vereinfachen
simplify (Mult z (Exact q)) = simplify $ Mult (Exact q) z

-- Sonst.
simplify z = z

-- | Bestimmt eine obere Schranke (im Sinn von '<') für den Betrag der
-- gegebenen Zahl.
--
-- Mehrmalige Aufrufe dieser Funktion können verschiedene obere Schranken
-- produzieren.
normUpperBoundR :: (NormedRing ex) => AST ex -> R Rational
normUpperBoundR (Exact q) = return $ normUpperBound q
normUpperBoundR z         = liftM ((+1) . normUpperBound) $ approx 1 z
-- Sei z_1 eine 1/1-Näherung von z.
-- Dann gilt: |z| <= |z_1| + |z - z_1| < |z_1| + 1.

-- | Wie bei 'HasDenseSubset' müssten wir eigentlich einen geeigneten
-- Metrik- oder Normkontext fordern.
class (Ring a) => HasMagnitudeZeroTest a where
    -- | Sei /z/ eine Zahl. Dann ist nicht entscheidbar, ob /|z| = 0/ oder
    -- ob nicht /|z| = 0/. Für festes /n >= 1/ gilt aber stets:
    --
    -- > |z| > 0  oder  |z| < 1/n,
    --
    -- wobei das /oder/ natürlich kein /entweder oder/ ist. Gibt
    -- 'magnitudeZeroTestR' /False/ zurück, so liegt der erste Fall vor,
    -- andernfalls der zweite.
    magnitudeZeroTestR :: PositiveNat -> a -> R Bool

-- | Klasse für Ringe, die im Sinne folgender schwächeren Definition Körper sind:
--
-- > Für alle /x/, die von Null entfernt sind, gibt es ein Inverses von /x/.
--
-- Da wir das Konzept der Entferntheit nutzen, müssten wir (wie bei
-- 'HasDenseSubset' genauer erläutert) eigentlich einen geeigneten Metrik-
-- oder Normkontext fordern.
class (Ring a) => PseudoField a where
    -- | Sei /z/ von null entfernt, es existiere also eine rationale Zahl /q/ mit
    -- /|z| >= q > 0/. Dann soll /recip' z/ die Zahl /z^(-1)/ darstellen.
    -- 'recip'' muss sonst nicht definiert sein.
    recip' :: a -> a

instance (NormedRing a, Eq a) => HasMagnitudeZeroTest (AST a) where
    magnitudeZeroTestR _ (Exact q) = return $ q == zero
    magnitudeZeroTestR n z = do
        q <- approx (2 * n) z
        return $ norm q (1 / (2*fromInteger n))
-- Korrektheitsbeweis:
-- Gelte |z_(2n)| <= 1/(2n). Dann |z| <= |z_(2n)| + |z - z_(2n)| < 1/n.
-- Gelte |z_(2n)| >= 1/(2n). Dann |z| >= |z_(2n)| - |z_(2n) - z| > 0.

-- | Sei die gegebene Zahl /z/ von null entfernt, existiere also eine rationale
-- Zahl /q/ mit /|z| >= q > 0/. Dann liefert /apartnessBound z/ eine positive
-- natürliche Zahl /n/ mit
--
-- > |z_n| > 1/N für alle n >= N  und  |z| > 2/N,
--
-- wobei /z_n/ für jede mögliche /n^(-1)/-Näherung von /z/ steht.
apartnessBound :: (Field ex, NormedRing ex) => AST ex -> R PositiveNat
apartnessBound z = go 10
    -- go 1 ist semantisch genauso gut. go 10 führt aber in der Praxis zu viel
    -- besseren Laufzeiten.
    where
    go i = do
	q <- approx i z
        -- Ist |q| >= 3/i?
	if q /= zero && norm (unit/q) (fromInteger i / 3)
	    then return i
	    else go (2*i)
            -- /go (2*i)/ ist der Praxis (zum Beispiel für
            -- /cf (goldenRatio + sqrt2)/) schneller als /go (i+1)/.
            -- Semantisch ist beides okay.
-- Zur Korrektheit und Terminierung:
-- a) |z_N| >= 3/N  ==>  |z_n| > 1/N f.a. n >= N  und  |z| > 2/N.
-- b) z # 0  ==>  es gibt ein N wie in a)
--
-- Zu a):
-- |z_n| >= |z_N| - |z_N - z_n| > 3/N - (1/N + 1/n) >= 1/N.
-- |z|   >= |z_N| - |z_N - z|   > 2/N - 1/N = 1/N.
--
-- Zu b):
-- Sei |z| >= q > 0. Sei q >= 1/k, k >= 1.
-- Setze N := 4k.
-- Dann gilt: |z_N| >= |z| - |z - z_N| > 1/k - 1/(4k) = (4k-1)/(4k) >= 3/N.

instance (Field ex, NormedRing ex) => PseudoField (AST ex) where
    recip' (Exact q) = Exact . fromJust . recip $ q
    recip' z = Ext "recip'" $ MkApprox $ \n -> do
        n0 <- apartnessBound z
        let n' = halve $ n * n0^2
        liftM (fromJust . recip) $ approx n' z
        where
        halve i
            | i `mod` 2 == 0 = i `div` 2
            | otherwise      = i `div` 2 + 1
        -- Eigenschaft: halve i = Aufrundung(i / 2).
    -- Beweis:
    -- |1/z_n' - 1/z| = |z - z_n'| / (|z_n'| |z|) <
    -- n' = Aufr(n/2 n0^2) >= n0? 

-- | Bestimmt das Vorzeichen einer von null entfernten reellen Zahl.
-- Die Auswertung von /signum' zero/ terminiert nicht.
signum' :: Real -> Ordering
signum' x = unsafeRunR . liftM (`compare` zero) $ go 1
    where
    go i = do
        appr <- approx i x
        if abs appr >= 1/fromInteger i
            then return appr
            else go (i + 1)
-- Beweis:
-- Zunächst ist klar, dass ein Index i wie gesucht existiert (etwa
-- i <- apartnessBound x). Es gilt dann also |x - x_i| < 1/i.
-- Sollte nun x_i positiv sein, so ist x_i also >= 1/i und damit x > 0.
-- Sollte x_i negativ sein, gilt x_i <= -1/i und daher x < 0.

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

-- | /logMaxEval z/ gibt ein Paar /(var, z')/ zurück, wobei /z'/ semantisch
-- nicht von /z/ zu unterscheiden ist, aber seine maximalen Approximationsgesuche
-- in der veränderlichen Variablen /var/ speichert.
logMaxEval :: (NormedRing ex) => AST ex -> IO (IORef PositiveNat, AST ex)
logMaxEval z = do
    maxNvar <- newIORef 0
    let z' = Ext "" $ MkApprox $ \n -> do
        R $ modifyIORef maxNvar (`max` n)
        approx n z
    return (maxNvar, z')

sqrt2 :: Real
sqrt2 = Ext "sqrt2" $ MkApprox $ return . sqrt2Seq

goldenRatio :: Real
goldenRatio = Ext "goldenRatio" $ MkApprox $ return . goldenRatioSeq

demo :: IO ()
demo = do
    (maxNvar, sqrt2') <- logMaxEval sqrt2
    printInfo "sqrt2"                   sqrt2'
    printInfo "goldenRatio"             goldenRatio
    printInfo "sqrt2^2 + 3*goldenRatio" $ sqrt2'^2 + fromInteger 3 * goldenRatio
    printInfo "(sqrt2 * goldenRatio)^3" $ (sqrt2' * goldenRatio)^3

    maxN <- readIORef maxNvar
    printf "Bei diesen Berechnungen maximal benötigte Approximation von sqrt2: 1/%d\n" maxN

    where
    printInfo name z = do
        printf "Approximationen von %s:\n" name :: IO ()
        flip mapM_ [1,10,100,1000,10000] $ printApproxs z
        putStrLn ""
    printApproxs z n = do
        q <- runR $ approx n z
        printf "` auf Genauigkeit < 1/%-6s %-10s ~~ %s\n"
            (show n ++ ":") (show q) (show (unsafeApprox q))
