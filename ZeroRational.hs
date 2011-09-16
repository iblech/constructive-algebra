-- | Dieses Modul implementiert den Fundamentalsatz der Algebra, stellt also
-- eine Funktion 'roots' zur Verfügung, die zu einem gegebenen Polynom seine
-- Nullstellen berechnet.
--
-- Das Verfahren funktioniert wie folgt: Ausgehend von einem großen Rechteck,
-- welches aufgrund einer a-priori-Abschätzung alle Nullstellen enthalten muss,
-- zählen wir mithilfe von Sturmketten die Anzahl der Nullstellen auf den
-- Kanten und den vier Teilrechtecken. Teile ohne Nullstellen werden verworfen,
-- auf den anderen wird das Verfahren rekursiv fortgesetzt.
-- In jedem Schritt halbiert sich also die Größe der einzelnen Suchzellen.
--
-- Das Verfahren entstammt folgendem Artikel:
--
-- [1] Michael Eisermann. The Fundamental Theorem of Algebra made effective:
-- an elementary real-algebraic proof via Sturm chains. 2009.
-- arXiv:0808.0097v2 [math.AG]
{-# LANGUAGE PatternGuards, TupleSections #-}
module ZeroRational
    ( signChanges, signChanges'
    , sturmChain, index
    , rootsOnSegment, windingNumber, rootsOnRectangle
    , Cell(..), midpoint
    , divide, cauchyRadius, roots
    , subdivisions, newton, newtonPrecondition
    ) where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, quotRem, gcd)
import Polynomial
import Ring
import Field
import Complex
import Algebraic hiding (eval)
import Polynomial as Poly
import Control.Monad
import Euclidean
import ComplexRational
import IntegralClosure hiding (eval)
import Debug.Trace
import Data.List hiding (sum)
import System.IO.Unsafe
import Data.IORef
import qualified Data.Map as M

-- | Zählt die Anzahl von Vorzeichenwechseln einer endlichen Liste von Zahlen
-- eines geordneten Rings.  Wechsel von/auf null zählen /1\/2/.
signChanges :: (OrderedRing a) => [a] -> Rational
signChanges xs = sum $ map f (pairs xs)
    where
    pairs []       = []
    pairs [_]      = []
    pairs (x:y:zs) = (x,y) : pairs (y:zs)
    f (x,y)
        | (x*y) `compare` zero == LT = 1
        | x == zero && y /= zero     = 1/2
        | x /= zero && y == zero     = 1/2
        | otherwise                  = 0

signChanges' :: (OrderedRing a) => a -> a -> [Poly a] -> Rational
signChanges' a b ps = signChanges (map (eval a) ps) - signChanges (map (eval b) ps)

-- | Berechnet zu einer rationalen Funktion /R\/S/, wobei /R/ und /S/ Polynome
-- sind, ihre zugehörige Sturmkette. Dabei soll der Grad von /R/ kleinergleich
-- dem von /S/ sein, sonst wird eine Laufzeitausnahme geworfen.
sturmChain :: (Field a) => Poly a -> Poly a -> [Poly a]
sturmChain r s
    | degree r > degree s = error "sturmChain: Zählergrad > Nennergrad"
    | otherwise           = euclidChain r s

-- | Bestimmt zu einer rationalen Funktion /R\/S/ und Intervallgrenzen /a/ und
-- /b/ ihren Cauchyindex.
--
-- Zwei Spezialfälle des Index sind wichtig: Der Index von /f'\/f/, wobei
-- /f/ ein Polynom und /f'/ seine Ableitung bezeichnet, ist die Anzahl der
-- Nullstellen von /f/ auf /[a,b]/, wobei die Nullstellen ohne Vielfachheit
-- gezählt werden und Nullstellen in den Randpunkten /a/ und /b/ /1\/2/
-- beitragen.
--
-- Der Index von /Re γ \/ Im γ/ ist das doppelte der Windungszahl der
-- Einschränkung des polynomiellen Wegs /γ/ auf das Segment /[a,b]/ der
-- komplexen Zahlenebene, siehe 'windingNumber'.
index :: (Field a, OrderedRing a) => a -> a -> Poly a -> Poly a -> Rational
index a b r s
    | degree r <= degree s = signChanges' a b (sturmChain r s)
    | otherwise            = signChanges' a b [r,s] - index a b s r

-- | /rootsOnSegment z0 z1 p/ zählt die Anzahl der Nullstellen des
-- Polynoms /p/ im Segment /[z0,z1]/ der komplexen Ebene. Dabei muss /f/
-- keine bestimmten Voraussetzungen erfüllen.
--
-- Die Nullstellen werden ohne Vielfachheit gezählt, wobei Nullstelen auf
-- den Ecken /1\/2/ beitragen.
--
-- Siehe: Korollar 3.8 von [1].
rootsOnSegment :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
rootsOnSegment z0 z1 p = index zero unit (derivative f) f
    where
    gamma = compose p alpha
    alpha = fromComplexRational z0 + iX * fromComplexRational (z1 - z0)
    p1    = realPart gamma
    p2    = imagPart gamma
    f     = let (u,v,_,_) = gcd p1 p2 in u*p1 + v*p2

-- | /windingNumber z z' p/ berechnet die algebraische Windungszahl des
-- Wegs /γ/ mit /γ(t) = p(z + t (z' - z))/ um den Ursprung. Dazu berechnen wir
-- Sturmketten von Real- und Imaginärteil von /γ/. Anders als bei analytischen
-- Definitionen der Windungszahl sind Nullstellen von /γ/ zugelassen.
--
-- Siehe: Abschnitt 4.3 in [1].
windingNumber :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
windingNumber z z' p
    = index zero unit (realPart gamma) (imagPart gamma) / 2
    where
    gamma = compose p alpha
    alpha = fromComplexRational z + iX * fromComplexRational (z' - z)

-- | /rootsOnRectangle z0 z1 p/ zählt die Anzahl der Nullstellen von /p/ in
-- dem Rechteck, dessen zwei gegenüberliegende Eckpunkte durch /z0/ und /z1/
-- gegeben sind. Das Polynom /p/ darf dabei keine Nullstellen auf den
-- vier Eckpunkten des Rechtecks besitzen, kann sonst aber beliebig sein.
--
-- Die Nullstellen im Inneren des Rechtecks zählen mit ihrer Vielfachheit,
-- die auf den Kanten mit der Hälfte ihrer Vielfachheit. Mithilfe von
-- 'rootsOnSegment' kann man separat die Anzahl der Nullstellen auf den
-- Kanten bestimmen und so auch ermitteln, wie viele Nullstellen im Inneren
-- liegen.
--
-- Siehe: Theorem 5.1 von [1].
rootsOnRectangle :: ComplexRational -> ComplexRational -> Poly ComplexRational -> Rational
rootsOnRectangle z0 z1 p = sum
    [ windingNumber (ri z0 z0) (ri z1 z0) p
    , windingNumber (ri z1 z0) (ri z1 z1) p
    , windingNumber (ri z1 z1) (ri z0 z1) p
    , windingNumber (ri z0 z1) (ri z0 z0) p
    ]

ri :: ComplexRational -> ComplexRational -> ComplexRational
ri z w = realPart z :+: imagPart w

-- | Datentyp für 0-Zellen (Punkte), 1-Zellen (Liniensegmente) und 2-Zellen
-- (Rechtecke).
data Cell
    = Cell0 ComplexRational                  -- ^ Koordinaten des Punkts
    | Cell1 ComplexRational ComplexRational  -- ^ Anfangs- und Endpunkt
    | Cell2 ComplexRational ComplexRational  -- ^ Paar gegenüberliegender Ecken
    deriving (Show,Eq)

-- | Liefert den Mittelpunkt einer Zelle.
midpoint :: Cell -> ComplexRational
midpoint (Cell0 z0)    = z0
midpoint (Cell1 z0 z1) = (z0 + z1) / fromInteger 2
midpoint (Cell2 z0 z1) = (z0 + z1) / fromInteger 2

-- | Iterationsschritt des Unterteilungsverfahrens.
-- Bestimmt zu einem gegebenen Polynom und einer Zelle diejenigen Unterzellen
-- (also die beiden Hälften sowie dem Mittelpunkt einer 1-Zelle bzw.
-- die vier Teilrechtecke und vier Teilkanten einer 2-Zelle), die Nullstellen
-- des Polynoms enthalten.
--
-- Sollte schon eine Nullstelle gefunden worden sein, wird diese abdividiert,
-- sodass zukünftige Iterationen wegen des geringeren Grads effizienter
-- ablaufen können.
--
-- Die genauen Voraussetzungen sind:
--
-- (A) Das Polynom besitzt keine Nullstellen auf den Eckpunkten der 1- und
--     2-Zellen.
--
-- (B) Das Polynom ist separabel.
--
-- Von 'divide' wird dann eine Liste geliefert, die folgende Bedingungen
-- erfüllt:
--
-- (1) Die obigen beiden Voraussetzungen sind für die Teilzellen wieder erfüllt.
--
-- (2) Jede Zelle enthält in ihrem Inneren mindestens eine Nullstelle des
--     Inneren der Ausgangszelle.
--
-- (3) Jede Nullstelle des Inneren der Ausgangszelle liegt in einem Inneren der
--     Unterzellen.
--
-- Dabei ist das Innere einer 0-Zelle sie selbst, das einer 1- und
-- 2-Zelle sie ohne ihren topologischen Rand.
--
-- Speziell werden daher für auf dem Rand einer 2-Zelle liegenden Nullstellen
-- keine Unterzellen generiert. (Sonst könnte man mehrere Aufrufe von 'divide'
-- nicht gut zusammenführen, da dieselbe Nullstelle in mehreren Zellen liegen
-- könnte.)
--
-- Bei sukzessiver Anwendung von 'divide' erhält man irgendwann genau so viele
-- Zellen, wie der Grad vom Polynom vorgibt. Sobald dieser Zustand erreicht
-- ist, wird jede Zelle jeweils zu genau einer Unterzelle verfeinert: Denn
-- wegen Bedingung (3) kann eine Zelle nicht verschwinden, und wegen
-- Bedingung (2) kann eine Zeile nicht mehr als eine Nullstellen
-- beinhaltende Unterzellen enthalten, da der Grad des Polynoms keine weiteren
-- Nullstellen erlaubt.
divide :: Poly ComplexRational -> Cell -> [(Poly ComplexRational, Cell)]

-- Trivialer Fall: Wir haben zu prüfen, ob die gegebene 0-Zelle, also ein
-- einzelner Punkt, Nullstelle ist.
divide p (Cell0 z0)
    | eval z0 p == zero = [(p, Cell0 z0)]
    | otherwise         = []

-- Im Fall einer 1-Zelle prüfen wir zunächst, ob der Mittelpunkt der Zelle
-- eine Nullstelle ist.
divide p c@(Cell1 z0 z1)
    -- Wenn ja, dividieren wir diese ab und wiederholen uns. Das ist wichtig,
    -- denn sonst wäre Ziel (3) und Voraussetzung (A) verletzt.
    -- Nach der Separabilitätsvoraussetzung (B) genügt es, die Nullstelle ein
    -- einziges Mal abzudividieren.
    | eval mid p == zero =
        (p, Cell0 mid) : divide (fst $ p `quotRem` (iX - fromComplexRational mid)) c
    | otherwise          = rs
    where
    mid = midpoint c
    n1  = rootsOnSegment z0  mid p
    n2  = rootsOnSegment mid z1  p
    rs  = concat
        [ guard (n1 /= 0) >> return (p, Cell1 z0  mid)
        , guard (n2 /= 0) >> return (p, Cell1 mid z1)
        ]

-- Im Fall einer 2-Zelle prüfen wir zunächst, ...
divide p c@(Cell2 z0 z1)
    -- ...ob der Mittelpunkt Nullstelle ist.
    -- Denn wenn ja, dürfen wir nicht 'rootsOnRectangle' verwenden!
    | eval mid p == zero =
        (p, Cell0 mid) : divide (fst $ p `quotRem` (iX - fromComplexRational mid)) c

    -- Als nächstes prüfen wir, ob die Mittelpunkte der vier äußeren Kanten
    -- der 2-Zelle Nullstellen sind. Das hat denselben Grund; aber anders als
    -- beim Mittelpunkt dürfen wir hier keine 0-Zelle für die gefundene
    -- Nullstelle ausgeben: Denn diese liegt ja auf dem Rand, nach Ziel (2)
    -- dürfen solche nicht emittiert werden.
    | (v:_) <- midedgeZeros = divide (fst $ p `quotRem` (iX - fromComplexRational v)) c

    -- Nun können wir also annehmen, dass keine der insgesamt neun Eckpunkte
    -- Nullstellen sind; also dürfen wir 'rootsOnSegment' und
    -- 'rootsOnRectangle' zum Zählen verwenden. Wir emittieren jede der
    -- vier neuen Kanten und der vier neuen Teilrechtecke, die in ihrem Inneren
    -- eine Nullstelle besitzen.
    | otherwise = map (p,) $ concat
        [ guard (n1245 /= 0) >> return (Cell2 u1 u5)
        , guard (n2356 /= 0) >> return (Cell2 u2 u6)
        , guard (n4578 /= 0) >> return (Cell2 u4 u8)
        , guard (n5689 /= 0) >> return (Cell2 u5 u9)
        , guard (n25   /= 0) >> return (Cell1 u2 u5)
        , guard (n56   /= 0) >> return (Cell1 u5 u6)
        , guard (n58   /= 0) >> return (Cell1 u5 u8)
        , guard (n45   /= 0) >> return (Cell1 u4 u5)
        ]
    where
    mid   = midpoint c
    midedgeZeros = filter ((== zero) . (flip eval p) . fromComplexRational) [u2, u4, u6, u8]
    
    -- Bezeichnung der neun relevanten Eckpunkte, dem Nummernblock auf der
    -- Tastatur folgend (u1: unten links, u2: unten mitte, ...).
    (u1,u2,u3,u4,u5,u6,u7,u8,u9) =
        ( ri z0  z0
        , ri mid z0
        , ri z1  z0
        , ri z0  mid
        , ri mid mid
        , ri z1  mid
        , ri z0  z1
        , ri mid z1
        , ri z1  z1
        )

    -- Anzahl der Nullstellen im Inneren der Zellen.
    -- Hier geht die Separabilitätsvoraussetzung (B) ein, denn
    -- 'rootsOnRectangle' zählt mit Vielfachheiten, 'rootsOnSegment' aber ohne.
    -- Im separablen Fall ist das dasselbe und die Differenzbildung ist
    -- erlaubt.
    n1245 = rootsOnRectangle u1 u5 p - (n12 + n25 + n45 + n14) / 2
    n2356 = rootsOnRectangle u2 u6 p - (n23 + n36 + n56 + n25) / 2
    n4578 = rootsOnRectangle u4 u8 p - (n45 + n58 + n78 + n47) / 2
    n5689 = rootsOnRectangle u5 u9 p - (n56 + n69 + n89 + n58) / 2
    n12   = rootsOnSegment u1 u2 p
    n25   = rootsOnSegment u2 u5 p
    n45   = rootsOnSegment u4 u5 p
    n14   = rootsOnSegment u1 u4 p
    n23   = rootsOnSegment u2 u3 p
    n36   = rootsOnSegment u3 u6 p
    n56   = rootsOnSegment u5 u6 p
    n58   = rootsOnSegment u5 u8 p
    n78   = rootsOnSegment u7 u8 p
    n47   = rootsOnSegment u4 u7 p
    n69   = rootsOnSegment u6 u9 p
    n89   = rootsOnSegment u8 u9 p

-- | Bestimmt den /Cauchyradius/ eines Polynoms, also eine Zahl /R >= 0/
-- derart, dass alle Nullstellen im offenen Ball mit Radius /R/ um den Ursprung
-- liegen.
cauchyRadius :: NormedPoly ComplexRational -> Rational
cauchyRadius (MkNormedPoly (MkPoly zs)) =
    ((1 +) . maximum) $ map ComplexRational.magnitudeUpperBound zs

{-
-- für normierte Polynome (müssen nicht separabel sein)
subdivisions' :: Rational -> Poly ComplexRational -> [[ComplexRational]]
subdivisions' radius p =
    map (map (mid . snd)) $ iterate (concatMap (uncurry divide)) [(p', Cell2 z0 (negate z0))]
    where
    z0         = negate (radius :+: radius)
    (_,_,p',_) = gcd p (derivative p)
    mid (Cell0 z0)    = z0
    mid (Cell1 z0 z1) = (z0 + z1) / fromInteger 2
    mid (Cell2 z0 z1) = (z0 + z1) / fromInteger 2

-- muss separabel, aber nicht unbed. normiert sein
roots' :: Poly ComplexRational -> Rational -> [[ComplexRational]]
roots' f radius = go 1 iters
    where
    go n (cs:css)
	| all ((<= 1 / fromInteger n) . fst) cs = map snd cs : go (succ n) (cs:css)
	| otherwise                             = go n css
    iters = subdivisions radius f
-}

-- | Liefert zu einem gegebenen Polynom all seine Nullstellen.
-- Das Polynom muss weder normiert noch separabel sein; allerdings werden
-- die Nullstellen ohne Vielfachheiten zurückgegeben.
roots :: Poly Rational -> [Alg QinC]

-- Da die Nullstellenberechnung recht teuer ist, speichern wir für jedes
-- Polynom die gefundenen Nullstellen in der globalen Variablen
-- 'rootsMemoTable'.
--
-- Die Verwendung von 'unsafePerformIO' bricht nicht referentielle Transparenz
-- und ist daher sicher.
roots f = unsafePerformIO $ do
    table <- readIORef rootsMemoTable
    case canonCoeffs f `M.lookup` table of
        Just zs -> return zs
        Nothing -> do
            let zs = roots' f
            writeIORef rootsMemoTable (M.insert (canonCoeffs f) zs table)
            return zs

{-# NOINLINE rootsMemoTable #-}
rootsMemoTable :: IORef (M.Map ([Rational]) [Alg QinC])
rootsMemoTable = unsafePerformIO (newIORef M.empty)

-- Das ist eigentliche Nullstellenberechnungsfunktion.
-- Unser Vorgehen ist folgendes: Zunächst machen wir das Polynom durch
-- Betrachtung seines quadratfreien Anteils separabel. Dann bestimmen wir
-- mittels 'cauchyRadius' eine genügend große 2-Zelle, in deren Innerem
-- alle Nullstellen liegen. Diese wird dann mit 'subdivisions' sukzessive
-- unterteilt. Sobald die Nullstellen isoliert sind, also in jeder Zelle
-- der aktuellen Unterteilung genau eine Nullstelle liegt, können wir die
-- Zellmittelpunkte als Näherungen für die entsprechende Nullstelle verwenden.
roots' :: Poly Rational -> [Alg QinC]
roots' f =
    trace ("Suche Nullstellen von (r=" ++ show radius ++ "): " ++ show f) $
    flip map [0..n-1] $ \i ->
        let iters' = go i 1 iters
        in  MkAlg $ MkIC
                (traceEvals ("zero" ++ show i) $ MkComplex (return . genericIndex iters'))
                (fmap F f'')
    where
    f''        = squarefreePart f
    n          = fromIntegral . degree . unNormedPoly $ f'' :: Int
    radius     = cauchyRadius $ fmap fromRational f''
    iters      = subdivisions radius $ unNormedPoly $ fmap fromRational f''

    -- Bestimmt die "Folge" der 1/n-Näherungen für die i-te Nullstelle.
    -- Die Variable j gibt an, wie genau die als nächstes auszugebene
    -- Approximation sein soll -- sie soll sich von der echten Nullstelle
    -- um höchstens (im Sinne von "<", nicht "<=") 1/j unterscheiden.
    go :: Int -> Integer -> [[(Rational,ComplexRational)]] -> [ComplexRational]
    go i j (cs:css)
        -- Wenn die Nullstellen noch nicht isoliert sind: Weiter machen!
        -- Aber keine Approximation ausgeben.
	| length cs /= n
	= go i j css

        -- Wenn die Nullstellen isoliert sind und die Fehlerschranke der
        -- aktuellen Approximation der i-ten Nullstelle kleiner oder gleich 1/j
        -- ist, können wir diese ausgeben und uns dann auf die Suche nach einer
        -- 1/(j+1)-Approximation begeben.
	| fst (cs !! i) <= 1 / fromInteger j
	= snd (cs !! i) : go i (j + 1) (cs:css)

        -- Schließlich kann der Fall eintreten, dass die Nullstellen zwar schon
        -- isoliert sind, aber die Zelle noch zu groß für eine
        -- 1/j-Approximation sind. Dann müssen wir einfach die restlichen
        -- Iterationen in 'css' untersuchen.
	| otherwise
	= go i j css 
    go _ _ _ = error "roots'"  -- kann nicht eintreten

{-
-- muss weder normiert noch separabel sein; liefert die Nst. mit Vf.
rootsA' :: Poly Rational -> [Alg QinC]
rootsA' f = concatMap (\x -> replicate (multiplicity x (fmap fromRational f)) x) (rootsA f)
-}

{-
rootsEx :: Poly Rational -> Int -> [[ComplexRational]] -> [ComplexRational]
rootsEx f n = go 1
    where
    go :: Int -> [[ComplexRational]] -> [ComplexRational]
    go i xss
        | length (head xss) == n
        = flip map [0..n-1] $ \i -> MkAlg $ flip MkIC (fmap F f) $ MkComplex $ \j -> do
            R $ putStrLn $ "AAA:" ++ show i ++ "," ++ show j
            let z = number $ unAlg (xss `genericIndex` ((2*j - fromIntegral i) `max` 2) !! i)
            unComplex z (2*j)
        | otherwise
        = go (i + 1) (tail xss)
-}

-- | Zu einem gegebenen separablen Polynom und einem Suchradius gibt
-- 'subdivisions' eine (unendliche) Folge von Iterierten zurück, wobei jeder
-- Iterationspunkt eine (endliche) Liste von Näherungs-\/Fehlerschrankenpaare
-- an eine Nullstelle ist.
subdivisions :: Rational -> Poly ComplexRational -> [[(Rational, ComplexRational)]]
subdivisions radius f =
    -- Wir beginnen mit dem kleinsten Rechteck (sogar Quadrat), welches den
    -- durch die Cauchyradiusabschätzung gegebenen Ball umfasst.
    -- Der Mittelpunkt ist dann höchstens (im Sinne von "echt kleiner")
    -- 17/12 * radius von einer Nullstelle entfernt, da 17/12 > sqrt 2.
    go (17/12 * radius) [(f, Cell2 ((-radius) :+: (-radius)) (radius :+: radius))]
    where
    -- Gibt zu einer gegebenen Fehlerschranke und einer (endlichen) Liste von
    -- Zellen, in denen nach Nullstellen gesucht werden soll, den nächsten
    -- Iterationspunkt zurück.
    go :: Rational -> [(Poly ComplexRational, Cell)] -> [[(Rational, ComplexRational)]]
    go r cs = map ((r,) . mid . snd) cs : merge (map (uncurry process) cs)
	where
	process :: Poly (ComplexRational) -> Cell -> [[(Rational, ComplexRational)]]
	process _  (Cell0 z0) = repeat [(0, fromComplexRational z0)]
	process f' c
            -- XXX: Vorerst Newton ausgestellt.
            -- Grund: Zähler und Nenner riesig! Zieht Berechnungstempo enorm runter.
            -- Beispiel: Zerlegung in irred. Faktoren von X^9 - 243 X^3 mit
            -- Newton: etwas mehr als zwei Minuten, ohne Newton: etwa 17 Sekunden.
            -- Außerdem: XXX Falsch angewendet! Darf nur verwendet werden, wenn
            -- die Zelle so klein ist, dass nicht andere Nullstellen verloren
            -- gehen!
            {-
	    | newtonPrecondition f' (mid c)
	    = tail $ zipWith (\n x -> [(r / 2^(2^n - 1), x)]) [0..] (newton f' (mid c))
	    | otherwise
            -}
	    = go (r/2) $ divide f' c
    mid (Cell0 z0)    = fromComplexRational $ z0
    mid (Cell1 z0 z1) = fromComplexRational $ (z0 + z1) / fromInteger 2
    mid (Cell2 z0 z1) = fromComplexRational $ (z0 + z1) / fromInteger 2
    -- Mischt eine endliche Liste von (verallgemeinerten) Iteriertenlisten
    -- zusammen.
    merge :: [[[a]]] -> [[a]]
    merge xsss = concat (map head xsss) : merge (map tail xsss)
    -- Wir nehmen also die ersten Iterierten der gegebenen endlich vielen
    -- Iterationsfolgen, dann die zweiten Iterierten, die dritten...

-- | Bestimmt zu einem Polynom und einem Startpunkt die Folge der
-- Newtoniterierten, den Startpunkt selbst eingeschlossen.
newton :: Poly ComplexRational -> ComplexRational -> [ComplexRational]
newton f = iterate step
    where
    step x = x - eval x f / eval x (derivative f)

-- Thm. 6.9
-- Vor.: derivative f x != 0, f x != 0.
-- Die Voraussetzungen zeigen dann auch, dass f genau eine Nullstelle im
-- offenen Ball mit Radius 2*eta um x hat.
newtonPrecondition :: Poly ComplexRational -> ComplexRational -> Bool
newtonPrecondition f x = eval x f /= zero && eval x (derivative f) /= zero && and ineqs
    where
    etaSq    = absSq (eval x f / eval x (derivative f))
    ineqs    = zipWith (\c k -> absSq c * (fromInteger 8)^(2*k-2) * etaSq^(k-1) <= c1sq) (drop 2 cs) [2..]
    -- XXX: okay, dass coeffs Nuller liefert?
    cs       = unsafeCoeffs $ compose f (iX + fromComplexRational x)
    c1sq     = absSq (cs !! 1)

ex :: Poly ComplexRational
ex = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3 + fromInteger 4 * Poly.fromBase imagUnit))

ex2 :: Poly ComplexRational
ex2 = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3 + fromInteger 4 * Poly.fromBase imagUnit)) * (iX + negate (fromInteger 9 + fromInteger 8 * Poly.fromBase imagUnit))

ex' :: Poly ComplexRational
ex' = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 4))  -- + fromInteger 4 * Poly.fromBase imagUnit))

ex3 :: Poly Rational
ex3 = iX^2 + fromInteger 1

ex4 :: Poly Rational
ex4 = iX^2 + iX + fromInteger 1

ex5 :: Poly Rational
ex5 = iX^3 - fromInteger 1

ex6 :: Poly Rational
ex6 = Poly.fromBase (1/8)*iX^3 + Poly.fromBase (1/2)*iX
