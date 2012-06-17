{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
module MetricSpace where

import Data.Ratio

import NumericHelper (NonnegativeRational, PositiveRational)
import Proxy
import Testing
import Nondet

-- | Klasse für metrische Räume.
--
-- Gewöhnlich erwartet man ja von einer Distanzfunktion eines metrischen Raums,
-- dass sie jedem Element ihre Länge als reelle Zahl zuordnet. Diese Definition
-- ist für unsere Zwecke aber nicht geeignet, da wir die reellen Zahlen erst
-- durch einen geeigneten Vervollständigungsprozess aus den rationalen Zahlen
-- erhalten wollen.
--
-- Für uns ist ein metrischer Raum eine Menge /X/ zusammen mit einer
-- Relation /d/, die wir als /d(x,y) <= q/ schreiben, wobei /x/ und /y/
-- aus /X/ stammen und /q/ eine nichtnegative rationale Zahl sein kann.
--
-- Anschaulich soll /d(x,y) <= q/ genau dann wahr sein, wenn die Entfernung
-- von /x/ zu /y/ kleinergleich /q/ ist.
--
-- Wir fordern folgende Axiome erfüllt sein:
--
-- (1) für alle x, y gibt es ein q mit d(x,y) <= q
--
-- (2) d(x,y) <= q, q <= r  ==>  d(x,y) <= r
--
-- (3) d(x,y) <= q + eps, für alle eps > 0  ==>  d(x,y) <= q
--
-- (4) d(x,y) <= 0 <==>  x = y
--
-- (5) d(x,y) <= q  ==>  d(y,x) <= q
--
-- (6) d(x,y) <= q, d(y,z) <= r  ==>  d(x,z) <= q + r
--
-- Die Axiome (4), (5) und (6) entsprechen den üblichen Axiomen für metrische
-- Räume. Axiom (1) fordert, dass Abstände stets endlich sind. Axiom (2)
-- begründet die "<="-Schreibweise, und Axiom (3) wird benötigt, damit sich
-- d(x,y) wie eine reelle Zahl verhält. (Motiviert wird es dadurch, dass
-- die Menge { q | d(x,y) <= q }, falls d(x,y) eine klassische Abstandsfunktion
-- ist, abgeschlossen ist.)
--
-- Wenn man die reellen Zahlen und somit die übliche Definition metrischer
-- Räume zur Verfügung hat, kann man sich leicht überlegen, dass durch die
-- Setzungen
--
-- > X mit üblicher Abstandsfunktion d(.,.)
-- >     |--> X mit Definition dist x y q := (d(x,y) <= q),
-- >
-- > X mit Distanzrelation dist
-- >     |--> X mit Abstandsfunktion d(x,y) := inf { q | d(x,y) <= q }.
-- 
-- eine Äquivalenz (sogar ein Isomorphismus) von Kategorien gegeben wird.
-- Im Nachweis wird dabei jedes Axiom verwendet.
--
-- Überraschend ist vielleicht, dass die Typklasse "MetricSpace" keine
-- Funktion beinhaltet, die die Distanzrelation kodiert. Die Existenz
-- einer solchen stets terminierenden Funktion ist gleichbedeutend mit
-- der Entscheidbarkeit der Distanzrelation, die wir für allgemeine
-- metrische Räume nicht fordern wollen.
--
-- (Alternativ denkbar wäre auch, dist x y q als "d(x,y) < q" zu
-- verstehen. XXX (wieso) ist das schlecht?)
class MetricSpace a where
    -- | /distUpperBound x y/ soll eine obere Schranke für die Entfernung
    -- von /x/ zu /y/ produzieren, d.h. XXX Doku anpassen
    --
    -- > do { q <- distUpperBound x y; return (dist x y q) }
    --
    -- soll stets zu /True/ evaluieren. (Was diese Forderung genau bedeutet,
    -- hängt natürlich davon ab, wie man Werte des monadischen
    -- Typs /m PositiveRational/ beobachten kann und ist ohne weitere Angaben
    -- schwammig.)
    -- 
    -- /distUpperBound/ darf nicht-deterministisch sein, also für jeden Aufruf
    -- neue obere Schranken produzieren.
    distUpperBound :: a -> a -> R NonnegativeRational

class (MetricSpace a) => DecidableMetricSpace a where
    -- | /dist q x y/ soll genau dann wahr sein, wenn die Entfernung von /x/
    -- zu /y/ kleinergleich /q/ ist.
    dist :: NonnegativeRational -> a -> a -> Bool

class (MetricSpace a) => LocatedMetricSpace a where
    -- /locate eps delta x y/ soll für /0 <= delta < eps/ entscheiden, ob
    --   d(x,y) <= eps  oder  nicht: d(x,y) <= delta
    -- gilt und im ersten Fall /Left/, im zweiten Fall /Right/ zurückgeben.
    -- Falls beide Fälle erfüllt sind, darf die Wahl nichtdeterministisch
    -- erfolgen.
    locate :: PositiveRational -> NonnegativeRational -> a -> a -> R (Either () ())

instance (DecidableMetricSpace a) => LocatedMetricSpace a where
    locate eps delta x y = return $ if dist eps x y then Left () else Right ()

instance MetricSpace (Ratio Integer) where
    distUpperBound x y = return $ abs (x - y)

instance DecidableMetricSpace (Ratio Integer) where
    dist x y q = abs (x - y) <= q

{-
props_dist :: (MetricSpace a, Arbitrary a, Show a) => Proxy a -> [Property]
props_dist proxy = (:[]) $ forAll arbitrary $ \(x,y,q) -> q > 0 ==>
    (not (dist x y q) || dist y x q)
-- usw.
-}

{-
props_distUpperBound :: (MetricSpace a, Arbitrary a, Show a) => Proxy a -> [Property]
props_distUpperBound proxy = (:[]) $ forAll arbitrary $ \(x,y) ->
    let _ = x `asTypeOf` y `asTypeOf` unProxy proxy
	d = unsafeRunR $ distUpperBound x y
    in  d > 0 && dist x y d

check_MetricSpace :: IO ()
check_MetricSpace = mapM_ quickCheck $ concat
    [ props_distUpperBound (undefined :: Proxy Rational)
    ]
-}
