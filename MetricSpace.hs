{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
module MetricSpace where

import Data.Ratio

import NumericHelper (NonnegativeRational)
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
-- Die Anschauung hinter unserer Definition ist folgende: /dist x y q/ soll
-- genau dann wahr sein, wenn die Entfernung von /x/ zu /y/ kleinergleich /q/
-- ist. Wir schreiben
--
-- > d(x,y) <= q  genau dann, wenn  dist x y q wahr ist.
--
-- Konkret müssen folgende Axiome erfüllt sein:
--
-- (1) für alle x, y gibt es ein q mit d(x,y) <= q
--
-- (2) d(x,y) <= q, q <= r  ==>  d(x,y) <= r
--
-- (3) d(x,y) <= q + eps, für alle eps > 0  ==>  d(x,y) <= q
--
-- (4) d(x,y) <= eps für alle eps > 0  <==>  x = y
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
-- >     |--> X mit Abstandsfunktion d(x,y) := inf { q | dist x y q stets True }.
-- 
-- eine Äquivalenz (sogar ein Isomorphismus) von Kategorien gegeben wird.
-- Im Nachweis wird dabei jedes Axiom verwendet.
--
-- (Alternativ denkbar wäre auch, dist x y q als "d(x,y) < q" zu
-- verstehen. XXX (wieso) ist das schlecht?)
class MetricSpace a where
    -- | /dist x y q/ soll genau dann wahr sein, wenn die Entfernung von /x/
    -- zu /y/ kleinergleich /q/ ist.
    dist :: a -> a -> PositiveRational -> Bool

    -- | /distUpperBound x y/ soll eine obere Schranke für die Entfernung
    -- von /x/ zu /y/ produzieren, d.h.
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
    distUpperBound :: a -> a -> R PositiveRational

instance MetricSpace (Ratio Integer) where
    dist           x y q = abs (x - y) <= q
    distUpperBound x y   = return $ incr $ abs (x - y)
	where incr q = if q == 0 then 1e-20 else q

{-
props_dist :: (MetricSpace a, Arbitrary a, Show a) => Proxy a -> [Property]
props_dist proxy = (:[]) $ forAll arbitrary $ \(x,y,q) -> q > 0 ==>
    (not (dist x y q) || dist y x q)
-- usw.
-}

props_distUpperBound :: (MetricSpace a, Arbitrary a, Show a) => Proxy a -> [Property]
props_distUpperBound proxy = (:[]) $ forAll arbitrary $ \(x,y) ->
    let _ = x `asTypeOf` y `asTypeOf` unProxy proxy
	d = unsafeRunR $ distUpperBound x y
    in  d > 0 && dist x y d

check_MetricSpace :: IO ()
check_MetricSpace = mapM_ quickCheck $ concat
    [ props_distUpperBound (undefined :: Proxy Rational)
    ]
