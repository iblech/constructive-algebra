-- | Diese Modul stellt Ringe algebraischer Zahlen zur Verfügung.
-- Hauptbeispiele sind die über /Q/ algebraischen komplexen Zahlen,
-- /Alg QinC/, und die über /Q/ algebraischen reellen Zahlen, /Alg QinR/.
--
-- Solche Ringe haben gegenüber beliebigen Ganzheitsringen zwei entscheidende
-- zusätzliche Merkmale: Sie sind diskret (d.h. Gleichheit ist entscheidbar),
-- und sie bilden Körper im strengen Sinn (d.h. jedes Element ist entweder
-- null oder invertierbar, wobei die Inversen explizit konstruierbar sind).
{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances,
    GADTs, GeneralizedNewtypeDeriving, PatternGuards, StandaloneDeriving,
    TypeFamilies, UndecidableInstances, NondecreasingIndentation #-}
module Algebraic
    ( -- * Typen
      Alg(..), Algebraic.fromBase
      -- * Beziehungen zu anderen Zahlbereichen
    , fromRealAlg
    , isRational, isComplexRational, isInteger, isApproxInteger
    , isRationalPoly, isIntegerPoly, isApproxIntegerPoly
      -- * Rechnungen
    , Algebraic.eval
      -- * Beispiele
    , goldenRatio
    , sqrt2
    , Algebraic.demo
    ) where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger)
import Control.Monad
import Data.Maybe
import Data.Ratio
import Data.List (sortBy)
import Text.Printf

import Complex hiding (goldenRatio,sqrt2)
import ComplexRational
import Euclidean
import Field
import IntegralClosure hiding (goldenRatio,sqrt2)
import qualified IntegralClosure as IC
import NormedRing
import NumericHelper
import Polynomial
import Ring
import RingMorphism
import Smith (HasAnnihilatingPolynomials)

-- | Der Datentyp /'Alg' m/ bezeichnet für einen Ringmorphismus /m/
-- diejenigen Elemente von /'Codomain' m/, die über /'Domain' m/ algebraisch
-- sind, wobei wir anders als in "IntegralClosure" fordern, dass /'Domain' m/
-- ein Körper ist.
--
-- Da /Ganzheit/ und /Algebraizität/ über Körpern dasselbe bedeuten,
-- können wir zur Darstellung einfach 'IC' nutzen.
--
-- Die Klassenvoraussetzungen für 'Eq', 'IntegralDomain' und 'Field' sehen
-- in der HTML-Dokumentation sicherlich sehr erschreckend aus, im Code sind sie
-- durch das CPP-Makro @CanInvert@ besser lesbar.
--
-- Die Show-Instanz respektiert nicht Gleichheit, zwei gleiche algebraische
-- Zahlen können also verschieden formatiert werden.
newtype Alg m = MkAlg { unAlg :: IC m }

deriving instance (RingMorphism m, Eq (Domain m), Show (Domain m), Show (Codomain m)) => Show (Alg m)

-- | Liftet Elemente des Grundrings in den Ring algebraischer Zahlen.
fromBase :: (RingMorphism m, Field (Domain m)) => Domain m -> Alg m
fromBase = MkAlg . IC.fromBase

deriving instance (Ring (IC m)) => Ring (Alg m)
deriving instance (HasRationalEmbedding (IC m)) => HasRationalEmbedding (Alg m)
deriving instance (RingMorphism m, Field (Domain m), HasFloatingApprox (Codomain m)) => HasFloatingApprox (Alg m)

instance HasConjugation (Alg QinC) where
    type RealSubring (Alg QinC) = Alg QinR
    conjugate (MkAlg z) = MkAlg (conjugate z)
    realPart  (MkAlg z) = MkAlg (realPart  z)
    imagUnit            = MkAlg imagUnit

-- Solange es keine Typklassensynonyme gibt, müssen wir uns mit CPP-Makros
-- genügen. Folgendes sind genau die Voraussetzungen, die maybeInvert
-- benötigt.
#define CanInvert(m) \
    RingMorphism m, Field (Domain m), HasAnnihilatingPolynomials (Domain m), \
    NormedRing (Domain m), \
    HasMagnitudeZeroTest (Codomain m), PseudoField (Codomain m), \
    HasDenseSubset (Codomain m), \
    NormedRing (DenseSubset (Codomain m)), Field (DenseSubset (Codomain m))

instance (CanInvert(m)) => IntegralDomain (Alg m)
instance (CanInvert(m)) => Field          (Alg m) where recip = maybeInvert
instance (CanInvert(m)) => Eq             (Alg m) where x == y = isNothing $ maybeInvert (x - y)

instance Ord (Alg QinR) where
    compare x y
        | x == y    = EQ
        | otherwise = signum' . number . unAlg $ x - y

instance OrderedRing (Alg QinR)

-- | Entscheidet, ob die gegebene algebraische Zahl invertierbar ist, und
-- wenn ja, bestimmt ihr Inverses.
maybeInvert :: (CanInvert(m)) => Alg m -> Maybe (Alg m)
-- Die Verwendung von unsafeRunR ist hier offensichtlich sicher.
maybeInvert (MkAlg z) = unsafeRunR $ do
    -- Die Auswertung der mit z lazy mitgeführten Ganzheitsgleichung ist
    -- üblicherweise sehr teuer. Daher eine einfache Optimierung, um
    -- im Fall, dass die Nullverschiedenheit von z schon durch 1/1-, 1/10-
    -- oder 1/100-Näherungen entdeckt werden kann, auf diese verzichten zu
    -- können.
    foundApartness <- go [1,10,100]
    if foundApartness then return $ Just zInv else do
    zeroTest <- magnitudeZeroTestR (roundDownToRecipN $ minimum bounds) (number z)
    if zeroTest
        then return Nothing
        else return $ Just zInv
    where
    as     = canonCoeffs' (polynomial z)
    bs     = dropWhile (== zero) as
    k      = length bs
    -- Der Beweis im Skript verlangt, dass wir eine Schranke epsilon suchen,
    -- die echt kleiner als (|b_0| / (k |b_j|))^(1/j) für alle j = 1, ..., k
    -- ist. Wenn man sich den Beweis genauer anschaut, sieht man, dass es
    -- genügt, wenn epsilon kleiner oder gleich diesen Wurzeln ist.
    --
    -- Wir wollen allerdings die j-ten Wurzeln nicht berechnen. Dazu folgende
    -- Beobachtung: Für Zahlen r zwischen 0 und 1 liegt die j-te Wurzel von r
    -- stets oberhalb von r. Daher ist die Forderung "epsilon <= r" in solchen
    -- Fällen sogar stärker als "epsilon <= r^(1/j)".
    --
    -- Für Zahlen r >= 1 stimmt das nicht. Dann ist aber r^(1/j) >= 1;
    -- nehmen wir daher 1 stets in die Liste der Schranken auf, machen wir auch
    -- dann keinen Fehler.
    --
    -- Als Preis dafür, dass wir hier keine j-ten Wurzeln berechnen, wird
    -- unser epsilon (= minimum bounds) kleiner als nötig, weswegen es dann
    -- magnitudeZeroTestR schwieriger hat.
    bounds = 1 : map f (drop 1 bs)
        where
        f b
            | b == zero = unit  -- sinngemäß unendlich
            | otherwise = normUpperBound (head bs) * normUpperBound (unit/b) / fromIntegral k

    -- Das Inverse von z als algebraische Zahl.
    -- Wird nur verwendet, wenn die Invertierbarkeit auch wirklich nachgewiesen
    -- wurde.
    zInv   = MkAlg $ MkIC (recip' . number $ z) p'
    p'     = normalize' . MkPoly . reverse $ bs

    go []     = return False
    go (n:ns) = do
        q <- approx n (number z)
        -- Ist |q| >= 1/n?
        if q /= zero && norm (unit/q) (fromIntegral n)
            then return True
            else go ns

-- | Liftet eine reell-algebraische Zahl in die komplex-algebraischen Zahlen.
fromRealAlg :: Alg QinR -> Alg QinC
fromRealAlg (MkAlg (MkIC z p)) = MkAlg $ MkIC (fmap fromRational z) p

-- | Entscheidet, ob eine gegebene algebraische Zahl sogar rational ist.
isRational
    :: Alg QinC        -- ^ /z/
    -> Maybe Rational  -- ^ /Just q/, falls /z = q/ für ein rationales /q/,
                       -- sonst /Nothing/
isRational z = listToMaybe $ do
    cand <- [zero] ++ nonNegativeCandidates ++ map negate nonNegativeCandidates
    guard $ fromRational cand == z
    return cand
    where
    f     = MkPoly . map unF . dropWhile (== 0) . canonCoeffs' . polynomial . unAlg $ z
    as    = map unsafeFromRational . canonCoeffs $ (1 / content f) .* f
    (r,s) = (head as, last as)
    nonNegativeCandidates =
        [ p % q
        | p <- positiveDivisors r, q <- positiveDivisors s
        , areCoprime p q
        ]

-- | Entscheidet, ob eine gegebene algebraische Zahl sogar komplexrational ist.
isComplexRational
    :: Alg QinC               -- ^ /z/
    -> Maybe ComplexRational  -- ^ /Just u/, falls /z = u/ für ein
                              -- komplexrationales /u/, sonst /Nothing/
isComplexRational z = do
    x <- isRational . fromRealAlg . realPart $ z
    y <- isRational . fromRealAlg . imagPart $ z
    return $ x :+: y

-- | Entscheidet, ob eine gegebene algebraische Zahl sogar eine ganze Zahl ist.
-- Folgende Spezifikation wird für alle ganzen Zahlen /n/ erfüllt:
--
-- > isInteger z == Just n  <==>  z = n.
isInteger
    :: Alg QinC       -- ^ /z/
    -> Maybe Integer  -- ^ /Just n/, falls /z = n/ für ein ganzzahliges /n/, sonst Nothing
isInteger z
    | Nothing <- isApproxInteger z = Nothing
    | otherwise                    = do
        r <- isRational z
        let (n,m) = numerator r `quotRem` denominator r
        if m == 0 then return n else Nothing

-- | Entscheidet, ob die übergebene algebraische Zahl ganzzahlig sein kann,
-- und wenn ja, bestimmt die (dann eindeutig bestimmte) näheste ganze Zahl an
-- /z/.
--
-- Falls man mit irrtümlicherweise als ganzzahlig gemeldeten algebraischen
-- Zahlen leben kann (etwa, weil man später selbst eine entsprechende Prüfung
-- durchführt), so ist 'isApproxInteger' effizienter als 'isInteger'.
--
-- Folgende Spezifikation wird für alle ganzen Zahlen /n/ erfüllt:
--
-- > isApproxInteger z == Just n  <==  z = n.
isApproxInteger :: Alg QinC -> Maybe Integer
isApproxInteger z =
    let z0@(q :+: _) = unsafeRunR $ approx 100 (number . unAlg $ z)
        (a,b) = (floor q, ceiling q)
    in  if norm (z0 - fromInteger a) (1/100) then Just a else
        if norm (z0 - fromInteger b) (1/100) then Just b else Nothing

-- | Entscheidet, ob ein übergebenes Polynom mit algebraischen Koeffizienten
-- sogar ausschließlich rationale Koeffizienten besitzt.
isRationalPoly :: Poly (Alg QinC) -> Maybe (Poly Rational)
isRationalPoly = isGoodPoly isRational

-- | Entscheidet, ob ein übergebenes Polynom mit algebraischen Koeffizienten
-- sogar ausschließlich ganzzahlige Koeffizienten besitzt.
isIntegerPoly :: Poly (Alg QinC) -> Maybe (Poly Integer)
isIntegerPoly = isGoodPoly isInteger

-- | Entscheidet approximativ, ob ein übergebenes Polynom mit algebraischen
-- Koeffizienten sogar ausschließlich ganzzahlige Koeffizienten besitzt.
isApproxIntegerPoly :: Poly (Alg QinC) -> Maybe (Poly Integer)
isApproxIntegerPoly = isGoodPoly isApproxInteger

isGoodPoly :: (Alg QinC -> Maybe a) -> Poly (Alg QinC) -> Maybe (Poly a)
isGoodPoly isGood p
    | all isJust as = Just . MkPoly $ map fromJust as
    | otherwise     = Nothing
    where
    as = map isGood $ unsafeCoeffs p

-- | Wertet ein Polynom mit rationalen Koeffizienten in einer algebraischen
-- Zahl aus. Erfüllt die Spezifikation
--
-- > eval x f = Poly.eval x (fmap fromBase f),
--
-- ist aber wesentlich effizienter. (Siehe 'IC.eval' in "IntegralClosure".)
eval 
    :: (RingMorphism m, Eq (Domain m), HasAnnihilatingPolynomials (Domain m))
    => Alg m
    -> Poly (Domain m)
    -> Alg m
eval z p = MkAlg $ IC.eval (unAlg z) p

-- | Konstante für den goldenen Schnitt.
goldenRatio :: Alg QinR
goldenRatio = MkAlg $ IC.goldenRatio

-- | Konstante für die Quadratwurzel aus 2.
sqrt2 :: Alg QinR
sqrt2 = MkAlg $ IC.sqrt2

demo :: IO ()
demo = do
    let zs =
            [ ("41",                  fromInteger 41)
            , ("zero",                zero)
            , ("sqrt2 - sqrt2",       sqrt2 - sqrt2)
            , ("goldenRatio * (sqrt2 - sqrt2)", goldenRatio * (sqrt2 - sqrt2))
            , ("goldenRatio",         goldenRatio)
            , ("sqrt2",               sqrt2)
            , ("sqrt2^2",             sqrt2^2)
            , ("sqrt2^5",             sqrt2^5)
            , ("goldenRatio + sqrt2", goldenRatio + sqrt2)
            ]
    mapM_ (uncurry printInfo) zs
    
    putStrLn "Nach Größe sortiert:"
    print $ map fst $ sortBy (\(_,z) (_,z') -> z `compare` z') zs

    where
    printInfo name z = do
        putStrLn $ "Zur Zahl z = " ++ name ++ ":"
        printNumber "z" z
        case recip z of
            Nothing -> putStrLn "` ist nicht invertierbar."
            Just z' -> printNumber "1/z" z'
        putStrLn $ "` ist rational? " ++ show (isRational $ fromRealAlg z)
        putStrLn ""
    printNumber name z = do
        printf "` ungefährer Wert    von %s: %s\n" name (show (unsafeApprox z)) :: IO ()
        printf "` Ganzheitsgleichung von %s: %s\n" name
            (show (unNormedPoly . polynomial . unAlg $ z)) :: IO ()
