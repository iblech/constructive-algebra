-- | Diese Modul stellt Ringe algebraischer Zahlen zur Verfügung, also
-- Ganzheitsringe über Körpern: Zu einem 'RingMorphism' /m/ ist 'Alg' m
-- der Typ derjenigen Elemente von 'Codomain' /m/, welcher über 'Domain' m
-- algebraisch sind. Dabei muss der Ring 'Domain' m ein Körper sein.
--
-- Das Hauptbeispiel bilden die algebraischen Elemente der komplexen Zahlen,
-- 'Alg' 'QinC', und der reellen Zahlen, 'Alg' 'QinR'.
{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, FlexibleContexts,
StandaloneDeriving, UndecidableInstances, FlexibleInstances, PatternGuards,
DatatypeContexts, CPP #-}
module Algebraic where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger)
import qualified IntegralClosure as IC
import IntegralClosure hiding (goldenRatio,sqrt2)
import Complex hiding (goldenRatio,sqrt2)
import Smith (HasAnnihilatingPolynomials)
import ComplexRational
import Ring
import Field
import RingMorphism
import NumericHelper
import Polynomial
import Data.Maybe
import Control.Monad
import Data.Ratio
import Euclidean
import NormedRing

-- früher: newtype (RingMorphism m, Field (Domain m), Codomain m ~ Complex) => Alg m =
-- dann Codomain m ~ Complex weggelassen
-- FIXME
newtype (RingMorphism m, Field (Domain m)) => Alg m =
    MkAlg { unAlg :: IC m }

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

fromRealAlg :: Alg QinR -> Alg QinC
fromRealAlg (MkAlg (MkIC z p)) = MkAlg $ MkIC (fmap fromRational z) p

#define CanInvert(m) \
    RingMorphism m, Field (Domain m), HasAnnihilatingPolynomials (Domain m), \
    NormedRing (Domain m), \
    HasMagnitudeZeroTest (Codomain m), PseudoField (Codomain m), \
    HasDenseSubset (Codomain m), \
    NormedRing (DenseSubset (Codomain m)), Field (DenseSubset (Codomain m))

instance (CanInvert(m)) => IntegralDomain (Alg m)

instance (CanInvert(m)) => Field (Alg m) where recip = maybeInvert

instance (CanInvert(m)) => Eq (Alg m)    where x == y = isNothing $ maybeInvert (x - y)

instance Ord (Alg QinR) where
    compare x y
        | x == y    = EQ
        | otherwise = signum' . number . unAlg $ x - y

instance OrderedRing (Alg QinR)

goldenRatio :: Alg QinC
goldenRatio = MkAlg $ IC.goldenRatio

sqrt2 :: Alg QinC
sqrt2 = MkAlg $ IC.sqrt2

-- Entscheidet, ob die gegebene algebraische Zahl invertierbar ist, und
-- wenn ja, bestimmt ihr Inverses.
maybeInvert :: (CanInvert(m)) => Alg m -> Maybe (Alg m)
-- Die Verwendung von unsafeRunR ist hier offensichtlich sicher.
maybeInvert (MkAlg z) = unsafeRunR $ do
    -- Die Auswertung der mit z mitgelieferten Ganzheitsgleichung ist
    -- üblicherweise sehr teuer. Daher eine einfache Optimierung, um
    -- im Fall, dass die Nullverschiedenheit von z schon durch 1/1-, 1/10-
    -- oder 1/100-Näherungen entdeckt werden kann.
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
    bounds = 1 : map f (tail bs)
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

-- Wie maybeInvert.
maybeInvertReal :: Alg QinR -> Maybe (Alg QinR)
maybeInvertReal = fmap f . maybeInvert . fromRealAlg
    where
    -- Semantisch nicht zu unterscheiden wäre f = realPart.
    -- Dieses hier ist effizienter: Da wir wissen, dass z eine reelle
    -- Zahl sein wird, können wir als Ganzheitsgleichung einfach p
    -- nehmen. (realPart würde dagegen eine Gleichung für (z + i z) / 2
    -- berechnen; deren Grad kann doppelt so groß sein, wie der von p!)
    f :: Alg QinC -> Alg QinR
    f (MkAlg (MkIC z p)) = MkAlg $ MkIC (realPart z) p

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
    in  if magnitudeSq (z0 - fromInteger a) <= 1/100^2 then Just a else
        if magnitudeSq (z0 - fromInteger b) <= 1/100^2 then Just b else Nothing
-- XXX: Korrekt?

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
    :: Alg QinC
    -> Poly Rational
    -> Alg QinC
eval z p = MkAlg $ IC.eval (unAlg z) (fmap F p)
