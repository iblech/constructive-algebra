-- | Dieses Modul stellt die zentrale Typklasse 'Ring' für kommutative Ringe
-- mit Eins und einige spezialisierte Klassen zur Verfügung.
{-# LANGUAGE FlexibleInstances, TypeFamilies, FlexibleContexts #-}
module Ring
    ( -- * Typklassen für Ringe und Ringe mit bestimmten Eigenschaften
      Ring(..), (-), IntegralDomain, OrderedRing
    , HasTestableAssociatedness(..), HasRationalEmbedding(..)
      -- * Ringe mit einer "komplexen Konjugation"
    , HasConjugation(..), absSq
      -- * Näherungen für Debugging-Zwecke
    , HasFloatingApprox(..)
      -- * Allgemeine Funktionen für Ringe
    , sum, product, (^)
    ) where

import qualified Prelude as P
import Prelude (Maybe, (&&), (==), (/=), abs, otherwise, ($), (.), seq)
import Data.Ratio
import qualified Data.Complex as C

-- | Klasse für Typen, die Ringe repräsentieren.
-- Dabei meinen wir stets kommutative Ringe mit Eins.
class Ring a where
    -- | Addition.
    (+) :: a -> a -> a

    -- | Negation.
    negate :: a -> a

    -- | Multiplikation.
    (*) :: a -> a -> a

    -- | Null.
    zero   :: a

    -- | Eins.
    unit   :: a

    -- | /fromInteger z/ soll das Bild von /z/ unter dem eindeutigen
    -- Ringhomomorphismus vom Ring der ganzen Zahlen in /a/, also
    -- /z 1/, sein.
    fromInteger :: P.Integer -> a

    infixl 6 +
    infixl 7 *

    -- | Bei der Rechnung mit Polynomen sammeln sich manchmal abschließende
    -- Null-Koeffizienten an, die weggelassen werden könnten. Da wir nicht
    -- fordern wollen, dass jeder Ring diskret ist (etwa weil das nicht stimmt
    -- oder der Test auf Gleichheit teuer ist), gehen wir hier einen
    -- Kompromiss:
    --
    -- Ein Ring kann die Methode 'couldBeNonZero' implementieren.
    -- Diese soll nur dann 'False' zurückliefern, wenn das übergebene
    -- Ringelement null ist. Sie ist aber nicht gezwungen, in diesem
    -- wirklich 'False' zurückzugeben -- in der Tat ist die
    -- Standardimplementierung einfach
    --
    -- > couldBeNonZero = const True.
    --
    -- Die zu erfüllende Spezifikation ist also:
    --
    -- > couldBeNonZero x == False  ==>  x == zero.
    couldBeNonZero :: a -> P.Bool
    couldBeNonZero = P.const P.True

-- | Subtraktion, erfüllt folgende Spezifikation:
--
-- > x - y = x + negate y.
(-) :: (Ring a) => a -> a -> a
x - y = x + negate y
infixl 6 -

-- | Klasse für Typen, die Integritätsbereiche repräsentieren, also
-- für alle /x/ folgende Bedingung erfüllen: /Entweder/ ist /x/ null,
-- /oder/ /x/ ist regulär (d.h. die Multiplikationsabbildung mit /x/ ist
-- injektiv).
--
-- Aus dieser Definition folgt sofort, dass Gleichheit im Ring entscheidbar
-- (für gegebene Ringelemente /x/, /y/ muss nur die Frage stellen, ob /x-y/
-- null oder regulär ist), daher fordern wir die Zugehörigkeit zur
-- /Eq/-Typklasse.
--
-- Methoden muss ein Typ, der zur 'IntegralDomain'-Klasse gehören möchte,
-- nicht: Denn da in einem Integritätsbereich ein Element genau dann regulär
-- ist, wenn es nicht null ist, wird die geforderte Entscheidungsfähigkeit
-- schon durch '(==)' von 'Eq' geliefert.
class (Ring a, P.Eq a) => IntegralDomain a

-- | Klasse für geordnete Ringe, also Ringe mit einer totalen Relation
-- /(<=)/ (reflexiv, transitiv, antisymmetrisch, je zwei Elemente
-- vergleichbar), die folgende zwei Kompatibilitätsaxiome erfüllt:
--
-- > a <= b          ==>  a + c <= b + c
-- > 0 <= a, 0 <= b  ==>  0 <= ab.
class (Ring a, P.Ord a) => OrderedRing a

-- | Klasse für Ringe, in denen entscheidbar ist, ob zwei gegebene Elemente
-- /x/ und /y/ zueinander assoziiert sind, ob es also ein invertierbares
-- Element /u/ mit /y = ux/ gibt.
class (Ring a) => HasTestableAssociatedness a where
    -- | /areAssociated x y/ soll genau dann /False/ sein, wenn 'x'
    -- und 'y' nicht zueinander assoziiert sind, und andernfalls
    -- /Just u/ zurückgeben, wobei /u/ ein invertierbares Element
    -- mit /y = ux/ (in dieser Reihenfolge) ist.
    --
    -- Richtiger wäre es, den Rückgabetyp auf eine monadischen Typ
    -- abzuschwächen; in den in diesem Projekt betrachteten Fällen können wir
    -- aber in der Tat sogar den von diesem Typ geforderten funktionalen
    -- Zusammenhang bieten.
    areAssociated :: a -> a -> Maybe a

-- | Klasse für Ringe, die eine (dann eindeutige) Einbettung der rationalen
-- Zahlen zulassen.
class (Ring a) => HasRationalEmbedding a where
    -- | /fromRational q/ soll das Bild von /q/ unter der Einbettung der
    -- rationalen Zahlen in den Ring /a/ sein.
    fromRational :: Rational -> a

-- | Klasse für Ringe, in denen der Begriff der komplexen Konjugation definiert
-- ist.
class (Ring a, Ring (RealSubring a)) => HasConjugation a where
    -- | Zugehöriger Unterring der reellen Elemente, also solcher, die von
    -- der komplexen Konjugation invariant gelassen werden.
    type RealSubring a :: *

    -- | Konjugiert ein Ringelement.
    conjugate :: a -> a

    -- | Liefert die imaginäre Einheit.
    imagUnit  :: a

    -- | Liefert den Realteil.
    --
    -- Daraus wird dann auch 'absSq' und 'imagPart' definiert.
    realPart  :: a -> RealSubring a

    -- | Bestimmt den Imaginärteil einer Zahl.
    --
    -- Ist vordefiniert über 'realPart'; wenn das zu einer
    -- nicht-terminierenden Rekursion führt, muss die Instanz eine geeignete
    -- andere Definition gebeen.
    imagPart  :: (HasConjugation a) => a -> RealSubring a
    imagPart = negate . realPart . (imagUnit *)

-- | Berechnet das Betragsquadrat einer Zahl /z/, also
-- das Produkt von /z/ mit seinem komplex Konjugierten.
absSq :: (HasConjugation a) => a -> RealSubring a
absSq z = realPart $ z * conjugate z

-- | Klasse für Ringe, die für Debuggingzwecke eine Approximation durch
-- komplexe Fließkommazahlen zulassen.
class HasFloatingApprox a where
    -- | Liefert eine Approximation durch eine komplexe Fließkommazahl.
    -- Diese Methode ist nur für Debuggingzwecke gedacht; die Wahl der
    -- Genauigkeit bleibt den Instanzen überlassen. Auch muss 'unsafeApprox'
    -- nicht referentiell-transparent sein.
    unsafeApprox :: a -> C.Complex P.Double

-- | Summiert eine endliche Liste von Ringelementen, mit der Konvention
-- /sum [] = zero/.
sum :: (Ring a) => [a] -> a
sum = sum' zero
    where
    sum' acc []     = acc
    sum' acc (x:xs) = let y = acc + x in seq y $ sum' y xs

-- | Multipliziert eine endliche Liste von Ringelementen, mit der Konvention
-- /product [] = unit/.
product :: (Ring a) => [a] -> a
product = product' unit
    where
    product' acc []     = acc
    product' acc (x:xs) = let y = acc * x in seq y $ product' y xs

-- | Potenziert ein gegebenes Ringelement mittels binärer Exponentiation
-- (square and multiply).
(^) :: (Ring a) => a -> P.Integer -> a
_ ^ 0           = unit
x ^ n | n P.> 0 = f x (n-1) x
    where f _ 0 y = y
          f x n y = g x n  where
                    g x n | P.even n    = g (x*x) (n `P.quot` 2)
                          | P.otherwise = f x (n-1) (x*y)
_ ^ _           = P.error "Ring.^: negative exponent"
infixr 8 ^
-- Quelle: Das Haskell-Prelude.

-- Die größenbeschränkten Ganzzahlen bilden einen bestimmten Faktorring
-- des echten Rings der ganzen Zahlen.
instance Ring P.Int where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance HasFloatingApprox P.Int where
    unsafeApprox = P.fromIntegral

-- Der richtige Ring aller ganzen Zahlen, ohne Größenbeschränkung.
instance Ring P.Integer where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance IntegralDomain P.Integer
instance HasTestableAssociatedness P.Integer where
    areAssociated x y
        | abs x == abs y = P.Just (P.signum x * P.signum y)
        | otherwise      = P.Nothing
instance HasFloatingApprox P.Integer where
    unsafeApprox = P.fromIntegral

-- Quotientenkörper.
-- Die Integral-Beschränkung stammt von
instance (IntegralDomain a, P.Integral a) => Ring (Ratio a) where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance (IntegralDomain a, P.Integral a) => IntegralDomain (Ratio a)
instance (IntegralDomain a, P.Integral a) => HasTestableAssociatedness (Ratio a) where
    areAssociated x y
        | x == zero && y == zero = P.Just 1
        | x /= zero && y /= zero = P.Just (y * P.recip x)
        | otherwise              = P.Nothing
instance (IntegralDomain a, P.Integral a) => HasRationalEmbedding (Ratio a) where
    fromRational z =
        let (p,q) = (numerator z, denominator z)
        in  fromInteger p * P.recip (fromInteger q)
instance (IntegralDomain a, P.Integral a, HasFloatingApprox a) => HasFloatingApprox (Ratio a) where
    unsafeApprox x =
        let (p,q) = (numerator x, denominator x)
        in  unsafeApprox p P./ unsafeApprox q
instance OrderedRing (Ratio P.Integer)
