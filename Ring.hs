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
      -- * QuickCheck-Eigenschaften
    , props_ringAxioms, props_areAssociated
    , check_Ring
    ) where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger, sum, product)
import qualified Prelude as P
import qualified Data.Complex as C
import Data.Ratio

import Proxy
import Testing

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
    fromInteger :: Integer -> a

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
    --
    -- Ringe, für die es einen effizienten Gleichheitstest mit Null gibt,
    -- können 'couldBeNonZero' entsprechend besser definieren.
    couldBeNonZero :: a -> Bool
    couldBeNonZero = const True

-- | Subtraktion, erfüllt folgende Spezifikation:
--
-- > x - y = x + negate y.
(-) :: (Ring a) => a -> a -> a
x - y = x + negate y
infixl 6 -

newtype RejectZero a = MkRejectZero a
    deriving (Show,Eq)

instance (Ring a, Eq a, Arbitrary a) => Arbitrary (RejectZero a) where
    arbitrary = do
        x <- arbitrary
        return $ if x == zero
            then MkRejectZero unit
            else MkRejectZero x
    shrink (MkRejectZero x) = map MkRejectZero . shrink $ x

props_ringAxioms :: (Ring a, Eq a, Arbitrary a, Show a) => Proxy a -> [Property]
props_ringAxioms a = concat
    [ props_commutativeGroup (+) (zero `asTypeOfProxy` a) negate
    , [ property $ \x y z -> typ x && x * (y * z) == (x * y) * z ]
    , [ property $ \x     -> typ x && x * unit    == x           ]
    , [ property $ \x y   -> typ x && x * y       == y * x       ]
    , [ property $ \x y z -> typ x && x * (y + z) == x * y + x * (z `asTypeOfProxy` a) ]
    ]
    where typ x = let _ = x `asTypeOfProxy` a in True

props_commutativeMonoid :: (Eq a, Show a, Arbitrary a) => (a -> a -> a) -> a -> [Property]
props_commutativeMonoid (#) nul =
    [ property $ \x y z -> x # (y # z)    == (x # y) # z
    , property $ \x     -> x # nul        == x
    , property $ \x y   -> x # y          == y # x
    ]

props_commutativeGroup :: (Eq a, Show a, Arbitrary a) => (a -> a -> a) -> a -> (a -> a) -> [Property]
props_commutativeGroup (#) nul neg =
    props_commutativeMonoid (#) nul ++ [ property $ \x -> x # neg x == nul ]


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
-- Bestimmte Methoden muss ein Typ, der zur 'IntegralDomain'-Klasse gehören
-- möchte, nicht haben: Denn da in einem Integritätsbereich ein Element genau dann
-- regulär ist, wenn es nicht null ist, wird die geforderte Entscheidungsfähigkeit
-- schon durch '(==)' von 'Eq' geliefert.
class (Ring a, Eq a) => IntegralDomain a

-- | Klasse für geordnete Ringe, also Ringe mit einer totalen Relation
-- /(<=)/ (reflexiv, transitiv, antisymmetrisch, je zwei Elemente
-- vergleichbar), die folgende zwei Kompatibilitätsaxiome erfüllt:
--
-- > a <= b          ==>  a + c <= b + c
-- > 0 <= a, 0 <= b  ==>  0 <= ab.
class (Ring a, Ord a) => OrderedRing a

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

props_areAssociated :: (HasTestableAssociatedness a, Eq a, Show a, Arbitrary a) => Proxy a -> [Property]
props_areAssociated a =
    [ property $ \x y ->
        case areAssociated x y of
            Nothing -> True  -- ungenau!
            Just u  -> y == u * x
                where _ = x `asTypeOfProxy` a
    ]

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
    unsafeApprox :: a -> C.Complex Double

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
--
-- Quelle: Das Haskell-Prelude.
(^) :: (Ring a) => a -> Integer -> a
_ ^ 0           = unit
x ^ n | n > 0 = f x (n-1) x
    where f _ 0 y = y
          f x n y = g x n  where
                    g x n | even n    = g (x*x) (n `quot` 2)
                          | otherwise = f x (n-1) (x*y)
_ ^ _           = error "Ring.^: negative exponent"
infixr 8 ^

-- Die größenbeschränkten Ganzzahlen bilden einen bestimmten Faktorring
-- des echten Rings der ganzen Zahlen.
instance Ring Int where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance HasFloatingApprox Int where
    unsafeApprox = fromIntegral

-- Der richtige Ring aller ganzen Zahlen, ohne Größenbeschränkung.
instance Ring Integer where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance IntegralDomain Integer
instance HasTestableAssociatedness Integer where
    areAssociated x y
        | abs x == abs y = Just (signum x * signum y)
        | otherwise      = Nothing
instance HasFloatingApprox Integer where
    unsafeApprox = fromIntegral

-- Quotientenkörper.
-- Die Integral-Beschränkung stammt von
instance (IntegralDomain a, Integral a) => Ring (Ratio a) where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance (IntegralDomain a, Integral a) => IntegralDomain (Ratio a)
instance (IntegralDomain a, Integral a) => HasTestableAssociatedness (Ratio a) where
    areAssociated x y
        | x == zero && y == zero = Just 1
        | x /= zero && y /= zero = Just (y * P.recip x)
        | otherwise              = Nothing
instance (IntegralDomain a, Integral a) => HasRationalEmbedding (Ratio a) where
    fromRational z =
        let (p,q) = (numerator z, denominator z)
        in  fromInteger p * P.recip (fromInteger q)
instance (IntegralDomain a, Integral a, HasFloatingApprox a) => HasFloatingApprox (Ratio a) where
    unsafeApprox x =
        let (p,q) = (numerator x, denominator x)
        in  unsafeApprox p P./ unsafeApprox q
instance OrderedRing (Ratio Integer)

check_Ring :: IO ()
check_Ring = mapM_ quickCheck $ concat
    [ props_ringAxioms    (undefined :: Proxy Integer)
    , props_ringAxioms    (undefined :: Proxy Int)
    , props_ringAxioms    (undefined :: Proxy Rational)
    , props_areAssociated (undefined :: Proxy Integer)
    , props_areAssociated (undefined :: Proxy Rational)
    ]
