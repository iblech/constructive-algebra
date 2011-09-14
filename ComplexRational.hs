-- | Dieses Modul stellt den Datentyp 'ComplexRational' komplexrationaler
-- Zahlen, also den Elementen von /Q(i)/, bereit.
module ComplexRational where

import Data.List (genericIndex)
import qualified Prelude as P
import Prelude hiding (fromInteger, fromRational, (+), (*), (-), (/), (^), negate, recip)
import qualified Data.Complex as C

import NumericHelper
import Ring
import Field
import Testing
import Control.Monad

-- | Typ für komplexrationale Zahlen in kartesischer Darstellung.
-- Der Konstruktor ist strikt in seinen beiden Argumenten.
data ComplexRational = !Rational :+: !Rational
    deriving (Eq)

instance Show ComplexRational where
    show (x :+: y)
	| y == 0    = show x
	| otherwise = "(" ++ show x ++ "+i" ++ show y ++ ")"

instance Ring ComplexRational where
    (x :+: y) + (x' :+: y') = (x + x') :+: (y + y')
    (x :+: y) * (x' :+: y') = (x*x' - y*y') :+: (x*y' + y*x')
    negate (x :+: y)        = negate x :+: negate y
    fromInteger i = fromInteger i :+: 0
    zero = fromInteger 0
    unit = fromInteger 1
    couldBeNonZero = (/= zero)

instance IntegralDomain ComplexRational

instance AllowsConjugation ComplexRational where
    conjugate (x :+: y) = x :+: (-y)
    imagUnit            = 0 :+: 1

instance Field ComplexRational where
    recip (x :+: y)
	| sq == 0   = error "division by zero (ComplexRational)"
	| otherwise = (x/sq) :+: (-y/sq)
	where sq = x^2 + y^2

instance AllowsRationalEmbedding ComplexRational where
    fromRational = (:+: 0)

instance ApproxFloating ComplexRational where
    approx (x :+: y) = P.fromRational x C.:+ P.fromRational y

-- | Berechnet das Quadrat /|z|^2/ des Betrags einer Zahl /z/.
--
-- (Oftmals sind wir eigentlich am Betrag selbst, und nicht an seinem
-- Quadrat, interessiert. Aber das Betragsquadrat ist stets wieder eine
-- rationale Zahl, während wir für den echten Betrag entweder Fließkommazahlen
-- (schlecht) oder eine Umsetzung von Q(i) (besser) benötigen würden.)
magnitudeSq :: ComplexRational -> Rational
magnitudeSq (x :+: y) = x^2 + y^2

props_magnitudeSq :: [Property]
props_magnitudeSq =
    [ property $ magnitudeSq unit == 1
    , forAll arbitrary $ \z -> forAll arbitrary $ \u ->
        magnitudeSq (z * u) == magnitudeSq z * magnitudeSq u
    ]

-- | Liefert eine obere Schranke für den Betrag einer Zahl /z/.
magnitudeUpperBound :: ComplexRational -> Rational
magnitudeUpperBound (x :+: y) = abs x + abs y

props_magnitudeUpperBound :: [Property]
props_magnitudeUpperBound = (:[]) $ forAll arbitrary $ \x ->
    magnitudeUpperBound x >= 0 && magnitudeSq x <= (magnitudeUpperBound x)^2

-- | Liefert Approximationen an den goldenen Schnitt. Erfüllt folgende
-- Spezifikation:
--
-- > |goldenRatioSeq n - φ| < 1/n für alle n >= 1.
goldenRatioSeq :: Integer -> ComplexRational
goldenRatioSeq n = xs `genericIndex` (ilogb 2 n)
    where xs = iterate ((unit +) . recip) unit
-- a_1 = 1, a_(n+1) = 1 + 1/a_n
-- erfüllt |a_n - a| < (4/9)^n für alle n >= 2.
-- Diese Folge hier wird künstlich verlangsamt, sie erfüllt |x_n - x| < 1/n für
-- alle n >= 1.
-- XXX: Bestimmt kann man die Folge noch viel weiter verlangsamen!

-- | Liefert Approximationen an /√2/. Erfüllt folgende Spezifikation:
--
-- > |sqrt2Seq n - √2| < 1/n für alle n >= 1.
sqrt2Seq :: Integer -> ComplexRational
sqrt2Seq n = xs `genericIndex` ((1 + ilogb 2 n) `div` 2)
    where xs = map (+ unit) $ iterate (\x -> unit / (fromInteger 2 + x)) zero
-- Die Folge mit
--   a_1 = 0, a_(n+1) = 1/(2+a_n)
-- erfüllt |a_n - (sqrt(2) - 1)| <= gamma^n * c für alle n >= 1
-- mit gamma = 1 / (2 (1 + sqrt(2))) <= 0.2072 und c = 2.
-- Die Folge hier wird daher entsprechend künstlich verlangsamt.
-- XXX: Bestimmt kann man die Folge noch viel weiter verlangsamen!

props_Approximation :: (Integer -> ComplexRational) -> C.Complex P.Double -> [Property]
props_Approximation f x = (:[]) $ forAll positive $ \n ->
    C.magnitude (approx (f n) P.- x) < P.recip (P.fromInteger n)

props_ComplexRational :: [Property]
props_ComplexRational = concat
    [ props_magnitudeSq
    , props_magnitudeUpperBound
    , props_Approximation goldenRatioSeq ((1 P.+ sqrt 5) P./ 2)
    , props_Approximation sqrt2Seq       (sqrt 2)
    ]


-- Reduktion auf die 'Arbitrary'-Instanz von /(Rational,Rational)/.
instance Arbitrary ComplexRational where
    arbitrary = liftM (uncurry (:+:)) arbitrary
    shrink    = map   (uncurry (:+:)) . shrink . (\(x :+: y) -> (x,y))
