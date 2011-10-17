-- | Dieses Modul stellt den Datentyp 'ComplexRational' komplexrationaler
-- Zahlen, also den Elementen von /Q(i)/, bereit.
{-# LANGUAGE TypeFamilies, TypeSynonymInstances, FlexibleInstances #-}
module ComplexRational where

import Data.List (genericIndex)
import qualified Prelude as P
import Prelude hiding (fromInteger, fromRational, (+), (*), (-), (/), (^), negate, recip)
import qualified Data.Complex as C

import NumericHelper
import Ring
import NormedRing
import Field
import Testing
import Control.Monad
import Data.Maybe
import Proxy

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

instance NormedRing ComplexRational where
    norm (x :+: y) q = x^2 + y^2 <= q^2
    normUpperBound = snd . squareRootBounds . magnitudeSq

instance IntegralDomain ComplexRational

instance HasConjugation ComplexRational where
    type RealSubring ComplexRational = Rational
    conjugate (x :+: y) = x :+: (-y)
    realPart  (x :+: _) = x
    imagUnit            = 0 :+: 1

instance Field ComplexRational where
    recip (x :+: y)
	| sq == 0   = Nothing
        | otherwise = Just $ (x/sq) :+: (-y/sq)
      where sq = x^2 + y^2

instance HasRationalEmbedding ComplexRational where
    fromRational = (:+: 0)

instance HasFloatingApprox ComplexRational where
    unsafeApprox (x :+: y) = P.fromRational x C.:+ P.fromRational y

-- | Ringe, die eine Einbettung der rationalen Zahlen zulassen und außerdem
-- über eine komplexe Konjugation verfügen, erlauben auch eine Einbettung
-- der komplexrationalen Zahlen. Diese ist eindeutig, wenn man fordert, dass
-- die imaginäre Einheit /0 :+: 1/ der komplexrationalen Zahlen auf die
-- ausgezeichnete imaginäre Einheit /imagUnit/ des Zielrings gehen soll.
--
-- /fromComplexRational z/ ist dann das Bild von /z/ unter dieser Einbettung.
fromComplexRational :: (Ring a, HasRationalEmbedding a, HasConjugation a) => ComplexRational -> a
fromComplexRational (u :+: v) = fromRational u + imagUnit * fromRational v

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

props_ComplexRational :: [Property]
props_ComplexRational = concat
    [ props_fieldAxioms    (undefined :: Proxy ComplexRational)
    , props_normUpperBound (undefined :: Proxy ComplexRational)
    , props_magnitudeSq
    ]


-- Reduktion auf die 'Arbitrary'-Instanz von /(Rational,Rational)/.
instance Arbitrary ComplexRational where
    arbitrary = liftM (uncurry (:+:)) arbitrary
    shrink    = map   (uncurry (:+:)) . shrink . (\(x :+: y) -> (x,y))
