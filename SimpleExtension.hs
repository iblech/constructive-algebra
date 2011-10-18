-- | Dieses Modul stellt einfache Ring- und Körpererweiterungen der Form
-- /R[X]\/(f)/ bereit. Das Polynom /f/ wird ausschließlich im Typ mitgeführt
-- und befindet sich nicht auf Wertebene; das verhindert unabsichtliches
-- Vermischung von Elementen verschiedener Quotientenringe.
{-# LANGUAGE TypeFamilies, FlexibleContexts, UndecidableInstances, GeneralizedNewtypeDeriving, EmptyDataDecls, StandaloneDeriving #-}
module SimpleExtension
    ( -- * Klassen für Polynome auf Typebene
      ReifyPoly, ReifyIrreduciblePoly
      -- * Datentyp und Funktionen zu einfachen Erweiterungen
    , SE, canonRep, adjointedRoot, SimpleExtension.fromBase
      -- * Beispiele
    , MinPolySqrt2, Qsqrt2inR, SimpleExtension.demo
    ) where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd, Real)
import Ring
import Field
import Polynomial hiding (fromBase)
import qualified Polynomial as Poly
import Complex hiding (fromBase)
import RingMorphism
import Proxy
import Euclidean
import Data.Maybe
import Algebraic
import IntegralClosure hiding (fromBase)
import Text.Printf
import Testing

-- | Klasse für Typen, die Polynome auf Typebene darstellen.
-- Das Gegenstück wäre in Anlehnung an die üblichen Konventionen zur
-- Programmierung auf Typniveau die Funktion 'reflectPoly', die wir aber nicht
-- benötigen und daher auch nicht implementiert haben.
class (Ring (BaseRing p)) => ReifyPoly p where
    type BaseRing p :: *
    -- | Gibt das zu /p/ gehörige Polynom auf Wertebene zurück.
    reifyPoly :: Proxy p -> Poly (BaseRing p)

-- | Klasse für Typen, die irreduzible Polynome auf Typebene darstellen.
class (ReifyPoly p) => ReifyIrreduciblePoly p

-- | Typ der Elemente der einfachen Erweiterung (simple extension) /R[X]\/(p)/.
newtype SE p = MkSE (Poly (BaseRing p))

deriving instance (ReifyPoly p) => Ring (SE p)
deriving instance (ReifyPoly p, Arbitrary (BaseRing p)) => Arbitrary (SE p)

instance (ReifyPoly p, Field (BaseRing p), Show (BaseRing p)) => Show (SE p) where
    show z = "[" ++ show (canonRep z) ++ "]"

-- | Gibt das zu /SE p/ gehörige Moduluspolynom auf Wertebene zurück.
modulus :: (ReifyPoly p) => Proxy (SE p) -> Poly (BaseRing p)
modulus = reifyPoly . (undefined :: Proxy (SE p) -> Proxy p)

-- | Bestimmt zu einem Element des Faktorrings seinen kanonischen
-- Repräsentanten mittels Polynomdivision durch das herausgeteilte Polynom.
--
-- Da wir nicht fordern, dass der Modulus ein normiertes Polynom ist,
-- ist diese Funktion auf solche Grundringe beschränkt, die Körper sind.
canonRep :: (ReifyPoly p, Field (BaseRing p)) => SE p -> Poly (BaseRing p)
canonRep z@(MkSE f) = snd $ f `quotRem` modulus (toProxy z)

-- | Liefert das Element /[X]/ im Quotientenring /R[X]\/(p)/, also die
-- künstliche Nullstelle von /p/.
adjointedRoot :: (ReifyPoly p) => SE p
adjointedRoot = MkSE iX

-- | Hebt ein Element des Grundrings in den Quotientenring hoch.
fromBase :: (ReifyPoly p) => BaseRing p -> SE p
fromBase = MkSE . Poly.fromBase

-- Wenn wir kanonische Repräsentanten zur Verfügung haben, können wir auf
-- Gleichheit testen.
instance (ReifyPoly p, Field (BaseRing p)) => Eq (SE p) where
   z == w = canonRep z == canonRep w

instance (ReifyIrreduciblePoly p, Field (BaseRing p)) => IntegralDomain (SE p) where

instance (ReifyIrreduciblePoly p, Field (BaseRing p)) => Field (SE p) where
    -- Unter der gegebenen Voraussetzung, dass der Modulus p irreduzibel ist,
    -- kann ein ggT von f und p nur konstant oder assoziiert zu p sein.
    -- Im ersten Fall erhalten wir daraus eine Darstellung des Inverses von [f],
    -- im zweiten den Beweis, dass [f] nicht invertierbar ist.
    recip z@(MkSE f)
        | degree d == 0        = Just . MkSE $ fromJust (recip (leadingCoeff d)) .* v
        | degree d == degree p = Nothing
        | otherwise            =
            error "SimpleExtension.recip: Echten Faktor des angeblich irreduziblen Modulus gefunden!"
        where
        p         = modulus (toProxy z)
        (u,v,_,_) = gcd p f
        d         = u*p + v*f

-- | Dummytyp, der das Minimalpolynom der Quadratwurzel aus 2, /X^2 - 2/,
-- repräsentiert.
data MinPolySqrt2
instance ReifyPoly MinPolySqrt2 where
    type BaseRing MinPolySqrt2 = Rational
    reifyPoly _ = iX^2 - fromInteger 2
instance ReifyIrreduciblePoly MinPolySqrt2

-- | Dummytyp, der die kanonische Einbettung der rationalen Zahlen in
-- die Erweiterung /Q[X]\/(X^2-2)/ repräsentiert.
data Qsqrt2inR
instance RingMorphism Qsqrt2inR where
    type Domain   Qsqrt2inR = F (SE MinPolySqrt2)
    type Codomain Qsqrt2inR = Real
    mor _ = Poly.eval Complex.sqrt2 . fmap fromRational . canonRep . unF

props_SimpleExtension :: [Property]
props_SimpleExtension =
    props_fieldAxioms (undefined :: Proxy (SE MinPolySqrt2))

demo :: IO ()
demo = do
    let zs =
            [ ("sqrt2",                   sqrt2' :: Alg Qsqrt2inR)
            , ("goldenRatio",             goldenRatio')
            , ("sqrt2 + goldenRatio",     sqrt2' + goldenRatio')
            , ("(sqrt2 + goldenRatio)^2", (sqrt2' + goldenRatio')^2)
            ]
    putStrLn "Ganzheitsgleichungen über Q(sqrt2):"
    flip mapM_ zs $ \(name,z) -> do
        printf "` %-25s %s\n" (name ++ ":") (show $ unNormedPoly . polynomial . unAlg $ z)

    where
    -- sqrt(2) als Element vom Grad 1 in Q(sqrt2)
    sqrt2'       = MkAlg $ MkIC Complex.sqrt2       $ mkNormedPoly (iX - Poly.fromBase (F adjointedRoot))
    goldenRatio' = MkAlg $ MkIC Complex.goldenRatio $ mkNormedPoly (iX^2 - iX - unit)
