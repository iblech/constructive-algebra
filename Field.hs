-- | Dieses Modul stellt die zentrale Typklasse 'Field' für Körper
-- zur Verfügung.
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Field where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger, sum, product)
import qualified Prelude as P
import Ring
import Testing
import Proxy

import Data.Ratio

-- | Klasse für Typen, die Körper repräsentieren. Ein Körper ist für uns ein
-- (kommutativer) Ring, der folgendes Zusatzaxiom erfüllt:
--
-- Für jedes Ringelement /x/ gilt /entweder/, dass /x = 0/, /oder/ /x/ ist
-- invertierbar.
--
-- Somit sind Körper dieser Definition nach stets diskret.
class (IntegralDomain a) => Field a where
    -- | Entscheidet, ob das gegebene Körperelement null ist, und falls nein,
    -- berechnet sein Inverses.
    recip :: a -> Maybe a

-- | Dummytyp, um überlappende Instanzdeklarationen vermeiden zu können.
newtype F a = F { unF :: a }
    deriving (Eq,Ord,Ring,IntegralDomain,Field,P.Num,P.Fractional,HasTestableAssociatedness,HasRationalEmbedding,HasFloatingApprox,Arbitrary)
instance (Show a, Field a) => Show (F a) where
    show        = show . unF
    showsPrec i = showsPrec i . unF
    showList    = showList . map unF

-- | Syntaktischer Zucker, um bequemer Divisionen formulieren zu können.
-- Ist der Divisor null, wird eine Laufzeitausnahme geworfen.
(/) :: (Field a) => a -> a -> a
x / y
    | Just y' <- recip y = x * y'
    | otherwise          = error "Field./: Division durch Null!"
infixl 7 /

instance (IntegralDomain a, P.Integral a) => Field (Ratio a) where
    recip z = if z == zero then Nothing else Just (P.recip z)

props_fieldAxioms :: (Field a, Eq a, Arbitrary a, Show a) => Proxy a -> [Property]
props_fieldAxioms a =
    props_ringAxioms a ++
    [ forAll arbitrary $ \x ->
        case recip (x `asTypeOfProxy` a) of
            Just y  -> x /= zero && x * y == unit
            Nothing -> x == zero
    ]
