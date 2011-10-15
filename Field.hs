-- | Dieses Modul stellt die zentrale Typklasse 'Field' für Körper
-- zur Verfügung.
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Field where

import Prelude (Show, Eq, Ord, (.), map, Maybe(..), otherwise, error, (==))
import qualified Prelude as P
import Ring
import Testing

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
    show        = P.show . unF
    showsPrec i = P.showsPrec i . unF
    showList    = P.showList . map unF

-- | Syntaktischer Zucker, um bequemer Divisionen formulieren zu können.
-- Ist der Divisor null, wird eine Laufzeitausnahme geworfen.
(/) :: (Field a) => a -> a -> a
x / y
    | Just y' <- recip y = x * y'
    | otherwise          = error "Field./: Division durch Null!"
infixl 7 /

instance (IntegralDomain a, P.Integral a) => Field (Ratio a) where
    recip z = if z == zero then Nothing else Just (P.recip z)
