{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Field where

import Prelude (Show, Eq, Ord, (.), map)
import qualified Prelude as P
import Ring

import Data.Ratio

class (Ring a) => Field a where
    recip :: a -> a
    -- darf auf der null beliebiges liefern

-- Dummytyp, um das Typsystem davon zu überzeugen, dass ein Field-Typ vorliegt
newtype (Field a) => F a = F { unF :: a }
    deriving (Eq,Ord,Ring,IntegralDomain,Field,P.Num,P.Fractional,TestableAssociatedness,AllowsRationalEmbedding)
instance (Show a, Field a) => Show (F a) where
    show        = P.show . unF
    showsPrec i = P.showsPrec i . unF
    showList    = P.showList . map unF

infixl 7 /
(/) :: (Field a) => a -> a -> a
x / y = x * recip y

instance (IntegralDomain a, P.Integral a) => Field (Ratio a) where
    recip = P.recip
