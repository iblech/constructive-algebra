module Field where

import qualified Prelude as P
import Ring

import Data.Ratio

class (Ring a) => Field a where
    recip :: a -> a
    -- darf auf der null beliebiges liefern

infixl 7 /
(/) :: (Field a) => a -> a -> a
x / y = x * recip y

instance (IntegralDomain a, P.Integral a) => Field (Ratio a) where
    recip = P.recip
