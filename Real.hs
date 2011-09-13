{-# LANGUAGE EmptyDataDecls, TypeFamilies, GeneralizedNewtypeDeriving #-}
module Real where

import Prelude hiding (Real, fromRational, fromInteger, signum, (/), (+), (*), (^))
import ComplexRational
import Ring
import RingMorphism
import Field
import qualified Complex as C
import Complex hiding (sqrt2,goldenRatio)
import Control.Monad

newtype Real = MkReal { unReal :: Complex }
    deriving (Ring,AllowsRationalEmbedding,ApproxFloating)
-- Invariante: Alle epsilon-Näherungen müssen reell sein.

data QinR
instance RingMorphism QinR where
    type Domain   QinR = F Rational
    type Codomain QinR = Real
    mor _ = MkReal . mor (undefined :: Proxy QinC)

data RinC
instance RingMorphism RinC where
    type Domain   RinC = Real
    type Codomain RinC = Complex
    mor _ = unReal

realComponent :: Complex -> Real
realComponent (MkRat (x :+: y)) = MkReal $ MkRat (x :+: 0)
realComponent (MkComplex f) = MkReal . MkComplex $ liftM phi . f
    where
    phi (x :+: y) = x :+: 0

-- terminiert bei 0 nicht, gibt sonst N oder P zurück
signum' :: Real -> Sign
signum' x = unsafeRunR $ do
    q :+: 0 <- go 1
    return (signum q)
    where
    go i = do
        appr <- unComplex (unReal x) i
        if magnitudeSq appr >= 1/fromInteger i^2
            then return appr
            else go (i + 1)

goldenRatio :: Real
goldenRatio = MkReal C.goldenRatio

sqrt2 :: Real
sqrt2 = MkReal C.sqrt2
