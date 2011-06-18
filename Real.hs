{-# LANGUAGE EmptyDataDecls, TypeFamilies, GeneralizedNewtypeDeriving #-}
module Real where

import Prelude hiding (Real, fromRational)
import ComplexRational
import Ring
import RingMorphism
import Field
import Complex
import Control.Monad

newtype Real = MkReal { unReal :: Complex }
    deriving (Ring,AllowsRationalEmbedding,ApproxFloating)

data QinR
instance RingMorphism QinR where
    type Domain   QinR = F Rational
    type Codomain QinR = Real
    mor _ = MkReal . MkComplex . const . return . fromRational . unF

data RinC
instance RingMorphism RinC where
    type Domain   RinC = Real
    type Codomain RinC = Complex
    mor _ = unReal

realComponent :: Complex -> Real
realComponent (MkComplex f) = MkReal . MkComplex $ liftM phi . f
    where
    phi (x :+: y) = x :+: 0
