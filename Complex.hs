{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Complex where

import Control.Monad (liftM, liftM2)
import ComplexRational hiding (magnitudeBound)
import qualified ComplexRational

newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)

type Nat = Integer

newtype Complex = MkComplex { unComplex :: Nat -> R ComplexRational }

instance Eq   Complex where (==) = undefined
instance Show Complex where show = undefined

instance Num Complex where
    MkComplex f + MkComplex g = MkComplex $ \n -> liftM2 (+) (f (2*n)) (g (2*n))
    f * g = MkComplex $ \n -> do
	fBound <- magnitudeBound f
	gBound <- magnitudeBound g
	let n' = n * (fBound + gBound + 1)
	liftM2 (*) (unComplex f n') (unComplex g n')

    abs (MkComplex f) = MkComplex $ liftM abs . f

    signum = error "signum on Complex"

    fromInteger = MkComplex . const . return . fromInteger

magnitudeBound :: Complex -> R Integer
magnitudeBound (MkComplex f) = liftM (succ . ComplexRational.magnitudeBound) $ f 1
-- Eigenschaft: Stelle f die komplexe Zahl a dar. Dann gilt:
--     |a| <= magnitudeBound f
