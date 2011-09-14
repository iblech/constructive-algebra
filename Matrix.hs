-- | Dieses Modul stellt grundlegende Matrixoperationen bereit.
--
-- Zur Darstellung der zugrundeliegenden Felder nutzen wir "Data.Array".
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses, TupleSections, TypeSynonymInstances #-}
module Matrix
    ( Nat
    , Matrix(..), SqMatrix
    , (!!)
    , fromArray, fromArray'
    , numRows, numRows'
    , numCols, numCols'
    , withNontrivialRows, withNontrivialCols, withNontrivialRowsCols, withSquare
    , deleteRow, deleteColumn, transpose
    , fromBase
    , naiveDeterminant
    , prettyMatrix
    ) where

import Prelude hiding ((!!), (+), (*), (-), negate, (^), sum, fromInteger)

import Data.Array
import Control.Monad
import Control.Arrow ((***), (&&&))
import Data.List hiding (transpose, (!!), sum)
import Text.Printf
import TypeLevelNat
import Ring
import Testing

-- | Approximation an den Typ für natürliche Zahlen (beginnend bei null).
-- Wird zur Indizierung der Matrizen zugrundeliegenden "Data.Array"s benutzt.
type Nat = Int

-- | Typ der Matrizen beliebiger Größe über /a/.
-- Die Indizierung der zugrundeliegenden Felder beginnt bei /(0,0)/,
-- Matrizen mit null Zeilen oder Spalten sind zugelassen.
--
-- Eine statische Typisierung der Größe über natürliche Zahlen auf Typebene
-- wäre möglich gewesen, war jedoch im Hinblick auf die vielen
-- Abschneideoperationen auf Untermatrizen in "Smith" unkomfortabel.
newtype Matrix n m a = MkMatrix { unMatrix :: Array (Nat,Nat) a }
    deriving (Show,Eq,Functor)

-- | Typ der quadratischen Matrizen beliebiger Größe über /a/.
type SqMatrix n a = Matrix n n a

-- | /m !! (i,j)/ ist der /(i,j)/-Eintrag der Matrix /m/.
-- Die Indizierung beginnt bei /(0,0)/.
(!!) :: Matrix n m a -> (Nat,Nat) -> a
(!!) m ij = unMatrix m ! ij

fromArray :: Array (Nat,Nat) a -> (forall n m. (ReifyNat n, ReifyNat m) => Matrix n m a -> r) -> r
fromArray arr k = reflectNat n $ \n' -> reflectNat m $ \m' ->
    k (MkMatrix arr `asTypeOf` dummy n' m')
    where
    dummy :: Proxy n -> Proxy m -> Matrix n m a
    dummy = undefined
    (n,m) = (succ *** succ) . (fromIntegral *** fromIntegral) $ snd (bounds arr)

fromArray' :: Array (Nat,Nat) a -> (forall n. (ReifyNat n) => SqMatrix n a -> r) -> r
fromArray' arr k
    | n == m    = reflectNat n $ \n' -> k (MkMatrix arr `asTypeOf` dummy n')
    | otherwise = error "fromArray' eines nicht-quadratischen Felds!"
    where
    dummy = undefined :: Proxy n -> SqMatrix n a
    (n,m) = dim arr

withNontrivialRows
    :: (ReifyNat n, ReifyNat m)
    => Matrix n m a
    -> (forall k. (ReifyNat k) => Matrix (S k) m a -> r)
    -> r
withNontrivialRows mtx@(MkMatrix arr) k
    | n == 0    = error "withNontrivialRows' einer Matrix ohne Zeilen!"
    | otherwise = reflectPositiveNat n $ \n' -> k (MkMatrix arr `asTypeOf` dummy n' (numCols' mtx))
    where
    dummy = undefined :: Proxy k -> Proxy l -> Matrix k l a
    (n,m) = dim arr

withNontrivialCols
    :: (ReifyNat n, ReifyNat m)
    => Matrix n m a
    -> (forall k. (ReifyNat k) => Matrix n (S k) a -> r)
    -> r
withNontrivialCols mtx k = withNontrivialRows (transpose mtx) $ k . transpose

withNontrivialRowsCols
    :: (ReifyNat n, ReifyNat m)
    => Matrix n m a
    -> (forall k l. (ReifyNat k, ReifyNat l) => Matrix (S k) (S l) a -> r)
    -> r
withNontrivialRowsCols mtx k =
    withNontrivialRows mtx $ \mtx' ->
        withNontrivialCols mtx' $ \mtx'' -> k mtx''

withSquare
    :: (ReifyNat n, ReifyNat m)
    => Matrix n m a
    -> (forall k. (ReifyNat k) => SqMatrix k a -> r)
    -> r
withSquare (MkMatrix arr) k = fromArray' arr k

dim :: Array (Nat,Nat) a -> (Integer,Integer)
dim = (succ *** succ) . (fromIntegral *** fromIntegral) . snd . bounds

-- | Liefert die Anzahl der Zeilen einer Matrix.
numRows :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Nat
numRows = fromIntegral . reifyNat . numRows'

-- | Liefert die Anzahl der Spalten einer Matrix.
numCols :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Nat
numCols = fromIntegral . reifyNat . numCols'

numRows' :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Proxy n
numRows' = undefined
numCols' :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Proxy m
numCols' = undefined

-- | /deleteRow i m/ ist diejenige Untermatrix von /m/, die aus /m/ durch
-- Streichen der Zeile #/i/ (Zählung bei null beginnend) hervorgeht.
deleteRow :: (ReifyNat n, ReifyNat m) => Nat -> Matrix (S n) m a -> Matrix n m a
deleteRow a (MkMatrix matrix)
    | a <= n    = MkMatrix $ ixmap ((0,0), (n-1,m)) f matrix
    | otherwise = error "deleteRow"
    where
    ((0,0), (n,m)) = bounds matrix
    f (i,j)
	| i  < a    = (i,j)
	| i >= a    = (i+1,j)
        | otherwise = undefined  -- kann nicht eintreten

-- | /deleteColumn i m/ ist diejenige Untermatrix von /m/, die aus /m/ durch
-- Streichen der Spalte #/i/ (Zählung bei null beginnend) hervorgeht.
deleteColumn :: (ReifyNat n, ReifyNat m) => Nat -> Matrix n (S m) a -> Matrix n m a
deleteColumn a = transpose . deleteRow a . transpose

-- | Bestimmt die Transponierte.
transpose :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Matrix m n a
transpose (MkMatrix m) = MkMatrix $ ixmap ((id *** swap) (bounds m)) swap m
    where swap (i,j) = (j,i)

-- | Bestimmt die Determinante über die Leibniz-Formel.
-- Hier nur zu Demonstrationszwecken, das restliche Projekt verwendet
-- (eine Vorstufe der) Smithschen Normalform zur Berechnung von Determinanten.
naiveDeterminant :: (ReifyNat n, Ring a) => SqMatrix n a -> a
naiveDeterminant m
    | numRows m == 0 = unit
    | otherwise      = sum $ map f [0..numRows m - 1]
    where
    f i = (negate unit)^fromIntegral i * (m !! (0,i)) *
        withNontrivialRowsCols m (flip withSquare naiveDeterminant . deleteColumn i . deleteRow 0)

-- | Formatiert eine Matrix (für Debugging-Zwecke).
prettyMatrix :: (ReifyNat n, ReifyNat m, Show a) => Matrix n m a -> String
prettyMatrix m =
    concat . intersperse "\n" $ flip map [0..numRows m - 1] $ \i ->
	concat . intersperse " " $ map (printf "%-10s" . show . (m !!) . (i,)) [0..numCols m - 1]

instance (ReifyNat n, Ring a) => Ring (SqMatrix n a) where
    zero        = fromBase zero
    unit        = fromBase unit
    negate      = fmap negate
    fromInteger = fromBase . fromInteger
    MkMatrix a + MkMatrix b = MkMatrix $ listArray (bounds a) $ zipWith (+) (elems a) (elems b)
    MkMatrix a * MkMatrix b = MkMatrix $ array ((0,0), (n,n)) $
        [ ((i,j), sum [ a!(i,k) * b!(k,j) | k <- [0..n] ]) | i <- [0..n], j <- [0..n] ]
        where ((0,0),(n,_)) = bounds a

fromBase :: (ReifyNat n, Ring a) => a -> SqMatrix n a
fromBase x = r
    where
    r = MkMatrix $ array ((0,0), (n,n)) $
        [ ((i,j), if i == j then x else zero) | i <- [0..n], j <- [0..n] ]
    n = numRows r - 1

instance (ReifyNat n, ReifyNat m, Arbitrary a) => Arbitrary (Matrix n m a) where
    arbitrary = r
        where
        r = do
            xs <- replicateM (n*m) arbitrary
            return . MkMatrix $ listArray ((0,0), (n-1,m-1)) xs
        (n,m) = (numRows &&& numCols) . (undefined :: Gen a -> a) $ r
