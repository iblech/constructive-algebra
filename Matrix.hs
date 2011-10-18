-- | Dieses Modul stellt grundlegende Matrixoperationen bereit.
--
-- Zur Darstellung der zugrundeliegenden Felder nutzen wir "Data.Array",
-- zur statischen Typisierung der Zeilen- und Spaltenzahl "TypeLevelNat".
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses,
TupleSections, TypeSynonymInstances, FlexibleInstances #-}
module Matrix
    ( -- * Typen
      Nat, Matrix(..), SqMatrix
    , (!!)
      -- * Konstruktion von Matrizen
    , fromArray, fromArray'
    , fromBase
      -- * Dimensionsabfrage
    , numRows, numRows'
    , numCols, numCols'
      -- * Laufzeitprüfungen über bestimmte Dimensionseigenschaften
    , withNontrivialRows, withNontrivialCols, withNontrivialRowsCols, withSquare
      -- * Operationen mit Matrizen
    , deleteRow, deleteColumn, transpose
    , naiveDeterminant
      -- * Debugging
    , prettyMatrix
    ) where

import Prelude hiding ((!!), (+), (*), (-), negate, (^), sum, fromInteger)

import Control.Arrow ((***), (&&&))
import Control.Monad
import Data.Array
import Data.List hiding (transpose, (!!), sum)
import Text.Printf

import Ring
import Testing
import TypeLevelNat

-- | Approximation an den Typ für natürliche Zahlen (beginnend bei Null),
-- abweichend vom restlichen Projekt einfach 'Int' statt 'Integer'.
-- Wird zur Indizierung der Matrizen zugrundeliegenden "Data.Array"s benutzt.
type Nat = Int

-- | Typ der /(n x m)/-Matrizen über /a/.
-- Die Indizierung der zugrundeliegenden Felder beginnt bei /(0,0)/,
-- Matrizen mit null Zeilen oder Spalten sind zugelassen.
--
-- Die Typen /n/ und /m/ sollten der 'TypeLevelNat.ReifyNat'-Klasse angehören.
--
-- Da wir den 'MkMatrix'-Konstruktor exportieren, kann man den statischen
-- Schutz überwinden.
newtype Matrix n m a = MkMatrix { unMatrix :: Array (Nat,Nat) a }
    deriving (Show,Eq,Functor)

-- | Typ der quadratischen /n x n/-Matrizen über /a/.
-- Der Typ /n/ sollte der 'TypeLevelNat.ReifyNat'-Klasse angehören.
--
-- Die 'Ring'-Instanz von /SqMatrix n/ ist eine Lüge, da diese die
-- Multiplikation als kommutativ voraussetzt. Sie wird nur in "Smith"
-- für eine QuickCheck-Eigenschaft verwendet.
type SqMatrix n a = Matrix n n a

-- | /m !! (i,j)/ ist der /(i,j)/-Eintrag der Matrix /m/.
-- Die Indizierung beginnt bei /(0,0)/.
(!!) :: Matrix n m a -> (Nat,Nat) -> a
(!!) m ij = unMatrix m ! ij

-- | Ummantelt ein gegebenes Feld in eine Matrix.
-- Da der Ergebnistyp abhängig von der Zeilen- und Spaltenanzahl des gegebenen
-- Felds ist, kann die resultierende Matrix aber nicht einfach zurückgegeben
-- werden, sondern muss an eine polymorphe Continuation übergeben werden.
fromArray :: Array (Nat,Nat) a -> (forall n m. (ReifyNat n, ReifyNat m) => Matrix n m a -> r) -> r
fromArray arr k
    | fst (bounds arr) == (0,0) =
        reflectNat n $ \n' -> reflectNat m $ \m' -> k (MkMatrix arr `asTypeOf` dummy n' m')
    | otherwise                 = error "Matrix.fromArray: Unkonventionsgemäße Indizierung in fromArray!"
    where
    dummy :: Proxy n -> Proxy m -> Matrix n m a
    dummy = undefined
    (n,m) = (succ *** succ) . (fromIntegral *** fromIntegral) $ snd (bounds arr)

-- | Ummantelt ein gegebenes quadratisches Feld in eine quadratische Matrix.
-- Wirft eine Laufzeitausnahme, falls das gegebene Feld nicht quadratisch ist.
fromArray' :: (forall n. (ReifyNat n) => SqMatrix n a -> r) -> Array (Nat,Nat) a -> r
fromArray' k arr
    | n == m    = reflectNat n $ \n' -> k (MkMatrix arr `asTypeOf` dummy n')
    | otherwise = error "Matrix.fromArray': auf nicht-quadratisches Feld aufgerufen!"
    where
    dummy = undefined :: Proxy n -> SqMatrix n a
    (n,m) = dim arr

-- | Bringt die Information darüber, dass die gegebene Matrix mindestens eine
-- Zeile besitzt, aufs Typniveau; ist dem nicht so, wird eine Laufzeitausnahme
-- geworfen.
withNontrivialRows
    :: (ReifyNat n, ReifyNat m)
    => (forall k. (ReifyNat k) => Matrix (S k) m a -> r)
    -> Matrix n m a
    -> r
withNontrivialRows k mtx@(MkMatrix arr)
    | n == 0    = error "Matrix.withNontrivialRows': aufgerufen auf einer Matrix ohne Zeilen!"
    | otherwise = reflectPositiveNat n $ \n' -> k (MkMatrix arr `asTypeOf` dummy n' (numCols' mtx))
    where
    dummy = undefined :: Proxy k -> Proxy l -> Matrix k l a
    (n,_) = dim arr

-- | Bringt die Information darüber, dass die gegebene Matrix mindestens eine
-- Spalte besitzt, aufs Typniveau; ist dem nicht so, wird eine Laufzeitausnahme
-- geworfen.
withNontrivialCols
    :: (ReifyNat n, ReifyNat m)
    => (forall k. (ReifyNat k) => Matrix n (S k) a -> r)
    -> Matrix n m a
    -> r
withNontrivialCols k mtx = withNontrivialRows (k . transpose) (transpose mtx)

-- | Bringt die Information darüber, dass die gegebene Matrix mindestens eine
-- Zeile und eine Spalte besitzt, aufs Typniveau; ist dem nicht so, wird eine
-- Laufzeitausnahme geworfen.
withNontrivialRowsCols
    :: (ReifyNat n, ReifyNat m)
    => (forall k l. (ReifyNat k, ReifyNat l) => Matrix (S k) (S l) a -> r)
    -> Matrix n m a
    -> r
withNontrivialRowsCols k = withNontrivialRows (withNontrivialCols k)
-- Leider kann man das nicht punktfrei als withNontrivialRows .
-- withNontrivialCols schreiben: GHC bringt wegen des forall-Typs höherer
-- Ordnung dann einen Typfehler, da er den Kompositionsoperator (.)
-- nicht richtig instanziieren kann.

-- | Bringt die Information darüber, dass die gegebene Matrix quadratisch ist,
-- aufs Typniveau; ist dem nicht so, wird eine Laufzeitausnahme geworfen.
withSquare
    :: (ReifyNat n, ReifyNat m)
    => (forall k. (ReifyNat k) => SqMatrix k a -> r)
    -> Matrix n m a
    -> r
withSquare k (MkMatrix arr) = fromArray' k arr

-- | Liefert die Anzahl Zeilen und Spalten des zugrundeliegenden Felds.
-- Wird nur intern in diesem Modul benötigt. Benutzer dieses Moduls sollten
-- die Funktionen 'numRows' und 'numCols' verwenden, die auch nur statische
-- Typinformation benötigen und nichts das zugrundeliegende Feld betrachten.
dim :: Array (Nat,Nat) a -> (Integer,Integer)
dim = (succ *** succ) . (fromIntegral *** fromIntegral) . snd . bounds

-- | Liefert die Anzahl der Zeilen einer Matrix auf Wertebene.
-- Diese Funktion nutzt nur die gegebenen Typinformationen und betrachtet
-- nicht das zugrundeliegende Feld.
numRows :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Nat
numRows = fromIntegral . reifyNat . numRows'

-- | Liefert die Anzahl der Spalten einer Matrix auf Wertebene.
-- Diese Funktion nutzt nur die gegebenen Typinformationen und betrachtet
-- nicht das zugrundeliegende Feld.
numCols :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Nat
numCols = fromIntegral . reifyNat . numCols'

-- | Liefert die Anzahl der Zeilen einer Matrix auf Typebene.
-- In das zugrundeliegende Feld wird nicht geschaut.
numRows' :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Proxy n
numRows' = undefined

-- | Liefert die Anzahl der Spalten einer Matrix auf Typebene.
-- In das zugrundeliegende Feld wird nicht geschaut.
numCols' :: (ReifyNat n, ReifyNat m) => Matrix n m a -> Proxy m
numCols' = undefined

-- | /deleteRow i m/ ist diejenige Untermatrix von /m/, die aus /m/ durch
-- Streichen der Zeile #/i/ (Zählung bei null beginnend) hervorgeht.
deleteRow :: (ReifyNat n, ReifyNat m) => Nat -> Matrix (S n) m a -> Matrix n m a
deleteRow a (MkMatrix matrix)
    | a <= n    = MkMatrix $ ixmap ((0,0), (n-1,m)) f matrix
    | otherwise = error "Matrix.deleteRow: Zeilenindex übersteigt Dimension"
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
        withNontrivialRowsCols (withSquare naiveDeterminant . deleteColumn i . deleteRow 0) m

-- Ringstruktur der quadratischen (n x n)-Matrizen.
-- Da wir unsere Ringe als kommutativ voraussetzen, ist diese eigentlich
-- nicht zulässig.
instance (ReifyNat n, Ring a) => Ring (SqMatrix n a) where
    zero        = fromBase zero
    unit        = fromBase unit
    negate      = fmap negate
    fromInteger = fromBase . fromInteger
    MkMatrix a + MkMatrix b = MkMatrix $ listArray (bounds a) $ zipWith (+) (elems a) (elems b)
    MkMatrix a * MkMatrix b = MkMatrix $ array ((0,0), (n,n)) $
        [ ((i,j), sum [ a!(i,k) * b!(k,j) | k <- [0..n] ]) | i <- [0..n], j <- [0..n] ]
        where ((0,0),(n,_)) = bounds a

-- | 'fromBase x' ist das 'x'-fache der Einheitsmatrix.
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

-- | Formatiert eine Matrix (für Debugging-Zwecke).
prettyMatrix :: (ReifyNat n, ReifyNat m, Show a) => Matrix n m a -> String
prettyMatrix m =
    concat . intersperse "\n" $ flip map [0..numRows m - 1] $ \i ->
	concat . intersperse " " $ map (printf "%-10s" . show . (m !!) . (i,)) [0..numCols m - 1]
