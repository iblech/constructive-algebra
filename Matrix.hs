-- | Dieses Modul stellt grundlegende Matrixoperationen bereit.
--
-- Zur Darstellung der zugrundeliegenden Felder nutzen wir "Data.Array".
{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses, TupleSections #-}
module Matrix where

import Prelude hiding ((!!))

import Data.Array
import Control.Arrow ((***))
import Data.List hiding (transpose, (!!))
import Text.Printf

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
newtype Matrix a = MkMatrix { unMatrix :: Array (Nat,Nat) a }
    deriving (Show,Eq,Functor)

-- | Typ der quadratischen Matrizen beliebiger Größe über /a/.
type SqMatrix a = Matrix a

-- | /m !! (i,j)/ ist der /(i,j)/-Eintrag der Matrix /m/.
-- Die Indizierung beginnt bei /(0,0)/.
(!!) :: Matrix a -> (Nat,Nat) -> a
(!!) m ij = unMatrix m ! ij

fromArray :: Array (Nat,Nat) a -> Matrix a
fromArray = MkMatrix

-- | Liefert die Anzahl der Zeilen einer Matrix.
numRows :: Matrix a -> Nat
numRows = succ . fst . snd . bounds . unMatrix

-- | Liefert die Anzahl der Spalten einer Matrix.
numCols :: Matrix a -> Nat
numCols = succ . snd . snd . bounds . unMatrix

-- | /deleteRow i m/ ist diejenige Untermatrix von /m/, die aus /m/ durch
-- Streichen der Zeile #/i/ (Zählung bei null beginnend) hervorgeht.
deleteRow :: Nat -> Matrix a -> Matrix a
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
deleteColumn :: Nat -> Matrix a -> Matrix a
deleteColumn a = transpose . deleteRow a . transpose

-- | Bestimmt die Transponierte.
transpose :: Matrix a -> Matrix a
transpose (MkMatrix m) = MkMatrix $ ixmap ((id *** swap) (bounds m)) swap m
    where swap (i,j) = (j,i)

-- | Bestimmt die Determinante über die Leibniz-Formel.
-- Hier nur zu Demonstrationszwecken, das restliche Projekt verwendet
-- (eine Vorstufe der) Smithschen Normalform zur Berechnung von Determinanten.
naiveDeterminant :: (Num a) => SqMatrix a -> a
naiveDeterminant m
    | numRows m /= numCols m = error "determinant on non-square matrix>"
    | numRows m == 0         = 1
    | otherwise              = sum $ map f [0..numRows m - 1]
    where
    f i = (-1)^i * (m !! (0,i)) * naiveDeterminant (deleteColumn i m')
    m'  = deleteRow 0 m

-- | Formatiert eine Matrix (für Debugging-Zwecke).
prettyMatrix :: (Show a) => Matrix a -> String
prettyMatrix m =
    concat . intersperse "\n" $ flip map [0..numRows m - 1] $ \i ->
	concat . intersperse " " $ map (printf "%-10s" . show . (m !!) . (i,)) [0..numCols m - 1]

-- XXX: Ringstruktur für quadratische Matrizen!
