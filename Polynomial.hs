-- | Dieses Modul stellt für jeden Ring /a/ seinen Polynomring /Poly a/ in
-- einer Variablen zur Verfügung.
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Polynomial
    ( Poly(MkPoly)
    , canonCoeffs, unsafeCoeffs
    , fromBase, eval, eval0
    , normedQuotRem
    , (.*), iX
    , normalize, leadingCoeff
    , derivative, compose
    , squarefreePart
    , couldBeNotX
    ) where

import Prelude hiding (gcd, (+), (-), (*), (/), (^), negate, recip, fromInteger, fromRational, quotRem, sum)
import qualified Prelude as P
import Test.QuickCheck
import Data.List (intersperse, genericLength, foldl')
import NumericHelper
import Ring
import Field
import Euclidean

-- | Typ der Polynome über 'a', repräsentiert durch die zugehörigen Folgen der
-- Koeffizienten, von niedrigster zur höchsten Potenz geordnet. Die Darstellung
-- ist wegen möglicher abschließender Nuller natürlich nicht eindeutig.
newtype Poly a = MkPoly { unPoly :: [a] }
  deriving (Functor)

instance (Ring a, Eq a, Show a) => Show (Poly a) where
  show f = addZero $ concat . intersperse " + " $ filter (not . null) $ zipWith join (canonCoeffs f) vars
      where
      vars = "" : "X" : map (("X^" ++) . show) [2..]
      join x v
        | x == zero = ""
	| x == unit = if null v then "1" else v
	| otherwise = show x ++ (if null v then "" else "*" ++ v)
      addZero s
	| null s    = "0"
	| otherwise = s

instance (Ring a, Eq a) => Eq (Poly a) where
    p == q = canonCoeffs p == canonCoeffs q
    
instance (Ring a) => Ring (Poly a) where
    MkPoly xs + MkPoly ys = simplify $ MkPoly (zipWithDefault (+) zero xs ys)
    MkPoly xs * MkPoly ys = simplify . MkPoly $ go xs ys
	where
	go []     ys = []
	go (x:xs) ys = zipWithDefault (+) zero (map (x *) ys) (zero:go xs ys)
    negate = fmap negate
    fromInteger = MkPoly . (:[]) . fromInteger
    zero = MkPoly []
    unit = MkPoly [unit]

instance (AllowsConjugation a) => AllowsConjugation (Poly a) where
    conjugate (MkPoly xs) = MkPoly (map conjugate xs)
    imagUnit              = fromBase imagUnit

instance (IntegralDomain a) => IntegralDomain (Poly a)

instance (AllowsRationalEmbedding a) => AllowsRationalEmbedding (Poly a) where
    fromRational = fromBase . fromRational

instance (Field a, Eq a, IntegralDomain a) => EuclideanRing (Poly a) where
    degree = pred . genericLength . canonCoeffs
    quotRem f g
        | degree f < degree g = (MkPoly [], f)
        | otherwise
        = let (q,r) = quotRem (f - q' * g) g
              q'    = leadingCoeff f / leadingCoeff g .* (iX^(degree f - degree g))
          in  (q + q', r)

-- | Liefert die Liste der Koeffizienten in kanonisierter Form,
-- also ohne abschließende Nuller.
canonCoeffs :: (Ring a, Eq a) => Poly a -> [a]
canonCoeffs = reverse . dropWhile (== zero) . reverse . unsafeCoeffs

-- | Liefert die Liste der Koeffizienten ohne eine Kanonisierung
-- vorzunehmen. Diese Funktion ist bezüglich der Gleichheit auf Polynomen
-- also nicht referentiell-transparent.
unsafeCoeffs :: Poly a -> [a]
unsafeCoeffs = unPoly

-- | Entfernt Koeffizienten, die sicher nicht null sein können.
-- Gedacht für Ringe /a/, in denen eine Überprüfung auf Nullheit
-- teuer (oder sogar unmöglich) ist. Wird nur intern in diesem Modul verwendet.
simplify :: (Ring a) => Poly a -> Poly a
simplify = MkPoly . reverse . dropWhile (not . couldBeNonZero) . reverse . unPoly

-- | Wertet ein Polynom an einer Stelle aus.
-- Das ist bei Ganzheitsringen (bei denen Ganzheitsgleichungen mitgeschleppt
-- werden müssen) ineffizient, siehe 'IntegralClosure.eval' für eine
-- bessere Möglichkeit.
eval :: (Ring a) => a -> Poly a -> a
eval x = foldr (\c val -> c + x*val) zero . unPoly
-- Auch möglich ist die Definition
-- > eval x = foldl' ((+) . (* x)) zero . reverse . unPoly.

-- | Wertet ein gegebenes Polynom in /0/ aus. Ist effizienter, aber semantisch
-- nicht von folgender Spezifikation zu unterscheiden:
--
-- > eval0 = eval zero.
eval0 :: (Ring a) => Poly a -> a
eval0 (MkPoly [])     = zero
eval0 (MkPoly (a:as)) = a

-- | Berechnet die Polynomdivision mit Rest für den Fall, dass das
-- Nennerpolynom normiert ist. Gegenüber 'quotRem' besitzt diese
-- Variante daher den Vorteil, über beliebigen Ringen (statt Körpern)
-- einsetzbar zu sein.
normedQuotRem :: (Ring a, Eq a) => Poly a -> Poly a -> (Poly a, Poly a)
normedQuotRem f g
    | g' == zero              = error "normedQuotRem: Nenner ist null!"
    | leadingCoeff g' /= unit = error "normedQuotRem: Nenner ist nicht normiert!"
    | n < m                   = (zero, f')
    | otherwise               =
        let (q,r) = normedQuotRem (f' - q' * g') g'
            q'    = leadingCoeff f' .* (iX^(fromIntegral (n - m)))
        in (q + q', r)
    where
    (f',g') = (MkPoly (canonCoeffs f),   MkPoly (canonCoeffs g))
    (n,m)   = (length (unsafeCoeffs f'), length (unsafeCoeffs g'))

instance (Field a, Eq a) => TestableAssociatedness (Poly a) where
    areAssociated p q
        | p == zero && q == zero = Just unit
        | p /= zero && q /= zero =
            let x = leadingCoeff q / leadingCoeff p
            in  if x .* p == q then Just (fromBase x) else Nothing
        | otherwise        = Nothing

infixl 7 .*
-- | Multiplikation mit Skalaren des Grundrings.
(.*) :: (Ring a) => a -> Poly a -> Poly a
x .* f = MkPoly $ map (x *) $ unPoly f

-- | Die formale Variable des Polynomrings /Poly a/.
iX :: (Ring a) => Poly a
iX = MkPoly [zero, unit]

-- | Gibt zu jedem Element sein zugehöriges konstantes Polynom.
fromBase :: a -> Poly a
fromBase x = MkPoly [x]

-- | Normiert ein Polynom.
normalize :: (Field a, Eq a) => Poly a -> Poly a
normalize p = recip (leadingCoeff p) .* p

-- | Liefert den Leitkoeffizienten (konventionsgemäß also niemals null).
-- Auf dem Nullpolynom wird eine Laufzeitausnahme geworfen.
leadingCoeff :: (Ring a, Eq a) => Poly a -> a
leadingCoeff = last . canonCoeffs

-- | Bestimmt die formale Ableitung.
derivative :: (Ring a) => Poly a -> Poly a
derivative (MkPoly xs) 
    | null xs   = MkPoly []
    | otherwise = simplify . MkPoly $ zipWith (*) (tail xs) $ map fromInteger [1..]

-- | Setzt zwei Polynome ineinander ein. Erfüllt folgende Spezifikation:
--
-- > eval x (compose f g) = eval (eval x g) f
compose
    :: (Ring a)
    => Poly a  -- ^ /f/
    -> Poly a  -- ^ /g/
    -> Poly a  -- ^ /f . g/
compose (MkPoly as) g = sum $ zipWith (\a i -> a .* g^i) as (map fromInteger [0..])

-- | Versucht, für ein gegebenes Polynom /f/ die Frage /ist es gleich 'iX'?/ zu
-- beantworten. Da kein diskreter Ring vorausgesetzt wird, kann natürlich
-- im Allgemeinen keine Entscheidung getroffen werden; wir fordern nur folgende
-- Spezifikation:
--
-- > couldBeNotX p == False  ==>  p == iX.
couldBeNotX :: (Ring a) => Poly a -> P.Bool
couldBeNotX (MkPoly [a0,a1])
    | couldBeNonZero a0 == False && couldBeNonZero (a1 - unit) == False = False
couldBeNotX _ = True

-- | Berechnet zu einem gegebenen Polynom /f/ seinen quadratfreien Anteil (als
-- normiertes Polynom), also /g/ mit /f = dg/, wobei /d/ den größten
-- gemeinsamen Teiler von /f/ und /f'/ bezeichne.
squarefreePart :: (Field a, IntegralDomain a, Eq a) => Poly a -> Poly a
squarefreePart f = let (u,v,s,t) = gcd f (derivative f) in normalize s

-- | Mischt zwei Listen vermöge einem gegebenen Operator und einem
-- Standardargument, was genau dann verwendet wird, wenn eine der beiden Listen
-- kürzer als die andere ist.
zipWithDefault :: (a -> a -> b) -> a -> [a] -> [a] -> [b]
zipWithDefault (#) zero = go
    where
    go []     ys     = map (zero #) ys
    go (x:xs) []     = map (# zero) (x:xs)
    go (x:xs) (y:ys) = (x#y) : go xs ys
