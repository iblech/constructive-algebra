-- | Dieses Modul stellt für jeden Ring /a/ seinen Polynomring /Poly a/ in
-- einer Variablen zur Verfügung.
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, TypeFamilies #-}
module Polynomial
    ( Poly(MkPoly)
    , NormedPoly(..), mkNormedPoly
    , canonCoeffs, canonCoeffs', unsafeCoeffs
    , fromBase, eval, eval0
    , normedQuotRem
    , (.*), iX
    , normalize, normalize', leadingCoeff
    , derivative, content, compose
    , squarefreePart
    , couldBeNotX
    , normedPolyProp
    , simpleNonconstantRationalPoly
    ) where

import Prelude hiding (gcd, (+), (-), (*), (/), (^), negate, recip, fromInteger, fromRational, quotRem, sum)
import qualified Prelude as P
import Data.List (intersperse, genericLength, foldl1')
import Ring
import Field
import Euclidean
import Testing
import Control.Monad
import Data.Ratio
import NumericHelper
import Proxy

-- | Typ der Polynome über 'a', repräsentiert durch die zugehörigen Folgen der
-- Koeffizienten, von niedrigster zur höchsten Potenz geordnet. Die Darstellung
-- ist wegen möglicher abschließender Nuller natürlich nicht eindeutig.
newtype Poly a = MkPoly { unPoly :: [a] }
  deriving (Functor)

-- | Kennzeichnung für normierte Polynome. Dabei sei sogar vereinbart,
-- dass es keine abschließenden Nuller gibt, also dass der höchste Koeffizient
-- schon selbst genau /1/ ist.
--
-- Dient auch zum einfachen Testen von Eigenschaften normierter Polynome,
-- Beispielanwendung:
--
-- > forAll arbitrary $ \MkNormedPoly p -> ...
newtype NormedPoly a = MkNormedPoly { unNormedPoly :: Poly a } deriving (Show,Eq,Functor)

-- | Kluger Konstruktor für 'NormedPoly': Er prüft, ob wirklich ein normiertes
-- Polynom vorliegt (wirft sonst eine Laufzeitausnahme) und kanonisiert es.
mkNormedPoly :: (Ring a, Eq a) => Poly a -> NormedPoly a
mkNormedPoly f
    | last as == unit = MkNormedPoly (MkPoly as)
    | otherwise       = error "mkNormedPoly auf einem nicht-normierten Polynom!"
    where
    as = canonCoeffs f

instance (Ring a, Eq a, Show a) => Show (Poly a) where
  show f = addZero $ concat . intersperse " + " $ filter (not . null) $ zipWith mult (canonCoeffs f) vars
      where
      vars = "" : "X" : map (("X^" ++) . show) [(2::Integer)..]
      mult x v
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
	go []     _  = []
	go (a:as) bs = zipWithDefault (+) zero (map (a *) bs) (zero:go as bs)
    negate = fmap negate
    fromInteger = MkPoly . (:[]) . fromInteger
    zero = MkPoly []
    unit = MkPoly [unit]

instance (HasConjugation a) => HasConjugation (Poly a) where
    type RealSubring (Poly a) = Poly (RealSubring a)
    conjugate (MkPoly xs) = MkPoly (map conjugate xs)
    realPart  (MkPoly xs) = MkPoly (map realPart xs)
    imagUnit              = fromBase imagUnit

instance (IntegralDomain a) => IntegralDomain (Poly a)

instance (HasRationalEmbedding a) => HasRationalEmbedding (Poly a) where
    fromRational = fromBase . fromRational

instance (Field a) => EuclideanRing (Poly a) where
    degree = pred . genericLength . canonCoeffs
    quotRem f g
        | degree f < degree g = (MkPoly [], f)
        | otherwise
        = let (q,r) = quotRem (f - q' * g) g
              q'    = leadingCoeff f / leadingCoeff g .* (iX^(degree f - degree g))
          in  (q + q', r)

instance (Arbitrary a, Ring a) => Arbitrary (Poly a) where
    -- Künstlich hinten 0er anfügen, damit auch Polynome getestet werden,
    -- welche nicht in kanonisierter Form vorliegen.
    arbitrary = uncanonify =<< liftM MkPoly arbitrary

uncanonify :: (Ring a) => Poly a -> Gen (Poly a)
uncanonify (MkPoly as) = do
    i  <- elements [0..5]
    return . MkPoly $ as ++ replicate i zero

instance (Arbitrary a, Ring a) => Arbitrary (NormedPoly a) where
    arbitrary = liftM (MkNormedPoly . MkPoly . (++ [unit])) arbitrary

-- | Liefert die Liste der Koeffizienten in kanonisierter Form,
-- also ohne abschließende Nuller.
canonCoeffs :: (Ring a, Eq a) => Poly a -> [a]
canonCoeffs = reverse . dropWhile (== zero) . reverse . unsafeCoeffs

-- | Liefert für normierte Polynome die Liste der Koeffizienten in
-- kanonisierter Form, also ohne abschließende Nuller. Anders als 'canonCoeffs'
-- benötigen wir hier nicht die Diskretheitsvoraussetzung an den Ring, weil
-- wir vereinbart haben, dass Polynome in 'NormedPoly' sogar \"echt\",
-- also ohne abschließende Nuller, normiert sind.
canonCoeffs' :: (Ring a) => NormedPoly a -> [a]
canonCoeffs' = unsafeCoeffs . unNormedPoly

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
eval0 (MkPoly [])    = zero
eval0 (MkPoly (a:_)) = a

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

instance (Field a, Eq a) => HasTestableAssociatedness (Poly a) where
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

-- | Normiert ein Polynom. Angewendet aufs Nullpolynom wird eine Laufzeitausnahme
-- geworfen.
normalize :: (Field a, Eq a) => Poly a -> Poly a
normalize p = MkPoly $ map (a *) as where as = canonCoeffs p; Just a = recip (last as)
-- Semantisch nicht zu unterscheiden wäre die Alternativdefinition
-- > normalize p = recip (leadingCoeff p) .* p.
-- Diese hat den Vorteil, dass das zurückgegebene Polynom gleich schon
-- in kanonisierter Form vorliegt, also keine unnötigen Nullen besitzt.
-- Das erhöht die Effizienz in "IntegralClosure" bei der Berechnung von
-- Ganzheitsgleichungen.

-- | Normiert ein Polynom und markiert es als solches.
normalize' :: (Field a, Eq a) => Poly a -> NormedPoly a
normalize' = MkNormedPoly . normalize

-- | Liefert den Leitkoeffizienten (konventionsgemäß also niemals null).
-- Auf dem Nullpolynom wird eine Laufzeitausnahme geworfen.
leadingCoeff :: (Ring a, Eq a) => Poly a -> a
leadingCoeff = last . canonCoeffs

-- | Bestimmt die formale Ableitung.
derivative :: (Ring a) => Poly a -> Poly a
derivative (MkPoly xs) 
    | null xs   = MkPoly []
    | otherwise = simplify . MkPoly $ zipWith (*) (tail xs) $ map fromInteger [1..]

-- | Berechnet den Inhalt eines nicht-verschwindenden Polynoms über den
-- rationalen Zahlen.
content :: Poly Rational -> Rational
content f
    | abs a == 1 = fromInteger . abs $ foldl1' P.gcd $ map unsafeFromRational as 
    | otherwise  = content (abs a .* f) / abs a
    where
    as = canonCoeffs f
    a  = fromInteger . foldl1' P.lcm $ map denominator as

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
squarefreePart :: (Field a) => Poly a -> NormedPoly a
squarefreePart f = let (_,_,s,_) = gcd f (derivative f) in normalize' s

-- | Mischt zwei Listen vermöge einem gegebenen Operator und einem
-- Standardargument, was genau dann verwendet wird, wenn eine der beiden Listen
-- kürzer als die andere ist.
zipWithDefault :: (a -> a -> b) -> a -> [a] -> [a] -> [b]
zipWithDefault (#) def = go
    where
    go []     ys     = map (def #) ys
    go (x:xs) []     = map (# def) (x:xs)
    go (x:xs) (y:ys) = (x#y) : go xs ys

-- | Prüft, ob beim gegebenen Polynom die Vereinbarung, dass Elemente von
-- 'NormedPoly' auch ohne Wegwerfen abschließender Nullkoeffizienten schon
-- normiert sind, erfüllt ist. Nützlich zur Formulierung von Tests.
normedPolyProp :: (Ring a, Eq a) => NormedPoly a -> Bool
normedPolyProp (MkNormedPoly (MkPoly as)) = last as == unit

simpleNonconstantRationalPoly :: Gen (Poly Rational)
simpleNonconstantRationalPoly = do
    n  <- elements [1,2,3]
    as <- replicateM n simpleRational
    a  <- simpleNonzeroRational
    return $ MkPoly $ as ++ [a]

props_Polynomial :: [Property]
props_Polynomial = props_ringAxioms (undefined :: Proxy (Poly Rational))
