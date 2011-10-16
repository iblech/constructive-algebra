-- | Dieses Modull stellt die Typklasse 'EuclideanRing' für euklidische Ringe
-- und die wichtige Funktion 'gcd' zur Bestimmung größter gemeinsamer Teiler
-- zur Verfügung.
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Euclidean
    ( EuclideanRing(..), ER(..)
    , gcd, gcd', areCoprime
    , euclidChain
    , props_Euclidean
    ) where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/), negate)
import qualified Prelude as P
import Ring
import Field
import Nat
import Proxy
import Testing
import Data.Maybe

-- | Typklasse für euklidische Ringe, also Integritätsbereiche /R/ zusammen mit
-- einer Normabbildung von /R \ {0}/ in die natürlichen Zahlen mit null, sodass
-- folgendes Axiom erfüllt ist:
--
-- Für jedes Element /x/ aus /R/ und jedes von null verschiedene Element /y/
-- aus /R/ gilt: /Entweder/ ist /y/ ein Teiler von /x/, /oder/ es existiert
-- ein von null verschiedener Rest /r/ derart, dass /y/ ein Teiler von /x - r/
-- ist und die Norm von /r/ echt kleiner als die von /y/ ist.
class (IntegralDomain a) => EuclideanRing a where
    -- | Die Normabbildung. Muss auf dem Nullelement nicht definiert sein.
    degree :: a -> Nat

    -- | Division mit Rest.
    quotRem
        :: a      -- ^ Dividend /x/
        -> a      -- ^ Divisor /y/, nicht null
        -> (a,a)  -- ^ /(q,r)/ mit /x = qy + r/ und /N(r) < N(y)/

-- | Dummytyp, um überlappende Instanzdeklarationen vermeiden zu können.
newtype ER a = ER { unER :: a }
    deriving (Eq,Ring,Integral,Real,Enum,Ord,IntegralDomain,Field,EuclideanRing,Num,Fractional,HasTestableAssociatedness,HasFloatingApprox)
instance (Show a, EuclideanRing a) => Show (ER a) where
    show        = show . unER
    showsPrec i = showsPrec i . unER
    showList    = showList . map unER

instance (Field a) => EuclideanRing (F a) where
    degree x
        | x == zero = error "degree zero"
        | otherwise = 1
    quotRem x y
        | y == zero = error "quotRem: Division durch null"
        | otherwise = (x/y, zero)

instance EuclideanRing Integer where
    degree  = abs
    quotRem = P.quotRem

-- | Bestimmt einen größten gemeinsamen Teiler über den euklidischen
-- Algorithmus. Dieser wird nicht in irgendeiner kanonisierten Form geliefert
-- (eine solche gibt es in einem allgemeinen euklidischen Ring ja auch gar
-- nicht), sondern sollte nur als bis auf Assoziiertheit interpretiert werden.
gcd
    :: (EuclideanRing a)
    => a   -- ^ /x/
    -> a   -- ^ /y/
    -> (a,a,a,a)  -- ^ /(u,v,s,t)/, mit /d = ux + vy/ ein größter gemeinsamer
                  -- Teiler von /x/ und /y/, /x = ds/ und /y = dt/.
gcd = gcd_ (\_ _ -> Nothing)

-- | Wie 'gcd', aber mit folgender Zusatzeigenschaft:
--
-- Sollte /x/ zu /y/ assoziiert sein (d.h. sollte ein /u/ mit /y = ux/
-- existieren), wird garantiert, dass der Aufruf /gcd' x y/ zu /(1,0,1,u)/
-- führt.
--
-- Bei /gcd/ dagegen kann auch /(0,1,u,1)/ zurückgegeben werden.
-- Dies ist im "Smith"-Modul sehr wichtig, um Terminierung beim Algorithmus
-- für die Smitsche Normalform zu gewährleisten.
gcd' :: (EuclideanRing a, HasTestableAssociatedness a) => a -> a -> (a,a,a,a)
gcd' = gcd_ areAssociated

-- | Wie 'gcd', nur dass der zu verwendende Assoziiertheitstest explizit
-- vorgegeben werden kann.
gcd_ :: (EuclideanRing a) => (a -> a -> Maybe a) -> a -> a -> (a,a,a,a)
gcd_ associatednessTest a b
    | b == zero
    = (unit, zero, unit, zero)
    | Just u <- associatednessTest a b
    = (unit, zero, unit, u)
    | otherwise
    = (u,v,s,t)
        where
        (u',v',s',t') = gcd_ associatednessTest b r
        (q,r)         = a `quotRem` b
        u             = v'
        v             = u' - q * v'
        s             = t' + q * s'
        t             = s'

props_gcd :: (EuclideanRing a, Show a, Arbitrary a) => Proxy a -> [Property]
props_gcd x =
    [ property $ \a b -> b /= zero ==>
          let (q,r) = a `quotRem` b
              _     = a `asTypeOfProxy` x
          in   a == b * q + r  &&  (r == zero || degree r < degree b)
    , property $ \a b ->
          let (u,v,s,t) = gcd a b
              d         = u*a + v*b
              _         = a `asTypeOfProxy` x
          in  d*s == a && d*t == b
          -- Ungetestet bleibt die Forderung, dass d auch wirklich größter
          -- gemeinsamer Teiler ist.
    ]

props_gcdInteger :: [Property]
props_gcdInteger =
    [ property $ \a b ->
          let (u,v,_,_) = gcd a b
              d         = u*a + v*b
              _         = a `asTypeOf` (0 :: Integer)
          in flip all [1..min a b] $ \d' ->
          not (a `mod` d' == 0 && b `mod` d' == 0) || d `mod` d' == 0
    ]

-- | Testet, ob zwei übergebene Ringelemente zueinander teilerfremd sind.
areCoprime :: (EuclideanRing a, HasTestableAssociatedness a) => a -> a -> Bool
areCoprime x y = isJust $ areAssociated unit d
    where
    d         = u*x + v*y
    (u,v,_,_) = gcd x y

-- | Eine Folge /(S_0,...,S_n)/ von Polynomen heißt genau dann /Sturmkette
-- bezüglich des Intervalls [a,b]/, wenn für alle /x aus [a,b]/ gilt:
-- Sollte /S_k(x) = 0/ für ein /k/ mit /0 < k < n/ sein, so gilt
-- /S_(k-1)(x) S_(k+1)(x) < 0/.
--
-- Zu jeder rationalen Funktion /R\/S/, wobei /R/ und /S/ Polynome sind,
-- gibt es /die zugehörige Sturmkette/. Diese ist definiert als
-- /(S_0,...,S_n)/, wobei /S_k = P_k\/P_n/ (die Division geht auf) und die
-- /P_i/ aus dem euklidischen Algorithmus, angewendet auf /R/ und /S/ stammen,
-- also
--
-- > P_0 = S
-- > P_1 = R
-- > P_(k-1) = Q_k P_k - P_(k+1)
--
-- für gewisse Reste /P_(k+1)/ für alle /k >= 1/ erfüllen.
--
-- Angewendet wird die Funktion 'euclidChain' in "ZeroRational" auf Polynome.
-- Derart spezialisiert bestimmt sie zu zwei gegebenen Polynomen /R/ und /S/ 
-- ihre zugehörige Sturmkette. Sie funktioniert aber auch allgemeiner in
-- beliebigen euklidischen Ringen.
--
-- (Der Begriff der /zum Bruch zugeordneten/ Euklidkette ist eigentlich nicht
-- wohldefiniert, da verschiedene Wahlen des Rests in 'quotRem' zu
-- verschiedenen Ketten führen. Das ist aber auch das einzige Hindernis:
-- Trifft man die Wahlen konsistent, etwa indem man bei ganzen Zahlen fordert,
-- dass der Rest positiv ist, so sind die Ketten aller Darstellungen eines
-- Bruchs gleich.)
euclidChain :: (EuclideanRing a) => a -> a -> [a]
euclidChain a b = map (fst . (`quotRem` d)) xs
    where
    xs = euclidChain' b a
    d  = last xs

-- Vorzeichenkonvention für sturmChain
euclidChain' :: (EuclideanRing a) => a -> a -> [a]
euclidChain' a b
    | b == zero = [a]
    | otherwise = a : euclidChain' b (negate . snd $ a `quotRem` b)

props_Euclidean :: [Property]
props_Euclidean = concat
    [ props_gcd (undefined :: Proxy Integer)
    , props_gcd (undefined :: Proxy (F Rational))
    , props_gcdInteger
    ]
