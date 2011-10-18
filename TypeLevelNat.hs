-- | Dieses Modul stellt die natürlichen Zahlen (bei null beginnend) auf
-- Typebene bereit. Diese nutzen wir für rudimentäre Typsicherheit im Umgang
-- mit Matrizen.
--
-- Kernstück sind die Typklasse 'ReifyNat' und die Funktion 'reflectNat',
-- die sich einem geeigneten Sinn zueinader invers verhalten -- es gilt
-- folgende Spezifikation:
--
-- > reflectNat n reifyNat == n
--
-- für alle /n >= 0/. Siehe
-- <http://www.haskell.org/haskellwiki/Type_arithmetic>.
{-# LANGUAGE EmptyDataDecls, RankNTypes #-}
module TypeLevelNat
    ( Z, S, N0, N1, N2, N3, N4
    , ReifyNat(..), reflectNat, reflectPositiveNat
    , module Proxy
    , check_TypeLevelNat
    ) where

import Prelude hiding (pred,succ)
import Nat
import Proxy
import Testing

-- | Darstellung der Null (Zero)
data Z

-- | Darstellung des Nachfolgers /S n/ einer durch den Typ /n/ dargestellen
-- natürlichen Zahl (Successor)
data S n

-- | Null
type N0 = Z

-- | Eins
type N1 = S N0

-- | Zwei
type N2 = S N1

-- | Drei
type N3 = S N2

-- | Vier
type N4 = S N3

-- | Klasse, um natürliche Zahlen der Typebene in Werte zu wandeln.
-- Das Gegenstück ist 'reflectNat'.
class ReifyNat n where
    -- | Gibt den zur Zahl /n/ gehörigen Wert zurück.
    reifyNat :: Proxy n -> Nat

instance ReifyNat Z where reifyNat _ = 0

instance (ReifyNat n) => ReifyNat (S n) where
    reifyNat = (+ 1) . reifyNat . fmap pred

-- | Bringt eine auf Wertebene gegebene natürliche Zahl aufs Typniveau.
reflectNat
    :: Nat  -- ^ die zu liftende natürliche Zahl
    -> (forall n. (ReifyNat n) => Proxy n -> r)
            -- ^ eine polymorphe Continuation, die Darstellungen aller Zahlen
            -- auf Typebene akzeptiert und ein Ergebnis vom Typ /r/ produziert
    -> r    -- ^ das Endergebnis
reflectNat n k
    | n == 0    = k (undefined :: Proxy Z)
    | n  < 0    = error "TypeLevelNat.reflectNat: Argument negativ"
    | otherwise = reflectNat (n - 1) $ k . fmap succ

-- | Bringt eine auf Wertebene gegebene positive natürliche Zahl aufs
-- Typniveau; auf Typebene hat man dann einen Typ der Form /S n/.
reflectPositiveNat
    :: Nat  -- ^ die zu liftende positive Zahl
    -> (forall n. (ReifyNat n) => Proxy (S n) -> r)
            -- ^ eine polymorphe Continuation, die Darstellungen aller
            -- positiven Zahlen auf Typebene akzeptiert und ein Ergebnis vom
            -- Typ /r/ produziert
    -> r    -- ^ das Endergebnis
reflectPositiveNat n k
    | n  < 1    = error "TypeLevelNat.reflectPositiveNat: Argument negativ oder Null"
    | n == 1    = k (undefined :: Proxy (S Z))
    | otherwise = reflectPositiveNat (n - 1) $ k . fmap succ

pred :: S n -> n
pred = undefined

succ :: n -> S n
succ = undefined

check_TypeLevelNat :: IO ()
check_TypeLevelNat = mapM_ quickCheck $
    [ forAll arbitrary $ \(NonNegative n) -> reflectNat         n reifyNat == n
    , forAll arbitrary $ \(Positive    n) -> reflectPositiveNat n reifyNat == n
    ]
