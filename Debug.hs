-- | Dieses Modul stellt die Logging-Funktionen 'debug' und 'warn' zur
-- Verfügung.
module Debug (debug, warn) where

import Debug.Trace

-- | Konstante, die angibt, ob Debugging-Meldungen ausgegeben werden sollen.
doDebug :: Bool
doDebug = False

{-# NOINLINE debug #-}
-- | /debug msg x/ verhält sich semantisch wie /x/, gibt aber (bei gesetztem
-- 'doDebug') die Meldung /msg/ auf der Standardfehlerausgabe aus.
debug :: String -> a -> a
debug msg x
    | doDebug   = trace msg x
    | otherwise = x

{-# NOINLINE warn #-}
-- | /warn msg x/ verhält sich semantisch wie /x/, gibt aber (unabhängig von
-- 'doDebug') die Meldung /msg/ auf der Standardfehlerausgabe aus.
warn :: String -> a -> a
warn = trace
