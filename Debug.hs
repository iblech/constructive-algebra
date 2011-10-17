module Debug (debug, warn) where

import Debug.Trace

doDebug :: Bool
doDebug = False

{-# NOINLINE debug #-}
debug :: String -> a -> a
debug msg x
    | doDebug   = trace msg x
    | otherwise = x

{-# NOINLINE warn #-}
warn :: String -> a -> a
warn = trace
