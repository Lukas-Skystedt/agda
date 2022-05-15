module Agda.Mimer.Debug where

import Data.IORef (IORef, writeIORef, readIORef, newIORef)
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad (when)

mlog' :: Monad m => String -> m ()
mlog' str = doLog str $ return ()

{-# NOINLINE shouldLog #-}
shouldLog :: IORef Bool
shouldLog = unsafePerformIO $ newIORef False

mlog :: Monad m => String -> m ()
mlog str =  do
  let l = unsafePerformIO $ readIORef shouldLog
  when l $ doLog str (return ())

doLog :: String -> a -> a
doLog str e = unsafePerformIO $ do
  appendFile "/home/lukas/mimer.log" (str ++ "\n")
  return e
