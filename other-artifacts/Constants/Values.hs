module Constants.Values where

--------------------------------------------------------------------------------
-- Hacks to make width limit customizable
-- from https://stackoverflow.com/questions/16811376/simulate-global-variable
--------------------------------------------------------------------------------

import System.IO.Unsafe
import Data.IORef

{-# NOINLINE pageWidthIO #-}
pageWidthIO :: IORef Int
pageWidthIO = unsafePerformIO $ newIORef 80

{-# NOINLINE widthlimit #-}
widthlimit :: Int
widthlimit = unsafePerformIO $ (readIORef pageWidthIO)
