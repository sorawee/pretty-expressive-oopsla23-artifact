module Main where

import qualified TestFillSep as FillSep
import qualified TestFullSExp as FullSExp
import qualified TestJSONLarge as JSONLarge

main :: IO ()
main =
  FillSep.doIt
  -- FullSExp.doIt
  -- JSONLarge.doIt
