module Main where

import qualified Text.PrettyPrint.Leijen   as WL

import Lib.BenchTool

pp :: Int -> WL.Doc
pp 0 = WL.text "line"
pp n = WL.group (pp (n - 1) WL.<> WL.line WL.<> WL.text "line")

bench :: TestingProc
bench conf = do
  let s = wlRender $ pp (size conf)
  return s

main :: IO ()
main = do
  runIt
    "flatten"
    (defaultConfig { size = 1000 })
    (validateTargets
      [leijenTarget]
      (\_ -> Nothing))
    bench
