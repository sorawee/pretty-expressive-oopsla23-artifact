module Main where

import qualified Criterion.Main as C
import qualified Text.PrettyPrint.Leijen   as WL

import Lib.Bench

pp :: Int -> WL.Doc
pp 0 = WL.text "line"
pp n = WL.group (pp (n - 1) WL.<> WL.line WL.<> WL.text "line")

bench :: TestingProc
bench conf = do
  let s = wlRender $ pp (size conf)
  return s

core :: TestingFun
core conf = do
  return $ C.nfAppIO (instrument bench) conf

main :: IO ()
main = do
  runIt
    "TestWadlerFlatten"
    (defaultConfig { size = 1000 })
    (validateTargets
      [wadlerTarget]
      (\_ -> Nothing))
    core
