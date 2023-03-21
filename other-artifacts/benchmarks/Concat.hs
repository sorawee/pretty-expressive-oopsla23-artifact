module Main where

import Prelude hiding ((<>))

import qualified Text.PrettyPrint.Leijen   as WL
import qualified Text.PrettyPrint.Compact  as PC
import qualified TextPatched.PrettyPrint.Compact  as PCP
import PrinterPaper.BernardyPaper

import Lib.BenchTool

ppWL :: Int -> WL.Doc
ppWL 0 = WL.text ""
ppWL n = ppWL (n - 1) WL.<> WL.text "line"

ppPC :: Int -> PC.Doc ()
ppPC 0 = PC.text ""
ppPC n = ppPC (n - 1) PC.<> PC.text "line"

ppPCP :: Int -> PCP.Doc ()
ppPCP 0 = PCP.text ""
ppPCP n = ppPCP (n - 1) PCP.<> PCP.text "line"

pp :: Doc d => Int -> d
pp 0 = text ""
pp n = pp (n - 1) <> text "line"

bench :: TestingProc
bench conf = do
  let s | target conf == bernardyPaperTarget = render (pp (size conf) :: CDoc)
        | target conf == bernardyLibTarget = PC.render $ ppPC (size conf)
        | target conf == bernardyPatchedTarget = PCP.render $ ppPCP (size conf)
        | target conf == leijenTarget = wlRender $ ppWL (size conf)
        | otherwise = error "impossible"
  return s

main :: IO ()
main = do
  runIt
    "concat"
    (defaultConfig { size = 10000 })
    (validateTargets
      [ leijenTarget
      , bernardyPatchedTarget
      , bernardyLibTarget
      , bernardyPaperTarget]
      (\_ -> Nothing))
    bench
