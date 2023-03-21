module Main where

import Prelude hiding ((<>))

import PrinterPaper.BernardyPaper
import qualified Text.PrettyPrint.Compact as PC
import qualified TextPatched.PrettyPrint.Compact as PCP
import qualified Text.PrettyPrint.Leijen   as WL

import Lib.BenchTool
import Lib.SExpTool

testExpr :: Int -> Int -> (SExpr, Int)
testExpr 0 c = (Atom $ show c, c + 1)
testExpr n c = (SExpr [t1, t2], c2)
  where (t1, c1) = testExpr (n-1) c
        (t2, c2) = testExpr (n-1) c1

prettyPC ::  SExpr -> PC.Doc ()
prettyPC  (Atom s)    = PC.text s
prettyPC  (SExpr xs)  =   PC.text "(" PC.<>
                        (sepPC $ map prettyPC xs) PC.<>
                        PC.text ")"

prettyPCP ::  SExpr -> PCP.Doc ()
prettyPCP  (Atom s)    = PCP.text s
prettyPCP  (SExpr xs)  =   PCP.text "(" PCP.<>
                        (sepPCP $ map prettyPCP xs) PCP.<>
                        PCP.text ")"

pretty :: Doc d => SExpr -> d
pretty  (Atom s)    = text s
pretty  (SExpr xs)  =   text "(" <>
                        (sep $ map pretty xs) <>
                        text ")"

prettyWL :: SExpr -> WL.Doc
prettyWL  (Atom s)  = WL.text s
prettyWL  (SExpr xs)  = WL.text "(" WL.<> (WL.align (WL.sep $ map prettyWL xs)) WL.<> WL.text ")"

bench :: SExpr -> TestingProc
bench t conf = do
  let s | target conf == bernardyPaperTarget = render (pretty t :: CDoc)
        | target conf == bernardyLibTarget = PC.render (prettyPC t)
        | target conf == bernardyPatchedTarget = PCP.render (prettyPCP t)
        | target conf == leijenTarget = wlRender (prettyWL t)
        | otherwise = error "impossible"
  return s

core :: TestingProc
core conf =
  let (t, _) = testExpr (size conf) 0 in
  (bench t) conf

main :: IO ()
main = do
  runIt
    "sexp-full"
    (defaultConfig { size = 10 })
    (validateTargets
      [ bernardyPaperTarget
      , bernardyLibTarget
      , leijenTarget
      , bernardyPatchedTarget]
      (\_ -> Nothing))
    core
