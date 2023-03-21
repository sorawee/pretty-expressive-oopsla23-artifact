module Main where

import Prelude hiding ((<>))

import qualified Data.Text as TXT
import Data.Aeson.Types
import Data.Foldable (toList)

import qualified Text.PrettyPrint.Compact as PC
import qualified TextPatched.PrettyPrint.Compact as PCP
import qualified Text.PrettyPrint.Leijen   as WL
import PrinterPaper.BernardyPaper

import Lib.BenchTool
import Lib.JSONTool
import Lib.SExpTool

import System.Environment

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

convert :: Value -> SExpr
convert (Array a) = SExpr $ map convert $ toList a
convert (String s) = Atom $ TXT.unpack s
convert _ = error "impossible"

core :: TestingProc
core conf = do
  benchData <- getEnv "BENCHDATA"
  let fname = benchData ++ "/random-tree-" ++ (show $ size conf) ++ ".sexp"
  tree <- readJSONValue fname
  ret <- (bench $ convert tree) conf
  return ret

main :: IO ()
main = do
  runIt
    "sexp-random"
    (defaultConfig { size = 1 })
    (validateTargets
      [ bernardyPaperTarget
      , bernardyLibTarget
      , leijenTarget
      , bernardyPatchedTarget]
      (\_ -> Nothing))
    core
