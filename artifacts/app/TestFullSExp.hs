module Main where

import Prelude hiding ((<>))
import BernardyPaper
import qualified Criterion.Main as C
import Text.Printf
import LibTest
import qualified Text.PrettyPrint.Compact as PC
import qualified TextPatched.PrettyPrint.Compact as PCP

data SExpr = SExpr [SExpr] | Atom String
  deriving Show

testExpr 0 c = (Atom $ show c, c + 1)
testExpr n c = (SExpr [t1, t2], c2)
  where (t1, c1) = testExpr (n-1) c
        (t2, c2) = testExpr (n-1) c1

prettyPC ::  SExpr -> PC.Doc ()
prettyPC  (Atom s)    = PC.text s
prettyPC  (SExpr xs)  =   PC.text "(" PC.<>
                        (PC.sep $ map prettyPC xs) PC.<>
                        PC.text ")"

prettyPCP ::  SExpr -> PCP.Doc ()
prettyPCP  (Atom s)    = PCP.text s
prettyPCP  (SExpr xs)  =   PCP.text "(" PCP.<>
                        (PCP.sep $ map prettyPCP xs) PCP.<>
                        PCP.text ")"

pretty :: Doc d => SExpr -> d
pretty  (Atom s)    = text s
pretty  (SExpr xs)  =   text "(" <>
                        (sep $ map pretty xs) <>
                        text ")"

bench :: TestingProc
bench conf = do
  let s | target conf == bernardyMeasureTarget = render (pretty t :: DM)
        | target conf == bernardyPaperTarget = render (pretty t :: CDoc)
        | target conf == bernardyLibTarget = PC.render (prettyPC t)
        | target conf == bernardyPatchedTarget = PCP.render (prettyPCP t)
  return s
  where
    (t, _) = testExpr (size conf) 0

core :: TestingFun
core conf = do
  return $ C.nfAppIO (instrument bench) conf

main = do
  runIt
    "TestFullSExp"
    (defaultConfig { size = 10 })
    (validateTargets
      [ bernardyMeasureTarget
      , bernardyPaperTarget
      , bernardyLibTarget
      , bernardyPatchedTarget]
      (\conf -> Nothing))
    core
