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

foldD :: Monoid a => (a -> a -> a) -> [a] -> a
foldD _ []       = mempty
foldD f ds       = foldr1 f ds

hsepPC = foldD (PC.<+>)
hsepPCP = foldD (PCP.<+>)

sepPC xs = hsepPC xs PC.<|> PC.vcat xs
sepPCP xs = hsepPCP xs PCP.<|> PCP.vcat xs

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

bench :: SExpr -> TestingProc
bench t conf = do
  let s | target conf == bernardyMeasureTarget = render (pretty t :: DM)
        | target conf == bernardyPaperTarget = render (pretty t :: CDoc)
        | target conf == bernardyLibTarget = PC.render (prettyPC t)
        | target conf == bernardyPatchedTarget = PCP.render (prettyPCP t)
  return s

core :: TestingFun
core conf = do
  let (t, _) = testExpr (size conf) 0
  return $ C.nfAppIO (instrument $ bench t) conf

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
