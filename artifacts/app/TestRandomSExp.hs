module Main where

import Prelude hiding ((<>))
import BernardyPaper
import qualified Criterion.Main as C
import Text.Printf
import LibTest
import qualified Text.PrettyPrint.Compact as PC
import qualified TextPatched.PrettyPrint.Compact as PCP

import qualified Data.Text as TXT
import Data.Aeson.Parser
import Data.Aeson.Types
import Data.Foldable (toList)
import qualified Data.ByteString as BS
import Data.Attoparsec.ByteString

data SExpr = SExpr [SExpr] | Atom String
  deriving Show

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

bench :: SExpr -> TestingProc
bench t conf = do
  let s | target conf == bernardyMeasureTarget = render (pretty t :: DM)
        | target conf == bernardyPaperTarget = render (pretty t :: CDoc)
        | target conf == bernardyLibTarget = PC.render (prettyPC t)
        | target conf == bernardyPatchedTarget = PCP.render (prettyPCP t)
  return s

convert :: Value -> SExpr
convert (Array a) = SExpr $ map convert $ toList a
convert (String s) = Atom $ TXT.unpack s
convert _ = error "impossible"

core :: TestingFun
core conf = do
  let fname | size conf == -1 = "benchdata/tmp.sexp"
            | otherwise = "benchdata/random-tree-" ++ (show $ size conf) ++ ".sexp"

  tree <- readJSONValue fname
  return $ C.nfAppIO (instrument (bench $ convert tree)) conf

readJSONValue fname = do
  inptxt <- BS.readFile fname
  let Right inpJson = parseOnly json' inptxt
  return inpJson

main = do
  runIt
    "TestRandomSExp"
    (defaultConfig { size = 1 })
    (validateTargets
      [ bernardyMeasureTarget
      , bernardyPaperTarget
      , bernardyLibTarget
      , bernardyPatchedTarget]
      (\conf -> Nothing))
    core
