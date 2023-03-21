module Main where

import qualified Criterion.Main as C
import Text.Printf
import LibTest
import Data.Aeson.Parser
import Data.Aeson.Types
import Data.Aeson.KeyMap (toAscList)
import Data.Foldable (toList)
import qualified Data.ByteString as BS
import Data.Attoparsec.ByteString
import qualified Text.PrettyPrint.Leijen   as WL
import qualified Text.PrettyPrint.Compact  as PC
import qualified TextPatched.PrettyPrint.Compact  as PCP

prettiestJSON :: Value -> PC.Doc ()
prettiestJSON (Bool True)  = PC.text "true"
prettiestJSON (Bool False) = PC.text "false"
prettiestJSON (Object o)   = PC.encloseSep (PC.text "{") (PC.text "}") (PC.text ",") (map prettyKV $ toAscList o)
  where prettyKV (k,v)     = PC.text (show k) PC.<> PC.text ":" PC.<+> prettiestJSON v
prettiestJSON (String s)   = PC.string (show s)
prettiestJSON (Array a)    = PC.encloseSep (PC.text "[") (PC.text "]") (PC.text ",") (map prettiestJSON $ toList a)
prettiestJSON Null         = PC.mempty
prettiestJSON (Number n)   = PC.text (show n)

prettiestJSONP :: Value -> PCP.Doc ()
prettiestJSONP (Bool True)  = PCP.text "true"
prettiestJSONP (Bool False) = PCP.text "false"
prettiestJSONP (Object o)   = PCP.encloseSep (PCP.text "{") (PCP.text "}") (PCP.text ",") (map prettyKV $ toAscList o)
  where prettyKV (k,v)     = PCP.text (show k) PCP.<> PCP.text ":" PCP.<+> prettiestJSONP v
prettiestJSONP (String s)   = PCP.string (show s)
prettiestJSONP (Array a)    = PCP.encloseSep (PCP.text "[") (PCP.text "]") (PCP.text ",") (map prettiestJSONP $ toList a)
prettiestJSONP Null         = PCP.mempty
prettiestJSONP (Number n)   = PCP.text (show n)

wlJSON :: Value -> WL.Doc
wlJSON (Bool True)     = WL.text "true"
wlJSON (Bool False)    = WL.text "false"
wlJSON (Object o)      = WL.encloseSep (WL.text "{") (WL.text "}") (WL.text ",") (map prettyKV $ toAscList o)
  where prettyKV (k,v) = WL.text (show k) WL.<> WL.text ":" WL.<+> wlJSON v
wlJSON (String s)      = WL.string (show s)
wlJSON (Array a)       = WL.encloseSep (WL.text "[") (WL.text "]") (WL.text ",") (map wlJSON $ toList a)
wlJSON Null            = WL.empty
wlJSON (Number n)      = WL.text (show n)

readJSONValue fname = do
  inptxt <- BS.readFile fname
  let Right inpJson = parseOnly json' inptxt
  return inpJson

bench :: Value -> TestingProc
bench inpJson conf = do
  let s | target conf == bernardyLibTarget = PC.render $ prettiestJSON inpJson
        | target conf == bernardyPatchedTarget = PCP.render $ prettiestJSONP inpJson
        | target conf == wadlerTarget = wlRender $ wlJSON inpJson
  return s

core :: TestingFun
core conf = do
  inpJson <- readJSONValue $
    if size conf == 1 then "benchdata/1k.json"
    else "benchdata/10k.json"
  return $ C.nfAppIO (instrument (bench inpJson)) conf

main = do
  runIt
    "TestJSON"
    (defaultConfig { size = 2 })
    (validateTargets
      [ bernardyLibTarget
      , bernardyPatchedTarget
      , wadlerTarget]
      (\conf ->
         if not (size conf == 1 || size conf == 2) then
           Just "size must be either 1 or 2"
         else
           Nothing))
    core
