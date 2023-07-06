module Main where

import qualified Criterion.Main as C

import Data.List (intersperse)
import Data.Aeson.Types
import Data.Aeson.KeyMap (toAscList)
import Data.Foldable (toList)

import qualified Text.PrettyPrint.Leijen   as WL
import qualified Text.PrettyPrint.Compact  as PC
import qualified TextPatched.PrettyPrint.Compact  as PCP

import LibTest
import LibJSON

-- PC.encloseSep adds an extra space, so we reimplement it to be faithful with
-- Wadler/Leijen's encloseSep

encloseSepPC :: Monoid a => PC.Doc a -> PC.Doc a -> PC.Doc a -> [PC.Doc a] -> PC.Doc a
encloseSepPC left right sep ds
    = (\mid -> mid <> right) $ case ds of
        []  -> left <> mempty
        [d] -> left <> d
        (d:ds') ->
            PC.hcat (left:intersperse sep ds) PC.<|> PC.vcat (left PC.<> d:map (sep PC.<>) ds')

encloseSepPCP :: Monoid a => PCP.Doc a -> PCP.Doc a -> PCP.Doc a -> [PCP.Doc a] -> PCP.Doc a
encloseSepPCP left right sep ds
    = (\mid -> mid <> right) $ case ds of
        []  -> left <> mempty
        [d] -> left <> d
        (d:ds') ->
            PCP.hcat (left:intersperse sep ds) PCP.<|> PCP.vcat (left PCP.<> d:map (sep PCP.<>) ds')

prettiestJSON :: Value -> PC.Doc ()
prettiestJSON (Bool True)  = PC.text "true"
prettiestJSON (Bool False) = PC.text "false"
prettiestJSON (Object o)   = encloseSepPC (PC.text "{") (PC.text "}") (PC.text ",") (map prettyKV $ toAscList o)
  where prettyKV (k,v)     = PC.text (show k) PC.<> PC.text ":" PC.<+> prettiestJSON v
prettiestJSON (String s)   = PC.string (show s)
prettiestJSON (Array a)    = encloseSepPC (PC.text "[") (PC.text "]") (PC.text ",") (map prettiestJSON $ toList a)
prettiestJSON Null         = PC.mempty
prettiestJSON (Number n)   = PC.text (show n)

prettiestJSONP :: Value -> PCP.Doc ()
prettiestJSONP (Bool True)  = PCP.text "true"
prettiestJSONP (Bool False) = PCP.text "false"
prettiestJSONP (Object o)   = encloseSepPCP (PCP.text "{") (PCP.text "}") (PCP.text ",") (map prettyKV $ toAscList o)
  where prettyKV (k,v)     = PCP.text (show k) PCP.<> PCP.text ":" PCP.<+> prettiestJSONP v
prettiestJSONP (String s)   = PCP.string (show s)
prettiestJSONP (Array a)    = encloseSepPCP (PCP.text "[") (PCP.text "]") (PCP.text ",") (map prettiestJSONP $ toList a)
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

bench :: Value -> TestingProc
bench inpJson conf = do
  let s | target conf == bernardyLibTarget = PC.render $ prettiestJSON inpJson
        | target conf == bernardyPatchedTarget = PCP.render $ prettiestJSONP inpJson
        | target conf == wadlerTarget = wlRender $ wlJSON inpJson
        | otherwise = error "impossible"
  return s

core :: TestingFun
core conf = do
  inpJson <- readJSONValue $
    if size conf == 1 then "../benchdata/1k.json"
    else "../benchdata/10k.json"
  return $ C.nfAppIO (instrument (bench inpJson)) conf

main :: IO ()
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
