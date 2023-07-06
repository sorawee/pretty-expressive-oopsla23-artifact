module Main where

import Prelude hiding ((<>))
import qualified Criterion.Main as C

import BernardyPaper
import BernardyCustomizableWidth
import qualified Text.PrettyPrint.Compact  as PC
import qualified TextPatched.PrettyPrint.Compact  as PCP
import qualified Text.PrettyPrint.Leijen   as WL

import LibTest

fillSep :: Doc d => [String] -> d
fillSep [] = text ""
fillSep (x:xs) = go xs (text x)
  where go [] acc = acc
        go (x':xs') acc = go xs' ((acc <+> text x') <|> (acc $$ text x'))

fillSepPC :: [String] -> PC.Doc ()
fillSepPC [] = PC.text ""
fillSepPC (x:xs) = go xs (PC.text x)
  where go [] acc = acc
        go (x':xs') acc = go xs' ((acc PC.<+> PC.text x') PC.<|> (acc PC.$$ PC.text x'))

fillSepPCP :: [String] -> PCP.Doc ()
fillSepPCP [] = PCP.text ""
fillSepPCP (x:xs) = go xs (PCP.text x)
  where go [] acc = acc
        go (x':xs') acc = go xs' ((acc PCP.<+> PCP.text x') PCP.<|> (acc PCP.$$ PCP.text x'))

benchmark :: [String] -> TestingProc
benchmark linesFromFile conf = do
  let s | target conf == bernardyMeasureTarget = render (fillSep linesFromFile :: DM)
        | target conf == bernardyPaperTarget = render (fillSep linesFromFile :: CDoc)
        | target conf == bernardyLibTarget = PC.render $ fillSepPC linesFromFile
        | target conf == bernardyPatchedTarget = PCP.render $ fillSepPCP linesFromFile
        | target conf == wadlerTarget = wlRender $ WL.fillSep $ map WL.text linesFromFile
        -- NOTE: this fillSep from Bernardy's library doesn't
        -- implement fillSep correctly. Use --view-layout to see what it prints
        | target conf == extraTarget = PCP.render
            (PCP.fillSep (map PCP.text linesFromFile) :: PCP.Doc ())
        | target conf == extra2Target =
            render_with_limit (width conf) (fillSep linesFromFile :: ODoc)
        | otherwise = error "impossible"
  return s

core :: TestingFun
core conf = do
  file <- readFile "/usr/share/dict/words"
  let linesFromFile = take (size conf) $ lines file
  return $ C.nfAppIO (instrument (benchmark linesFromFile)) conf

main :: IO ()
main =
  runIt
    "TestFillSep"
    (defaultConfig { size = 5000 })
    (validateTargets
      [ bernardyMeasureTarget
      , bernardyPaperTarget
      , bernardyLibTarget
      , bernardyPatchedTarget
      , extraTarget
      , extra2Target
      , wadlerTarget]
      (\_ -> Nothing))
    core
