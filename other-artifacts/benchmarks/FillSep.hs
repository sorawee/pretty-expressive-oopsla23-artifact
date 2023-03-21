module Main where

import Prelude hiding ((<>))

import PrinterPaper.BernardyPaper
import PrinterPaper.BernardyCustomizableWidth
import qualified Text.PrettyPrint.Compact  as PC
import qualified TextPatched.PrettyPrint.Compact  as PCP
import qualified Text.PrettyPrint.Leijen   as WL

import Lib.BenchTool

import System.Environment

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
  let s | target conf == bernardyPaperTarget = render (fillSep linesFromFile :: CDoc)
        | target conf == bernardyLibTarget = PC.render $ fillSepPC linesFromFile
        | target conf == bernardyPatchedTarget = PCP.render $ fillSepPCP linesFromFile
        | target conf == leijenTarget = wlRender $ WL.fillSep $ map WL.text linesFromFile

        -- NOTE: `--target extra` uses fillSep from Bernardy's actual library,
        -- which is not implemented correctly
         -- (and thus the reason why we reimplement it from scratch.)
        | target conf == extraTarget = PCP.render
            (PCP.fillSep (map PCP.text linesFromFile) :: PCP.Doc ())

        -- NOTE: `--target extra-2` is an experiment to show that
        -- customizable width limit is what causes combinatorial explosion.
        | target conf == extra2Target =
            render_with_limit (width conf) (fillSep linesFromFile :: ODoc)
        | otherwise = error "impossible"
  return s

core :: TestingProc
core conf = do
  benchData <- getEnv "BENCHDATA"
  file <- readFile (benchData ++ "/words")
  let linesFromFile = take (size conf) $ lines file
  ret <- (benchmark linesFromFile) conf
  return ret

main :: IO ()
main =
  runIt
    "fill-sep"
    (defaultConfig { size = 5000 })
    (validateTargets
      [ bernardyPaperTarget
      , bernardyLibTarget
      , bernardyPatchedTarget
      , extraTarget
      , extra2Target
      , leijenTarget]
      (\_ -> Nothing))
    core
