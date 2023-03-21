{-# LANGUAGE BangPatterns #-}

module Lib.BenchTool where

import Options.Applicative
import Constants.Values
import Data.IORef
import System.Environment
import Text.Printf
import qualified Text.PrettyPrint.Leijen   as WL
import Data.Time
import Crypto.Hash
import qualified Data.Text.Lazy             as TL
import qualified Data.Text.Lazy.Encoding    as TL

wlRender :: WL.Doc -> String
wlRender d = WL.displayS (WL.renderPretty 1 widthlimit d) ""

leijenTarget, bernardyPaperTarget,
  bernardyPatchedTarget, bernardyLibTarget, extraTarget, extra2Target :: String
leijenTarget = "leijen"
bernardyPaperTarget = "bernardy-paper"
bernardyPatchedTarget = "bernardy-patched"
bernardyLibTarget = "bernardy-lib"
extraTarget = "extra"
extra2Target = "extra-2"

data Config = Config
  { width :: Int
  , size  :: Int
  , target :: String
  , outputPath :: Maybe String
  } deriving Show

defaultConfig :: Config
defaultConfig = Config { width = 80
                       , size = 0
                       , target = bernardyPatchedTarget
                       , outputPath = Nothing
                       }

validateConfig :: (Config -> Maybe String) ->
                  Int -> Int -> String -> Maybe String ->
                  Config
validateConfig validate w s t out =
  let conf = Config w s t out in
  case validate conf of
    Nothing -> conf
    Just x -> error $ "error: " <> x

validateTargets :: [String] -> (Config -> Maybe String) -> Config -> Maybe String
validateTargets allowedTargets validate conf =
  if not $ target conf `elem` allowedTargets then
    Just $ "target not allowed: available options are " <> show allowedTargets
  else
    validate conf

type TestingProc = Config -> IO String

run :: String -> (Config -> Maybe String) -> TestingProc -> Config -> IO ()
run prog validate f conf = do
  case validate conf of
    Nothing -> do
      writeIORef pageWidthIO (width conf)
      startTime <- getCurrentTime
      -- We use ! here to make the evaluation strict
      !out <- f conf
      let !len = show $ length $ lines out
      endTime <- getCurrentTime
      let diff = nominalDiffTimeToSeconds $ diffUTCTime endTime startTime
      case outputPath conf of
        Nothing -> return ()
        Just path | path == "-" -> putStrLn out
                  | otherwise -> writeFile path out
      putStr $
        unlines [ printf "([target %s]" (target conf)
                , printf " [program %s]" prog
                , printf " [duration %s]" (show diff)
                , printf " [lines %s]" len
                , printf " [size %s]" (show (size conf))
                , printf " [md5 %s]" (show (hashlazy $ TL.encodeUtf8 $ TL.pack out :: Digest MD5))
                , printf " [page-width %s])" (show (width conf))
                ]
    Just x -> error x

getConfig :: Config -> Parser Config
getConfig def = Config
        <$> option auto
        ( long "page-width"
        <> help "page width limit"
        <> showDefault
        <> value (width def))
        <*> option auto
        ( long "size"
        <> help "document size"
        <> showDefault
        <> value (size def))
        <*> strOption
        ( long "target"
        <> help "target printer"
        <> showDefault
        <> value (target def))
        <*> (optional $ strOption
        ( long "out"
        <> help "Output the actual layout to a specified path; - means stdout"))

runIt :: String -> Config -> (Config -> Maybe String) -> TestingProc -> IO ()
runIt prog def validate f = do
  let conf = getConfig def
  let opts = info (conf <**> helper) ( progDesc prog <> fullDesc )
  run prog validate f =<< execParser opts
