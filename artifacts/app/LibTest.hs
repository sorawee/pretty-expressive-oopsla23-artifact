module LibTest where

import Options.Applicative
import Data.Semigroup ((<>))
import Data.List (intercalate)

import Constants.Values
import Data.IORef

import qualified Criterion.Main as C
import qualified Criterion.Measurement as M
import System.Environment
import Constants.Values (widthlimit)

import Text.Printf

import qualified Text.PrettyPrint.Leijen   as WL

wlRender :: WL.Doc -> String
wlRender d = WL.displayS (WL.renderPretty 1 widthlimit d) ""

wadlerTarget = "wadler"
bernardyMeasureTarget = "bernardy-measure"
bernardyPaperTarget = "bernardy-paper"
bernardyPatchedTarget = "bernardy-patched"
bernardyLibTarget = "bernardy-lib"
extraTarget = "extra"

data Config = Config
  { width :: Int,
    size  :: Int,
    iter  :: Int,
    target :: String,
    viewLayout :: Bool,
    viewLines :: Bool
  } deriving Show

defaultConfig = Config { width = 80
                       , size = 0
                       , iter = 0
                       , target = bernardyPatchedTarget
                       , viewLayout = False
                       , viewLines = False
                       }

validateConfig :: (Config -> Maybe String) ->
                  Int -> Int -> Int -> String -> Bool -> Bool ->
                  Config
validateConfig validate w s i t vlay vli =
  let conf = Config w s i t vlay vli in
  case validate conf of
    Nothing -> conf
    Just x -> error $ "error: " <> x

validateTargets allowedTargets validate conf =
  if not $ target conf `elem` allowedTargets then
    Just $ "target not allowed: available options are " <> show allowedTargets
  else
    validate conf

type TestingProc = Config -> IO String
type TestingFun = Config -> IO C.Benchmarkable

instrument :: TestingProc -> TestingProc
instrument f conf = do
  s <- f conf
  if viewLayout conf then
    putStrLn s
  else
    return ()
  if viewLines conf then
    printf "(lines %d)\n" $ length $ lines s
  else
    return ()
  return s

run :: (Config -> Maybe String) -> TestingFun -> Config -> IO ()
run validate f conf = do
  case validate conf of
    Nothing -> do
      writeIORef pageWidthIO (width conf)
      case (iter conf) of
        0 -> do
          b <- f conf
          withArgs [] $ C.defaultMain [C.bench ("Benchmark with conf " <> (show conf)) b]
        iterv -> do
          b <- f conf
          (m, _) <- M.measure b $ fromIntegral $ iterv
          putStrLn $ show m
    Just x ->
      putStrLn ("error: " <> x)

getConfig :: Config -> Parser Config
getConfig def = Config
        <$> option auto
        ( long "width"
        <> help "page width limit"
        <> showDefault
        <> value (width def))
        <*> option auto
        ( long "size"
        <> help "document size"
        <> showDefault
        <> value (size def))
        <*> option auto
        ( long "iter"
        <> help "number of iterations; 0 means as long as Criterion likes"
        <> showDefault
        <> value (iter def))
        <*> strOption
        ( long "target"
        <> help "target printer"
        <> showDefault
        <> value (target def))
        <*> switch
        ( long "view-layout"
        <> help "view layout")
        <*> switch
        ( long "view-lines"
        <> help "view number of lines")

runIt :: String -> Config -> (Config -> Maybe String) -> TestingFun -> IO ()
runIt theDesc def validate f = do
  let conf = getConfig def
  let opts = info (conf <**> helper) ( progDesc theDesc <> fullDesc )
  run validate f =<< execParser opts
