module LibJSON where

import qualified Data.ByteString as BS
import Data.Aeson.Parser
import Data.Aeson.Types
import Data.Attoparsec.ByteString

readJSONValue :: FilePath -> IO Value
readJSONValue fname = do
  inptxt <- BS.readFile fname
  let inpJson = case parseOnly json' inptxt of
                  Left _ -> error "impossible"
                  Right inpJson' -> inpJson'
  return inpJson
