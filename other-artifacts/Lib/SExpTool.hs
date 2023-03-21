module Lib.SExpTool where

import qualified Text.PrettyPrint.Compact as PC
import qualified TextPatched.PrettyPrint.Compact as PCP

data SExpr = SExpr [SExpr] | Atom String
  deriving Show

foldD :: Monoid a => (a -> a -> a) -> [a] -> a
foldD _ []       = mempty
foldD f ds       = foldr1 f ds

hsepPC :: [PC.Doc ()] -> PC.Doc ()
hsepPC = foldD (PC.<+>)

hsepPCP :: [PCP.Doc ()] -> PCP.Doc ()
hsepPCP = foldD (PCP.<+>)

sepPC :: [PC.Doc ()] -> PC.Doc ()
sepPC xs = hsepPC xs PC.<|> PC.vcat xs

sepPCP :: [PCP.Doc ()] -> PCP.Doc ()
sepPCP xs = hsepPCP xs PCP.<|> PCP.vcat xs
