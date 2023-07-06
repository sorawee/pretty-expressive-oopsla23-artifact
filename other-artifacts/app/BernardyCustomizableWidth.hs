module BernardyCustomizableWidth where

import Prelude hiding ((<>))
import Data.List (minimumBy)
import Data.Function

import BernardyPaper

newtype ODoc = MkDoc {fromDoc :: Int -> [(M, L)]}

fits :: Int -> M -> Bool
fits w x = maxWidth x <= w

instance Layout ODoc where
  (MkDoc xs) <> (MkDoc ys) = MkDoc $ \w ->
    pareto $ concat [ filter (fits w . fst) [x <> y | y <- ys w] | x <- xs w]
  flush (MkDoc xs) = MkDoc $ \w -> pareto (map flush (xs w))
  text s = MkDoc $ \w -> filter (fits w . fst) [text s]
  render _ = "use render_with_limit"

instance Doc ODoc where
  fail = MkDoc $ \_ -> []
  MkDoc m1 <|> MkDoc m2 = MkDoc $ \w -> pareto ((m1 w) ++ (m2 w))

render_with_limit :: Int -> ODoc -> String
render_with_limit w (MkDoc xs) = (render . minimumBy (compare `on` fst)) (xs w)
