module PrinterPaper.BernardyCustomizableWidth where

-- This file is an experiment to patch the pretty printer in Bernardy's paper,
-- (BernardyPaper) which does not suffer from combinatorial explosion,
-- to support customizable width limit.
-- Unfortunately, the experiment shows that supporting customizable width limit
-- is precisely what causes the combinatorial explosion,
-- as computations are no longer shared.
-- In our paper, this version is briefly discussed in Section 2,
-- but not included in Section 7.
-- See FillSep.hs for an actual benchmark program that uses
-- BernardyCustomizableWidth and demonstrates the combinatorial explosion.

import Prelude hiding ((<>))
import Data.List (minimumBy)
import Data.Function

import PrinterPaper.BernardyPaper

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
