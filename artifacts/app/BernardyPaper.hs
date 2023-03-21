{-# LANGUAGE FlexibleInstances, InstanceSigs #-}

module BernardyPaper where

import Prelude hiding ((<>))
import Data.List (intercalate, minimumBy, intersperse)
import Data.Function
import Constants.Values

--------------------------------------------------------------------------------

class Layout l where
  (<>)    :: l -> l -> l
  text    :: String -> l
  flush   :: l -> l
  render  :: l -> String

type L = [String] -- non empty.

instance Layout L where
  render :: L -> String
  render = intercalate "\n"

  text :: String -> L
  text s = [s]

  (<>) :: L -> L -> L
  xs <> (y:ys) = xs0 ++ [x ++ y] ++ map (indent ++) ys
     where  xs0 = init xs
            x :: String
            x = last xs
            n = length x
            indent = replicate n ' '

  flush :: L -> L
  flush xs = xs ++ [""]


class Layout d => Doc d where
  (<|>) :: d -> d -> d
  fail :: d

data M = M {  height     :: Int,
              lastWidth  :: Int,
              maxWidth   :: Int}
  deriving (Show,Eq,Ord)

instance Layout M where
  a <> b = result
    where result = M {  maxWidth   =  max (maxWidth a) (lastWidth a + maxWidth b),
                        height     =  height     a + height     b,
                        lastWidth  =  lastWidth  a + lastWidth  b}
  text s   = M {  height     = 0,
                  maxWidth   = length s,
                  lastWidth  = length s}
  flush a  = M {  maxWidth   = maxWidth a,
                  height     = height a + 1,
                  lastWidth  = 0}
  render m = intercalate "\n"
      (replicate (height m) (replicate (maxWidth m) 'x') ++
      [replicate (lastWidth m) 'x'])


class Poset a where
  (≺) :: a -> a -> Bool

instance Poset M where
  m1 ≺ m2 =   height     m1 <= height     m2 &&
              maxWidth   m1 <= maxWidth   m2 &&
              lastWidth  m1 <= lastWidth  m2

pareto :: Poset a => [a]  -> [a]
-- pareto xs = trace (show $ length result) result
pareto xs = result
  where  l = length result
         result = loop [] xs
         loop acc  []      = acc
         loop acc  (x:xs)  = if  any (≺ x) acc
                                 then  loop acc xs
                                 else  loop (x:filter (not . (x ≺)) acc) xs

instance Poset (M,L) where
  (a,_) ≺ (b,_) = a ≺ b

-- This section is for debugging measure computation

type DM = [M]

instance Layout DM where
  xs <> ys =  pareto (concat [ filter valid [x <> y | y <- ys] | x <- xs])
  flush xs = pareto (map flush xs)
  text s = filter valid [text s]
  render = render . minimum

instance Doc DM where
  fail = []
  xs <|> ys = pareto (xs ++ ys)

-- end debugging


instance Layout (M,L) where
  (x,x') <> (y,y') =  (x<>y,x'<>y')
  flush (x,x') = (flush x, flush x')
  text s = (text s, text s)
  render = render . snd

valid :: M -> Bool
valid x = maxWidth x <= widthlimit

type CDoc = [(M, L)]

instance Layout CDoc where
  xs <> ys =  pareto $ concat [ filter (valid . fst) [x <> y | y <- ys] | x <- xs]
  flush xs = pareto $ (map flush xs)
  text s = filter (valid . fst) [text s]
  render = render . minimumBy (compare `on` fst)

instance Doc CDoc where
  fail = []
  xs <|> ys = pareto (xs ++ ys)

--------------------------------------------------------------------------------

($$) :: Layout d => d -> d -> d
a $$ b = flush a <> b

empty :: Layout d => d
empty = text ""

(<+>) :: Layout d => d -> d -> d
x <+> y  = x <> text " " <> y

hsep,vcat :: Doc d => [d] -> d
vcat  = foldDoc ($$)
hsep  = foldDoc (<+>)

foldDoc :: Doc d => (d -> d -> d) -> [d] -> d
foldDoc _ []      = empty
foldDoc _ [x]     = x
foldDoc f (x:xs)  = f x (foldDoc f xs)

sep :: Doc d => [d] -> d
sep []  = empty
sep xs  = hsep xs <|> vcat xs

hcat_with :: Doc d => [d] -> d -> d
hcat_with [] s = empty
hcat_with [x] s = x
hcat_with (x:xs) s = x <> s <> hcat_with xs s

encloseSep :: Doc d => d -> d -> d -> [d] -> d
encloseSep left right sep ds
    = case ds of
        []  -> left <> right
        [d] -> left <> d <> right
        (d:ds) -> (left <> (hcat_with (d : ds) (sep <> text " ")) <> right) <|>
                  ((vcat ((left <> d) : (map (\d -> sep <> d) ds))) <> right)

--------------------------------------------------------------------------------
