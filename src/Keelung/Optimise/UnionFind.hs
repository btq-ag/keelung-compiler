module Keelung.Optimise.UnionFind
  ( UnionFind(..),
    new,
    find,
    union,
    lookupVar,
    bindVar,
  )
where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe (fromMaybe)
import Keelung.Syntax.Common (Var)

data UnionFind f = UnionFind
  { links :: IntMap Var,
    sizes :: IntMap Int,
    values :: IntMap f -- values in associate with some Var
  }
  deriving (Show)

new :: IntMap f -> UnionFind f
new = UnionFind mempty mempty


-- | Bind variable 'x' to 'c'
bindVar :: UnionFind f -> Var -> f -> UnionFind f
bindVar xs var x = xs {values = IntMap.insert var x (values xs)}

-- | Lookup variable 'x'
lookupVar :: UnionFind f -> Var -> Maybe f
lookupVar xs x = IntMap.lookup x (values xs)

find :: (Show f, Eq f) => UnionFind f -> Var -> (Var, UnionFind f)
find xs var =
  let parent = parentOf xs var
   in if parent == var
        then (var, xs) -- root
        else -- not root

          let grandParent = parentOf xs parent
           in find
                ( xs
                    { values = mergeValues (values xs) var grandParent,
                      links = IntMap.insert var grandParent (links xs)
                    }
                )
                parent

-- Root returns itself has its parent
parentOf :: UnionFind f -> Var -> Var
parentOf xs var = fromMaybe var $ IntMap.lookup var (links xs)

-- Merge 2 mappings of values
mergeValues :: (Show f, Eq f) => IntMap f -> Var -> Var -> IntMap f
mergeValues xs x y = case (IntMap.lookup x xs, IntMap.lookup y xs) of
  (Nothing, Nothing) -> xs
  (Nothing, Just d) -> IntMap.insert x d xs
  (Just c, Nothing) -> IntMap.insert y c xs
  (Just c, Just d) ->
    if c == d
      then xs
      else
        error
          ( "in UnionFind, extra data doesn't match:\n  "
              ++ show (x, c)
              ++ " != "
              ++ show (y, d)
          )

-- | Unify x with y.  On ties, prefer smaller variables. This is just
-- a heuristic that biases toward pinned variables, many of which are
-- low-numbered input vars. This way, we avoid introducing pinned
-- eqns. in some cases.
union :: (Show f, Eq f) => UnionFind f -> Var -> Var -> UnionFind f
union xs x y
  | x < y =
    go x y
  | x > y =
    go y x
  | otherwise =
    xs
  where
    -- Left-biased: if size x == size y, prefer x as root.
    go x0 y0 =
      let (rx, xs2) = find xs x0
          (ry, xs3) = find xs2 y0
          sizeOfRootX = size xs3 rx
          sizeOfRootY = size xs3 ry
       in if sizeOfRootX >= sizeOfRootY
            then
              xs3
                { links = IntMap.insert y0 rx (links xs3),
                  sizes = IntMap.insert x0 (sizeOfRootX + sizeOfRootY) (sizes xs3)
                }
            else
              xs3
                { links = IntMap.insert x0 ry (links xs3),
                  sizes = IntMap.insert y0 (sizeOfRootX + sizeOfRootY) (sizes xs3)
                }

size :: UnionFind f -> Var -> Int
size xs x = fromMaybe 1 $ IntMap.lookup x (sizes xs)
