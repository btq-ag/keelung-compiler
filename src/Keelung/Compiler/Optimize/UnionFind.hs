module Keelung.Compiler.Optimize.UnionFind
  ( UnionFind (..),
    new,
    find,
    union,
    lookupVar,
    bindVar,
  )
where

import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Keelung.Field (N (..))
import Keelung.Types (Var)

data UnionFind n = UnionFind
  { links :: IntMap Var,
    sizes :: IntMap Int,
    values :: IntMap n -- values in associate with some Var
  }

instance (GaloisField n, Integral n) => Show (UnionFind n) where
  show xs =
    "UnionFind {\n"
      ++ "  links = "
      ++ showList' (map (\(x, y) -> "$" <> show x <> " -> $" <> show y) (IntMap.toList $ links xs))
      ++ "\n"
      ++ "  sizes = "
      ++ showList' (map (\(x, y) -> "$" <> show x <> ": " <> show y) (IntMap.toList $ sizes xs))
      ++ "\n"
      ++ "  values = "
      ++ showList' (map (\(x, y) -> "$" <> show x <> " = " <> show (N y)) (IntMap.toList $ values xs))
      ++ "\n"
      ++ "}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

new :: IntMap n -> UnionFind n
new = UnionFind mempty mempty

-- | Bind variable 'x' to 'c'
bindVar :: UnionFind n -> Var -> n -> UnionFind n
bindVar xs var x = xs {values = IntMap.insert var x (values xs)}

-- | Lookup variable 'x'
lookupVar :: UnionFind n -> Var -> Maybe n
lookupVar xs x = IntMap.lookup x (values xs)

-- | Find the root of a variable
find :: GaloisField n => UnionFind n -> Var -> (Var, UnionFind n)
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

-- If a variable has no parent, it is its own parent.
parentOf :: UnionFind n -> Var -> Var
parentOf xs var = fromMaybe var $ IntMap.lookup var (links xs)

-- Merge 2 mappings of values
mergeValues :: GaloisField n => IntMap n -> Var -> Var -> IntMap n
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
union :: GaloisField n => UnionFind n -> Var -> Var -> UnionFind n
union xs x y
  | x < y =
    union' xs x y
  | x > y =
    union' xs y x
  | otherwise =
    xs

-- | Choose the first argument as root on ties.
-- Left-biased: if size x == size y, prefer x as root.
union' :: GaloisField n => UnionFind n -> Var -> Var -> UnionFind n
union' xs x y =
  let (rootOfX, xs2) = find xs x
      (rootOfY, xs3) = find xs2 y
      sizeOfRootX = size xs3 rootOfX
      sizeOfRootY = size xs3 rootOfY
   in if sizeOfRootX >= sizeOfRootY
        then
          xs3
            { links = IntMap.insert y rootOfX (links xs3),
              sizes = IntMap.insert x (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }
        else
          xs3
            { links = IntMap.insert x rootOfY (links xs3),
              sizes = IntMap.insert y (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }

size :: UnionFind n -> Var -> Int
size xs x = fromMaybe 1 $ IntMap.lookup x (sizes xs)
