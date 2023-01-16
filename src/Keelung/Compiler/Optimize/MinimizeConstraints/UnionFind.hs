module Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind, new, union, find) where

import Data.Field.Galois (GaloisField)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

data UnionFind ref n = UnionFind
  { links :: Map ref ref,
    sizes :: Map ref Int
  }

instance (GaloisField n, Integral n, Show ref) => Show (UnionFind ref n) where
  show xs =
    "UnionFind {\n"
      ++ "  links = "
      ++ showList' (map (\(x, y) -> show x <> " -> $" <> show y) (Map.toList $ links xs))
      ++ "\n"
      ++ "  sizes = "
      ++ showList' (map (\(x, y) -> show x <> ": " <> show y) (Map.toList $ sizes xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

new :: Ord ref => UnionFind ref n
new = UnionFind mempty mempty

-- | Find the root of a variable
find :: (GaloisField n, Ord ref) => UnionFind ref n -> ref -> (ref, UnionFind ref n)
find xs var =
  let parent = parentOf xs var
   in if parent == var
        then (var, xs) -- root
        else -- not root

          let grandParent = parentOf xs parent
           in find
                ( xs
                    { links = Map.insert var grandParent (links xs)
                    }
                )
                parent

-- If a variable has no parent, it is its own parent.
parentOf :: Ord ref => UnionFind ref n -> ref -> ref
parentOf xs var = fromMaybe var $ Map.lookup var (links xs)

-- | Unify x with y.  On ties, prefer smaller variables. This is just
-- a heuristic that biases toward pinned variables, many of which are
-- low-numbered input vars. This way, we avoid introducing pinned
-- eqns. in some cases.
union :: (GaloisField n, Ord ref) => UnionFind ref n -> ref -> ref -> UnionFind ref n
union xs x y
  | x < y =
    union' xs x y
  | x > y =
    union' xs y x
  | otherwise =
    xs

-- | Choose the first argument as root on ties.
-- Left-biased: if size x == size y, prefer x as root.
union' :: (GaloisField n, Ord ref) => UnionFind ref n -> ref -> ref -> UnionFind ref n
union' xs x y =
  let (rootOfX, xs2) = find xs x
      (rootOfY, xs3) = find xs2 y
      sizeOfRootX = sizeOf xs3 rootOfX
      sizeOfRootY = sizeOf xs3 rootOfY
   in if sizeOfRootX >= sizeOfRootY
        then
          xs3
            { links = Map.insert y rootOfX (links xs3),
              sizes = Map.insert x (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }
        else
          xs3
            { links = Map.insert x rootOfY (links xs3),
              sizes = Map.insert y (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }

sizeOf :: Ord ref => UnionFind ref n -> ref -> Int
sizeOf xs x = fromMaybe 1 $ Map.lookup x (sizes xs)
