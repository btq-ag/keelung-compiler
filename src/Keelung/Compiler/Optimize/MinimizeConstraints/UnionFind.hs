{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
module Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind, new, union, find, find', toMap, size) where

import Data.Field.Galois (GaloisField)
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)

data UnionFind ref n = UnionFind
  { links :: Map ref (n, ref),
    sizes :: Map ref Int
  }
  deriving (Eq, Generic, NFData)

instance (Show ref, Show n, Eq n, Num n) => Show (UnionFind ref n) where
  show xs =
    "UnionFind {\n"
      ++ "  links = "
      ++ showList' (map (\(x, (coeff, y)) -> show x <> " = " <> (if coeff == 1 then "" else show coeff) <> show y) (Map.toList $ links xs))
      ++ "\n"
      ++ "  sizes = "
      ++ showList' (map (\(x, y) -> show x <> ": " <> show y) (Map.toList $ sizes xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

new :: Ord ref => UnionFind ref n
new = UnionFind mempty mempty

-- | Find the root of a variable
find :: (Ord ref, Num n) => ref -> UnionFind ref n -> Maybe ((n, ref), UnionFind ref n)
find var xs = case parentOf xs var of
  Nothing -> Just ((1, var), xs) -- returns self as root
  Just (coeff, parent) -> case parentOf xs parent of
    Nothing -> Just ((coeff, parent), xs) -- returns parent as root
    Just (coeff', grandparent) ->
      let coeff'' = coeff * coeff'
       in find grandparent (xs {links = Map.insert var (coeff'', grandparent) (links xs)})

-- | Find the root of a variable. Returns Nothing if the variable is a root.
find' :: (Ord ref, Num n) => ref -> UnionFind ref n -> ((n, ref), UnionFind ref n)
find' var xs = case find var xs of
  Nothing -> ((1, var), xs) -- returns self as root
  Just ((coeff, parent), xs') -> ((coeff, parent), xs')

-- If a variable has no parent, it is its own parent.
parentOf :: (Ord ref, Num n) => UnionFind ref n -> ref -> Maybe (n, ref)
parentOf xs var = Map.lookup var (links xs)

-- | Unify x with y.  On ties, prefer smaller variables. This is just
-- a heuristic that biases toward pinned variables, many of which are
-- low-numbered input vars. This way, we avoid introducing pinned
-- eqns. in some cases.
union :: (Ord ref, GaloisField n) => ref -> (n, ref) -> UnionFind ref n -> UnionFind ref n
union x (coeff, y) xs
  | x < y = union' x (coeff, y) xs
  | x > y = union' y (recip coeff, x) xs
  | otherwise =
    xs

-- | Choose the first argument as root on ties.
-- Left-biased: if size x == size y, prefer x as root.
union' :: (Ord ref, GaloisField n) => ref -> (n, ref) -> UnionFind ref n -> UnionFind ref n
union' x (coeff, y) xs =
  let ((coeff2, rootOfX), xs2) = find' x xs -- x = coeff2 * rootOfX
      ((coeff3, rootOfY), xs3) = find' y xs2 -- y = coeff3 * rootOfY
      sizeOfRootX = sizeOf xs3 rootOfX
      sizeOfRootY = sizeOf xs3 rootOfY
   in if sizeOfRootX >= sizeOfRootY
        then
          xs3 -- x = coeff y => y = x / coeff => y = coeff2 * rootOfX / coeff
            { links = Map.insert y (coeff2 / coeff, rootOfX) (links xs3),
              sizes = Map.insert x (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }
        else
          xs3 -- x = coeff y => x = coeff * coeff3 * rootOfY
            { links = Map.insert x (coeff * coeff3, rootOfY) (links xs3),
              sizes = Map.insert y (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }

sizeOf :: Ord ref => UnionFind ref n -> ref -> Int
sizeOf xs x = fromMaybe 1 $ Map.lookup x (sizes xs)

toMap :: UnionFind ref n -> Map ref (n, ref)
toMap = links

size :: UnionFind ref n -> Int
size = Map.size . links