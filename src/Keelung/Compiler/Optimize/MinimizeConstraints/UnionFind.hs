{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with fromMaybe" #-}

module Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind, new, lookup, relate, union, findMaybe, find, toMap, size) where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import GHC.Generics (Generic)
import Prelude hiding (lookup)

data UnionFind ref n = UnionFind
  { links :: Map ref (n, ref, n),
    sizes :: Map ref Int
  }
  deriving (Eq, Generic, NFData)

instance (Show ref, Show n, Eq n, Num n) => Show (UnionFind ref n) where
  show xs =
    "UnionFind {\n"
      ++ "  links = "
      ++ showList' (map (\(var, (slope, root, intercept)) -> show var <> " = " <> (if slope == 1 then "" else show slope) <> show root <> (if intercept == 0 then "" else " + " <> show intercept)) (Map.toList $ links xs))
      ++ "\n"
      ++ "  sizes = "
      ++ showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ sizes xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

new :: Ord ref => UnionFind ref n
new = UnionFind mempty mempty

-- | Find the root of a variable
findMaybe :: (Ord ref, Num n) => ref -> UnionFind ref n -> Maybe ((n, ref, n), UnionFind ref n)
findMaybe var xs = case parentOf xs var of
  Nothing -> Just ((1, var, 0), xs) -- returns self as root
  Just (slope, parent, intercept) -> case parentOf xs parent of
    Nothing -> Just ((slope, parent, intercept), xs) -- returns parent as root
    Just (slope', grandparent, intercept') ->
      -- var = slope * parent + intercept
      -- parent = slope' * grandparent + intercept'
      --  =>
      -- var = slope * (slope' * grandparent + intercept') + intercept
      --  =>
      -- var = slope * slope' * grandparent + slope * intercept' + intercept
      findMaybe grandparent (xs {links = Map.insert var (slope * slope', grandparent, slope * intercept' + intercept) (links xs)})

-- | Find the root of a variable, returns:
--      1. if the variable is already a root
--      2. the slope
--      3. the root
--      4. the intercept
lookup :: (Ord ref, Num n) => ref -> UnionFind ref n -> (Bool, n, ref, n)
lookup var xs = case parentOf xs var of
  Nothing -> (True, 1, var, 0) -- returns self as root
  Just (slope, parent, intercept) -> (False, slope, parent, intercept)

-- | Find the root of a variable. Returns Nothing if the variable is a root.
find :: (Ord ref, Num n) => ref -> UnionFind ref n -> ((n, ref, n), UnionFind ref n)
find var xs = case findMaybe var xs of
  Nothing -> ((1, var, 0), xs) -- returns self as root
  Just result -> result

-- If a variable has no parent, it is its own parent.
parentOf :: (Ord ref, Num n) => UnionFind ref n -> ref -> Maybe (n, ref, n)
parentOf xs var = Map.lookup var (links xs)

-- | Unify x with y.  On ties, prefer smaller variables. This is just
-- a heuristic that biases toward pinned variables, many of which are
-- low-numbered input vars. This way, we avoid introducing pinned
-- eqns. in some cases.
union :: (Ord ref, GaloisField n) => ref -> (n, ref, n) -> UnionFind ref n -> UnionFind ref n
union x (slope, y, intercept) xs
  | x < y = union' x (slope, y, intercept) xs -- x = slope * y + intercept
  | x > y = union' y (recip slope, x, intercept / slope) xs -- y = x / slope - intercept / slope
  | otherwise =
      xs

relate :: (Ord ref, GaloisField n) => ref -> (n, ref, n) -> UnionFind ref n -> Maybe (UnionFind ref n)
relate x (slope, y, intercept) xs
  | x > y = relate' x (slope, y, intercept) xs -- x = slope * y + intercept
  | x < y = relate' y (recip slope, x, - intercept / slope) xs -- y = x / slope - intercept / slope
  | otherwise = Nothing


-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relate' :: (Ord ref, GaloisField n) => ref -> (n, ref, n) -> UnionFind ref n -> Maybe (UnionFind ref n)
relate' x (slope, y, intercept) xs =
  let (_, slopeX, rootOfX, interceptX) = lookup x xs -- x = slopeX * rootOfX + interceptX
      (_, slopeY, rootOfY, interceptY) = lookup y xs -- y = slopeY * rootOfY + interceptY
      sizeOfRootX = sizeOf xs rootOfX
      sizeOfRootY = sizeOf xs rootOfY
   in if slope == slopeX && y == rootOfX && intercept == interceptX
        then Nothing
        else
          if sizeOfRootX > sizeOfRootY
            then --  x = slope * y + intercept
            --    =>
            --  y = (x - intercept) / slope
            --    =>
            --  y = (slopeX * rootOfX + interceptX - intercept) / slope
            --    =>
            --  y = slopeX * rootOfX / slope + (interceptX - intercept) / slope

              Just $
                xs
                  { links = Map.insert y (slopeX / slope, rootOfX, (interceptX - intercept) / slope) (links xs),
                    sizes = Map.insert x (sizeOfRootX + sizeOfRootY) (sizes xs)
                  }
            else --  x = slope * y + intercept
            --    =>
            --  x = slope * (slopeY * rootOfY + interceptY) + intercept
            --    =>
            --  x = slope * slopeY * rootOfY + slope * interceptY + intercept

              Just $
                xs
                  { links = Map.insert x (slope * slopeY, rootOfY, slope * interceptY + intercept) (links xs),
                    sizes = Map.insert y (sizeOfRootX + sizeOfRootY) (sizes xs)
                  }

-- | Choose the first argument as root on ties.
-- Left-biased: if size x == size y, prefer x as root.
union' :: (Ord ref, GaloisField n) => ref -> (n, ref, n) -> UnionFind ref n -> UnionFind ref n
union' x (slope, y, intercept) xs =
  let ((slopeX, rootOfX, interceptX), xs2) = find x xs -- x = slopeX * rootOfX + interceptX
      ((slopeY, rootOfY, interceptY), xs3) = find y xs2 -- y = slopeY * rootOfY + interceptY
      sizeOfRootX = sizeOf xs3 rootOfX
      sizeOfRootY = sizeOf xs3 rootOfY
   in if sizeOfRootX >= sizeOfRootY
        then --  x = slope * y + intercept
        --    =>
        --  y = (x - intercept) / slope
        --    =>
        --  y = slopeX * rootOfX / slope + (interceptX - intercept) / slope

          xs3
            { links = Map.insert y (slopeX / slope, rootOfX, (interceptX - intercept) / slope) (links xs3),
              sizes = Map.insert x (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }
        else --  x = slope * y + intercept
        --    =>
        --  x = slope * (slopeY * rootOfY + interceptY) + intercept
        --    =>
        --  x = slope * slopeY * rootOfY + slope * interceptY + intercept

          xs3
            { links = Map.insert x (slope * slopeY, rootOfY, slope * interceptY + intercept) (links xs3),
              sizes = Map.insert y (sizeOfRootX + sizeOfRootY) (sizes xs3)
            }

sizeOf :: Ord ref => UnionFind ref n -> ref -> Int
sizeOf xs x = fromMaybe 1 $ Map.lookup x (sizes xs)

toMap :: UnionFind ref n -> Map ref (n, ref, n)
toMap = links

size :: UnionFind ref n -> Int
size = Map.size . links