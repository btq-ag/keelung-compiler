{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with fromMaybe" #-}
{-# LANGUAGE FlexibleInstances #-}

module Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind
  ( UnionFind,
    relationBetween,
    new,
    lookup,
    parentOf,
    relate,
    bindToValue,
    toMap,
    size,
    exportFromRefBPairs,
    HasFromRefB(..)
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
-- import Data.Maybe (fromMaybe)

import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint (RefB, RefF (..), RefU (..))
import Prelude hiding (lookup)

data UnionFind ref n = UnionFind
  { links :: Map ref (Maybe (n, ref), n),
    sizes :: Map ref Int,
    fromRefBPairs :: Set (ref, RefB)
  }
  deriving (Eq, Generic, NFData)

instance (Show ref, Show n, Eq n, Num n) => Show (UnionFind ref n) where
  show xs =
    "UnionFind {\n"
      ++ "  links = "
      ++ showList' (map showLink (Map.toList $ links xs))
      ++ "\n"
      ++ "  sizes = "
      ++ showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ sizes xs))
      ++ "\n"
      ++ "  fromRefB = "
      ++ showList' (map (\(var, n) -> show var <> " = " <> show n) (Set.toList $ fromRefBPairs xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

      showLink (var, (Just (slope, root), intercept)) = show var <> " = " <> (if slope == 1 then "" else show slope) <> show root <> (if intercept == 0 then "" else " + " <> show intercept)
      showLink (var, (Nothing, intercept)) = show var <> " = " <> show intercept

new :: Ord ref => UnionFind ref n
new = UnionFind mempty mempty mempty

-- | Find the root of a variable, returns:
--      1. if the variable is already a root
--      2. the slope
--      3. the root
--      4. the intercept
lookup :: (Ord ref, Num n) => ref -> UnionFind ref n -> (Bool, (Maybe (n, ref), n))
lookup var xs = case parentOf xs var of
  Nothing -> (True, (Just (1, var), 0)) -- returns self as root
  Just (parent, intercept) -> (False, (parent, intercept))

-- | Returns 'Nothing' if the variable is already a root.
--   else returns 'Just (slope, root)'  where 'var = slope * root + intercept'
parentOf :: (Ord ref, Num n) => UnionFind ref n -> ref -> Maybe (Maybe (n, ref), n)
parentOf xs var = case Map.lookup var (links xs) of
  Nothing -> Nothing -- var is a root
  Just (Nothing, intercept) -> Just (Nothing, intercept) -- var is a root
  Just (Just (slope, parent), intercept) -> case parentOf xs parent of
    Nothing ->
      -- parent is a root
      Just (Just (slope, parent), intercept)
    Just (Nothing, intercept') ->
      -- parent is a value
      -- var = slope * parent + intercept
      -- parent = intercept'
      --  =>
      -- var = slope * intercept' + intercept
      Just (Nothing, slope * intercept' + intercept)
    Just (Just (slope', grandparent), intercept') ->
      -- var = slope * parent + intercept
      -- parent = slope' * grandparent + intercept'
      --  =>
      -- var = slope * (slope' * grandparent + intercept') + intercept
      --  =>
      -- var = slope * slope' * grandparent + slope * intercept' + intercept
      Just (Just (slope * slope', grandparent), slope * intercept' + intercept)

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Nothing` if the two variables are not related.
--   Returns `Just (slope, intercept)` where `var1 = slope * var2 + intercept` if the two variables are related.
relationBetween :: (Ord ref, GaloisField n) => ref -> ref -> UnionFind ref n -> Maybe (n, n)
relationBetween var1 var2 xs = case (lookup var1 xs, lookup var2 xs) of
  ((True, _), (True, _)) ->
    if var1 == var2
      then Just (1, 0)
      else Nothing -- var1 and var2 are roots, but not the same one
  ((True, _), (False, (Just (slope2, root2), intercept2))) ->
    -- var2 = slope2 * root2 + intercept2
    --  =>
    -- root2 = (var2 - intercept2) / slope2
    if var1 == root2
      then -- var1 = root2
      --  =>
      -- var1 = (var2 - intercept2) / slope2
        Just (recip slope2, -intercept2 / slope2)
      else Nothing
  ((True, _), (False, (Nothing, _))) -> Nothing -- var1 is a root, var2 is a value
  ((False, (Just (slope1, root1), intercept1)), (True, _)) ->
    -- var1 = slope1 * root1 + intercept1
    if var2 == root1
      then -- var2 = root1
      --  =>
      -- var1 = slope1 * var2 + intercept1
        Just (slope1, intercept1)
      else Nothing
  ((False, (Nothing, _)), (True, _)) -> Nothing -- var1 is a value, var2 is a root
  ((False, (Just (slope1, root1), intercept1)), (False, (Just (slope2, root2), intercept2))) ->
    -- var1 = slope1 * root1 + intercept1
    -- var2 = slope2 * root2 + intercept2
    if root1 == root2
      then -- var2 = slope2 * root2 + intercept2
      --  =>
      -- root2 = (var2 - intercept2) / slope2 = root1
      --  =>
      -- var1 = slope1 * root1 + intercept1
      --  =>
      -- var1 = slope1 * ((var2 - intercept2) / slope2) + intercept1
      --  =>
      -- var1 = slope1 * var2 / slope2 - slope1 * intercept2 / slope2 + intercept1
        Just (slope1 / slope2, -slope1 * intercept2 / slope2 + intercept1)
      else Nothing
  ((False, (Just _, _)), (False, (Nothing, _))) -> Nothing -- var2 is a value
  ((False, (Nothing, _)), (False, (Just _, _))) -> Nothing -- var1 is a value
  ((False, (Nothing, _)), (False, (Nothing, _))) -> Nothing -- both are values

-- | Bind a variable to a value
bindToValue :: (Ord ref, GaloisField n) => ref -> n -> UnionFind ref n -> UnionFind ref n
bindToValue x value xs =
  case parentOf xs x of
    Nothing ->
      -- x does not have a parent, so it is its own root
      xs
        { links = Map.insert x (Nothing, value) (links xs),
          sizes = Map.insert x 1 (sizes xs)
        }
    Just (Nothing, _oldValue) ->
      -- x is already a root with `_oldValue` as its value
      -- TODO: handle this kind of conflict in the future
      -- FOR NOW: overwrite the value of x with the new value
      xs
        { links = Map.insert x (Nothing, value) (links xs)
        }
    Just (Just (slopeP, parent), interceptP) ->
      -- x is a child of `parent` with slope `slopeP` and intercept `interceptP`
      --  x = slopeP * parent + interceptP
      -- now since that x = value, we have
      --  value = slopeP * parent + interceptP
      -- =>
      --  value - interceptP = slopeP * parent
      -- =>
      --  parent = (value - interceptP) / slopeP
      xs
        { links =
            Map.insert parent (Nothing, (value - interceptP) / slopeP) $
              Map.insert x (Nothing, value) $
                links xs,
          sizes = Map.insert x 1 (sizes xs)
        }

relate :: (Ord ref, GaloisField n, HasFromRefB ref) => ref -> (n, ref, n) -> UnionFind ref n -> Maybe (UnionFind ref n)
relate x (0, _, intercept) xs = Just $ bindToValue x intercept xs
relate x (slope, y, intercept) xs
  | x > y = relate' x (slope, y, intercept) xs -- x = slope * y + intercept
  | x < y = relate' y (recip slope, x, -intercept / slope) xs -- y = x / slope - intercept / slope
  | otherwise = Nothing

-- | Establish the relation of 'x = slope * y + intercept'
--   Returns Nothing if the relation has already been established
relate' :: (Ord ref, GaloisField n, HasFromRefB ref) => ref -> (n, ref, n) -> UnionFind ref n -> Maybe (UnionFind ref n)
relate' x (slope, y, intercept) xs =
  case parentOf xs x of
    Just (Nothing, interceptX) ->
      -- x is already a root with `interceptX` as its value
      --  x = slope * y + intercept
      --  x = interceptX
      -- =>
      --  slope * y + intercept = interceptX
      -- =>
      --  y = (interceptX - intercept) / slope
      Just $ bindToValue y (interceptX - intercept / slope) xs
    Just (Just (slopeX, rootOfX), interceptX) ->
      -- x is a child of `rootOfX` with slope `slopeX` and intercept `interceptX`
      --  x = slopeX * rootOfX + interceptX
      --  x = slope * y + intercept
      -- =>
      --  slopeX * rootOfX + interceptX = slope * y + intercept
      -- =>
      --  slopeX * rootOfX = slope * y + intercept - interceptX
      -- =>
      --  rootOfX = (slope * y + intercept - interceptX) / slopeX
      relate rootOfX (slope / slopeX, y, intercept - interceptX / slopeX) xs
    Nothing ->
      -- x does not have a parent, so it is its own root
      case parentOf xs y of
        Just (Nothing, interceptY) ->
          -- y is already a root with `interceptY` as its value
          --  x = slope * y + intercept
          --  y = interceptY
          -- =>
          --  x = slope * interceptY + intercept
          Just $ bindToValue x (slope * interceptY + intercept) xs
        Just (Just (slopeY, rootOfY), interceptY) ->
          -- y is a child of `rootOfY` with slope `slopeY` and intercept `interceptY`
          --  y = slopeY * rootOfY + interceptY
          --  x = slope * y + intercept
          -- =>
          --  x = slope * (slopeY * rootOfY + interceptY) + intercept
          -- =>
          --  x = slope * slopeY * rootOfY + slope * interceptY + intercept
          Just $
            rememberFromRefBPairs x y $
              xs
                { links = Map.insert x (Just (slope * slopeY, rootOfY), slope * interceptY + intercept) (links xs),
                  sizes = Map.insertWith (+) y 1 (sizes xs)
                }
        Nothing ->
          -- y does not have a parent, so it is its own root
          Just $
            rememberFromRefBPairs x y $
              xs
                { links = Map.insert x (Just (slope, y), intercept) (links xs),
                  sizes = Map.insertWith (+) y 1 (sizes xs)
                }

-- let (_, slopeX, rootOfX, interceptX) = lookup x xs -- x = slopeX * rootOfX + interceptX
--     (_, slopeY, rootOfY, interceptY) = lookup y xs -- y = slopeY * rootOfY + interceptY
--     sizeOfRootX = sizeOf xs rootOfX
--     sizeOfRootY = sizeOf xs rootOfY
--  in if slope == slopeX && y == rootOfX && intercept == interceptX
--       then Nothing
--       else
--         if sizeOfRootX > sizeOfRootY
--           then --  x = slope * y + intercept
--           --    =>
--           --  y = (x - intercept) / slope
--           --    =>
--           --  y = (slopeX * rootOfX + interceptX - intercept) / slope
--           --    =>
--           --  y = slopeX * rootOfX / slope + (interceptX - intercept) / slope

--             Just $
--               xs
--                 { links = Map.insert y (slopeX / slope, rootOfX, (interceptX - intercept) / slope) (links xs),
--                   sizes = Map.insert x (sizeOfRootX + sizeOfRootY) (sizes xs)
--                 }
--           else --  x = slope * y + intercept
--           --    =>
--           --  x = slope * (slopeY * rootOfY + interceptY) + intercept
--           --    =>
--           --  x = slope * slopeY * rootOfY + slope * interceptY + intercept

--             Just $
--               xs
--                 { links = Map.insert x (slope * slopeY, rootOfY, slope * interceptY + intercept) (links xs),
--                   sizes = Map.insert y (sizeOfRootX + sizeOfRootY) (sizes xs)
--                 }

-- sizeOf :: Ord ref => UnionFind ref n -> ref -> Int
-- sizeOf xs x = fromMaybe 1 $ Map.lookup x (sizes xs)

toMap :: UnionFind ref n -> Map ref (Maybe (n, ref), n)
toMap = links

size :: UnionFind ref n -> Int
size = Map.size . links

--------

-- | HACK
class HasFromRefB ref where
  extractRefB :: ref -> Maybe RefB

instance HasFromRefB RefF where
  extractRefB (RefBtoRefF refB) = Just refB
  extractRefB _ = Nothing

instance HasFromRefB RefU where
  extractRefB (RefBtoRefU refB) = Just refB
  extractRefB _ = Nothing

instance HasFromRefB String where 
  extractRefB _ = Nothing

-- | If the RefB is of RefUBit, remember it
rememberFromRefBPairs :: (HasFromRefB ref, Ord ref) => ref -> ref -> UnionFind ref n -> UnionFind ref n
rememberFromRefBPairs ref1 ref2 xs = case (extractRefB ref1, extractRefB ref2) of
  (Nothing, Nothing) -> xs
  (Just refB, _) -> xs {fromRefBPairs = Set.insert (ref2, refB) (fromRefBPairs xs)}
  (_, Just refB) -> xs {fromRefBPairs = Set.insert (ref1, refB) (fromRefBPairs xs)}

exportFromRefBPairs :: UnionFind ref n -> Set (ref, RefB)
exportFromRefBPairs = fromRefBPairs
