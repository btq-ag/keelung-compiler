{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Compile.Relations.UIntRelations
  ( UIntRelations,
    Lookup (..),
    new,
    lookup,
    bindToValue,
    assertEqual,
    -- rotate,
    size,
    relationBetween,
    toMap,
  )
where

import Control.DeepSeq (NFData)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint (RefU (..))
import Prelude hiding (lookup)

-- | Relation between a variable and a value or another variable
data Relation n
  = -- | The variable is a rotation of another variable
    Rotate Int RefU
  | -- | The variable is a constant
    Constant n
  deriving (Eq, Show, Generic, NFData)

data UIntRelations n = UIntRelations
  { links :: Map RefU (Relation n),
    sizes :: Map RefU Int
  }
  deriving (Eq, Generic, NFData)

instance Show n => Show (UIntRelations n) where
  show xs =
    "UIntRelations {\n"
      ++ "  sizes = "
      ++ showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ sizes xs))
      ++ "\n\n"
      ++ mconcat (map showLink (Map.toList $ links xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

      showLink (var, Rotate offset root) = "  " <> show var <> " = " <> show root <> " <<< " <> show offset <> "\n"
      showLink (var, Constant value) = "  " <> show var <> " = " <> show value <> "\n"

new :: UIntRelations n
new = UIntRelations mempty mempty

data Lookup n = Root | Value n | RotateOf Int RefU
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the UIntRelations
lookup :: UIntRelations n -> RefU -> Lookup n
lookup xs var = case Map.lookup var (links xs) of
  Nothing -> Root -- 'var' is a root
  Just (Constant value) -> Value value -- 'var' is a value
  Just (Rotate offset parent) -> case lookup xs parent of
    Root -> RotateOf offset parent -- 'parent' is a root
    Value value ->
      -- 'parent' is a value
      Value value
    RotateOf offset' grandparent ->
      -- 'parent' is a child of 'grandparent'
      RotateOf (offset + offset') grandparent

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Just relation` where `var1 = relation == var2` if the two variables are rotated.
relationBetween :: Eq n => RefU -> RefU -> UIntRelations n -> Maybe Bool
relationBetween var1 var2 xs = case (lookup xs var1, lookup xs var2) of
  (Root, Root) ->
    if var1 == var2
      then Just True
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, RotateOf rotate2 root2) ->
    if var1 == root2
      then Just (rotate2 == 0)
      else Nothing
  (Root, Value _) -> Nothing -- var1 is a root, var2 is a value
  (RotateOf rotate1 root1, Root) ->
    if var2 == root1
      then Just (rotate1 == 0)
      else Nothing
  (Value _, Root) -> Nothing -- var1 is a value, var2 is a root
  (RotateOf relation1 root1, RotateOf relation2 root2) ->
    if root1 == root2
      then Just (relation1 == relation2)
      else Nothing
  (Value _, RotateOf _ _) -> Nothing -- var1 is a value
  (RotateOf _ _, Value _) -> Nothing -- var2 is a value
  (Value value1, Value value2) -> if value1 == value2 then Just True else Just False

-- | If the RefU is of RefUBit, remember it
-- rememberPinnedBitTest :: RefU -> UIntRelations -> UIntRelations
-- rememberPinnedBitTest (RefUBit width ref index) xs = xs {pinnedBitTests = Set.insert (width, ref, index) (pinnedBitTests xs)}
-- rememberPinnedBitTest _ xs = xs

-- | Bind a variable to a value
bindToValue :: RefU -> n -> UIntRelations n -> UIntRelations n
bindToValue x value xs =
  case lookup xs x of
    Root ->
      -- x does not have a parent, so it is its own root
      xs
        { links = Map.insert x (Constant value) (links xs),
          sizes = Map.insert x 1 (sizes xs)
        }
    Value _oldValue ->
      -- x is already a root with `_oldValue` as its value
      -- TODO: handle this kind of conflict in the future
      -- FOR NOW: overwrite the value of x with the new value
      xs
        { links = Map.insert x (Constant value) (links xs)
        }
    RotateOf _ parent ->
      xs
        { links =
            Map.insert parent (Constant value) $
              Map.insert x (Constant value) $
                links xs,
          sizes = Map.insert x 1 (sizes xs)
        }

-- | Assert that two variables are equal
assertEqual :: RefU -> RefU -> UIntRelations n -> Maybe (UIntRelations n)
assertEqual x y = rotate x (0, y)

rotate :: RefU -> (Int, RefU) -> UIntRelations n -> Maybe (UIntRelations n)
rotate x (rotation, y) xs
  | x > y = rotate' x (rotation, y) xs
  | x < y = rotate' y (rotation, x) xs
  | otherwise = Nothing

-- | Returns Nothing if the relation has already been established
rotate' :: RefU -> (Int, RefU) -> UIntRelations n -> Maybe (UIntRelations n)
rotate' x (rotation, y) xs =
  case lookup xs x of
    Value valueX ->
      Just $ bindToValue y valueX xs
    RotateOf rotationX rootOfX ->
      rotate rootOfX (rotation + rotationX, y) xs
    Root ->
      -- x does not have a parent, so it is its own root
      case lookup xs y of
        Value valueY ->
          Just $ bindToValue x valueY xs
        RotateOf rotationY rootOfY ->
          Just $
            xs
              { links = Map.insert x (Rotate (rotation + rotationY) rootOfY) (links xs),
                sizes = Map.insertWith (+) y 1 (sizes xs)
              }
        Root ->
          -- y does not have a parent, so it is its own root
          Just $
            xs
              { links = Map.insert x (Rotate rotation y) (links xs),
                sizes = Map.insertWith (+) y 1 (sizes xs)
              }

size :: UIntRelations n -> Int
size = Map.size . links

toMap :: UIntRelations n -> Map RefU (Relation n)
toMap = links
