{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Optimize.MinimizeConstraints.UIntRelations
  ( UIntRelations,
    Relation (..),
    new,
    lookup,
    bindToValue,
    relate,
    size,
    relationBetween,
    toMap
  )
where

import Control.DeepSeq (NFData)
import Data.IntMap.Strict qualified as IntMap
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung.Compiler.Constraint (RefU (..))
import Keelung.Data.BinRep
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax.Counters
import Prelude hiding (lookup)

data UIntRelations n = UIntRelations
  { links :: Map RefU (Either (Bool, RefU) n),
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

      showLink (var, Left (slope, root)) = "  " <> show var <> " = " <> (if slope then "" else show slope) <> show root <> "\n"
      showLink (var, Right intercept) = "  " <> show var <> " = " <> show intercept <> "\n"

new :: UIntRelations n
new = UIntRelations mempty mempty

data Relation n = Root | Constant n | ChildOf Bool RefU
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the UIntRelations
lookup :: UIntRelations n -> RefU -> Relation n
lookup xs var = case Map.lookup var (links xs) of
  Nothing -> Root -- 'var' is a root
  Just (Right value) -> Constant value -- 'var' is a constant
  Just (Left (relation1, parent)) -> case lookup xs parent of
    Root -> ChildOf relation1 parent -- 'parent' is a root
    Constant value ->
      -- 'parent' is a constant
      Constant value
    ChildOf _ grandparent ->
      -- 'parent' is a child of 'grandparent'
      ChildOf True grandparent

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Just relation` where `var1 = relation == var2` if the two variables are related.
relationBetween :: Eq n => RefU -> RefU -> UIntRelations n -> Maybe Bool
relationBetween var1 var2 xs = case (lookup xs var1, lookup xs var2) of
  (Root, Root) ->
    if var1 == var2
      then Just True
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, ChildOf relation2 root2) ->
    if var1 == root2
      then Just relation2
      else Nothing
  (Root, Constant _) -> Nothing -- var1 is a root, var2 is a constant
  (ChildOf relation1 root1, Root) ->
    if var2 == root1
      then Just relation1
      else Nothing
  (Constant _, Root) -> Nothing -- var1 is a constant, var2 is a root
  (ChildOf relation1 root1, ChildOf relation2 root2) ->
    if root1 == root2
      then Just (relation1 == relation2)
      else Nothing
  (Constant _, ChildOf _ _) -> Nothing -- var1 is a constant
  (ChildOf _ _, Constant _) -> Nothing -- var2 is a constant
  (Constant value1, Constant value2) -> if value1 == value2 then Just True else Just False

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
        { links = Map.insert x (Right value) (links xs),
          sizes = Map.insert x 1 (sizes xs)
        }
    Constant _oldValue ->
      -- x is already a root with `_oldValue` as its value
      -- TODO: handle this kind of conflict in the future
      -- FOR NOW: overwrite the value of x with the new value
      xs
        { links = Map.insert x (Right value) (links xs)
        }
    ChildOf _ parent ->
      xs
        { links =
            Map.insert parent (Right value) $
              Map.insert x (Right value) $
                links xs,
          sizes = Map.insert x 1 (sizes xs)
        }

relate :: RefU -> (Bool, RefU) -> UIntRelations n -> Maybe (UIntRelations n)
relate x (relation, y) xs
  | x > y = relate' x (relation, y) xs
  | x < y = relate' y (relation, x) xs
  | otherwise = Nothing

-- | Establish the relation of 'x = (relation == y)'
--   Returns Nothing if the relation has already been established
relate' :: RefU -> (Bool, RefU) -> UIntRelations n -> Maybe (UIntRelations n)
relate' x (relation, y) xs =
  case lookup xs x of
    Constant constantX ->
      Just $ bindToValue y constantX xs
    ChildOf relationX rootOfX ->
      relate rootOfX (relation == relationX, y) xs
    Root ->
      -- x does not have a parent, so it is its own root
      case lookup xs y of
        Constant constantY ->
          Just $ bindToValue x constantY xs
        ChildOf relationY rootOfY ->
          Just $
            xs
              { links = Map.insert x (Left (relation == relationY, rootOfY)) (links xs),
                sizes = Map.insertWith (+) y 1 (sizes xs)
              }
        Root ->
          -- y does not have a parent, so it is its own root
          Just $
            xs
              { links = Map.insert x (Left (relation, y)) (links xs),
                sizes = Map.insertWith (+) y 1 (sizes xs)
              }

size :: UIntRelations n -> Int
size = Map.size . links

toMap :: UIntRelations n -> Map RefU (Either (Bool, RefU) n)
toMap = links
