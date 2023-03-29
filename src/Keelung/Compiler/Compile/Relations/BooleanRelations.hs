{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Compile.Relations.BooleanRelations
  ( BooleanRelations,
    Relation (..),
    new,
    lookup,
    assign,
    relate,
    exportPinnedBitTests,
    size,
    relationBetween,
    toIntMap,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Constraint (RefB (..), RefU)
import Keelung.Syntax (Width)
import Prelude hiding (lookup)

data BooleanRelations = BooleanRelations
  { links :: Map RefB (Either (Bool, RefB) Bool),
    sizes :: Map RefB Int,
    -- | Here stores bit tests on pinned UInt variables, so that we can export them as constraints later.
    pinnedBitTests :: Set (Width, RefU, Int)
  }
  deriving (Eq, Generic, NFData)

instance Show BooleanRelations where
  show xs =
    "BooleanRelations {\n"
      ++ "  sizes = "
      ++ showList' (map (\(var, n) -> show var <> ": " <> show n) (Map.toList $ sizes xs))
      ++ "\n\n"
      ++ "  pinnedBitTests = " <> show (Set.toList (exportPinnedBitTests xs)) <> "\n\n"
      ++ mconcat (map showLink (Map.toList $ links xs))
      ++ "\n}"
    where
      showList' ys = "[" <> List.intercalate ", " ys <> "]"

      showLink (var, Left (dontFlip, root)) = "  " <> show var <> " = " <> (if dontFlip then "" else "¬ ") <> show root <> "\n"
      showLink (var, Right intercept) = "  " <> show var <> " = " <> show intercept <> "\n"

new :: BooleanRelations
new = BooleanRelations mempty mempty mempty

data Relation = Root | Value Bool | ChildOf Bool RefB
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the BooleanRelations
lookup :: RefB -> BooleanRelations -> Relation
lookup var xs = case Map.lookup var (links xs) of
  Nothing -> Root -- 'var' is a root
  Just (Right value) -> Value value -- 'var' is a constant
  Just (Left (relation1, parent)) -> case lookup parent xs of
    Root -> ChildOf relation1 parent -- 'parent' is a root
    Value value ->
      -- 'parent' is a constant
      Value (relation1 == value)
    ChildOf relation2 grandparent ->
      -- 'parent' is a child of 'grandparent'
      ChildOf (relation1 == relation2) grandparent

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Just relation` where `var1 = relation == var2` if the two variables are related.
relationBetween :: RefB -> RefB -> BooleanRelations -> Maybe Bool
relationBetween var1 var2 xs = case (lookup var1 xs, lookup var2 xs) of
  (Root, Root) ->
    if var1 == var2
      then Just True
      else Nothing -- var1 and var2 are roots, but not the same one
  (Root, ChildOf relation2 root2) ->
    if var1 == root2
      then Just relation2
      else Nothing
  (Root, Value _) -> Nothing -- var1 is a root, var2 is a constant
  (ChildOf relation1 root1, Root) ->
    if var2 == root1
      then Just relation1
      else Nothing
  (Value _, Root) -> Nothing -- var1 is a constant, var2 is a root
  (ChildOf relation1 root1, ChildOf relation2 root2) ->
    if root1 == root2
      then Just (relation1 == relation2)
      else Nothing
  (Value _, ChildOf _ _) -> Nothing -- var1 is a constant
  (ChildOf _ _, Value _) -> Nothing -- var2 is a constant
  (Value value1, Value value2) -> if value1 == value2 then Just True else Just False

-- | If the RefB is of RefUBit, remember it
rememberPinnedBitTest :: RefB -> BooleanRelations -> BooleanRelations
rememberPinnedBitTest (RefUBit width ref index) xs = xs {pinnedBitTests = Set.insert (width, ref, index) (pinnedBitTests xs)}
rememberPinnedBitTest _ xs = xs

-- | Bind a variable to a value
assign :: RefB -> Bool -> BooleanRelations -> Except (Error n) BooleanRelations
assign x value xs =
  case lookup x xs of
    Root ->
      -- x does not have a parent, so it is its own root
      return $
        rememberPinnedBitTest x $
          xs
            { links = Map.insert x (Right value) (links xs),
              sizes = Map.insert x 1 (sizes xs)
            }
    Value oldValue ->
      if oldValue == value
        then
          return $
            rememberPinnedBitTest x $
              xs
                { links = Map.insert x (Right value) (links xs)
                }
        else throwError $ ConflictingValuesB oldValue value
    ChildOf relation parent ->
      return $
        rememberPinnedBitTest x $
          xs
            { links =
                Map.insert parent (Right (value == relation)) $
                  Map.insert x (Right value) $
                    links xs,
              sizes = Map.insert x 1 (sizes xs)
            }

relate :: RefB -> Bool -> RefB -> BooleanRelations -> Except (Error n) BooleanRelations
relate x polarity y xs
  | x > y = relate' x polarity y xs
  | x < y = relate' y polarity x xs
  | otherwise = return xs

-- | Establish the relation of 'x = (relation == y)'
--   Returns Nothing if the relation has already been established
relate' :: RefB -> Bool -> RefB -> BooleanRelations -> Except (Error n) BooleanRelations
relate' x relation y xs =
  case lookup x xs of
    Value constantX ->
      assign y (relation == constantX) xs
    ChildOf relationX rootOfX ->
      relate rootOfX (relation == relationX) y xs
    Root ->
      -- x does not have a parent, so it is its own root
      case lookup y xs of
        Value constantY ->
          assign x (relation == constantY) xs
        ChildOf relationY rootOfY ->
          return $
              rememberPinnedBitTest x $
                xs
                  { links = Map.insert x (Left (relation == relationY, rootOfY)) (links xs),
                    sizes = Map.insertWith (+) y 1 (sizes xs)
                  }
        Root ->
          -- y does not have a parent, so it is its own root
          return $
              rememberPinnedBitTest x $
                xs
                  { links = Map.insert x (Left (relation, y)) (links xs),
                    sizes = Map.insertWith (+) y 1 (sizes xs)
                  }

size :: BooleanRelations -> Int
size = Map.size . links

exportPinnedBitTests :: BooleanRelations -> Set RefB
exportPinnedBitTests = Set.map (\(w, ref, i) -> RefUBit w ref i) . pinnedBitTests

toIntMap :: BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
toIntMap = links