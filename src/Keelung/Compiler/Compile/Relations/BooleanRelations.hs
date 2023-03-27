{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Keelung.Compiler.Compile.Relations.BooleanRelations
  ( BooleanRelations,
    Relation (..),
    new,
    lookup,
    bindToValue,
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

data Relation = Root | Constant Bool | ChildOf Bool RefB
  deriving (Eq, Show)

-- | Returns the result of looking up a variable in the BooleanRelations
lookup :: BooleanRelations -> RefB -> Relation
lookup xs var = case Map.lookup var (links xs) of
  Nothing -> Root -- 'var' is a root
  Just (Right value) -> Constant value -- 'var' is a constant
  Just (Left (relation1, parent)) -> case lookup xs parent of
    Root -> ChildOf relation1 parent -- 'parent' is a root
    Constant value ->
      -- 'parent' is a constant
      Constant (relation1 == value)
    ChildOf relation2 grandparent ->
      -- 'parent' is a child of 'grandparent'
      ChildOf (relation1 == relation2) grandparent

-- | Calculates the relation between two variables `var1` and `var2`
--   Returns `Just relation` where `var1 = relation == var2` if the two variables are related.
relationBetween :: RefB -> RefB -> BooleanRelations -> Maybe Bool
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

-- | If the RefB is of RefUBit, remember it
rememberPinnedBitTest :: RefB -> BooleanRelations -> BooleanRelations
rememberPinnedBitTest (RefUBit width ref index) xs = xs {pinnedBitTests = Set.insert (width, ref, index) (pinnedBitTests xs)}
rememberPinnedBitTest _ xs = xs

-- | Bind a variable to a value
bindToValue :: RefB -> Bool -> BooleanRelations -> Except (Error n) BooleanRelations
bindToValue x value xs =
  case lookup xs x of
    Root ->
      -- x does not have a parent, so it is its own root
      return $
        rememberPinnedBitTest x $
          xs
            { links = Map.insert x (Right value) (links xs),
              sizes = Map.insert x 1 (sizes xs)
            }
    Constant oldValue ->
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

relate :: RefB -> (Bool, RefB) -> BooleanRelations -> Except (Error n) (Maybe BooleanRelations)
relate x (relation, y) xs
  | x > y = relate' x (relation, y) xs
  | x < y = relate' y (relation, x) xs
  | otherwise = return Nothing

-- | Establish the relation of 'x = (relation == y)'
--   Returns Nothing if the relation has already been established
relate' :: RefB -> (Bool, RefB) -> BooleanRelations -> Except (Error n) (Maybe BooleanRelations)
relate' x (relation, y) xs =
  case lookup xs x of
    Constant constantX ->
      Just <$> bindToValue y (relation == constantX) xs
    ChildOf relationX rootOfX ->
      relate rootOfX (relation == relationX, y) xs
    Root ->
      -- x does not have a parent, so it is its own root
      case lookup xs y of
        Constant constantY ->
          Just <$> bindToValue x (relation == constantY) xs
        ChildOf relationY rootOfY ->
          return $
            Just $
              rememberPinnedBitTest x $
                xs
                  { links = Map.insert x (Left (relation == relationY, rootOfY)) (links xs),
                    sizes = Map.insertWith (+) y 1 (sizes xs)
                  }
        Root ->
          -- y does not have a parent, so it is its own root
          return $
            Just $
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