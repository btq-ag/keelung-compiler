{-# LANGUAGE FunctionalDependencies #-}

module Keelung.Compiler.Compile.Relations.Relations where

import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map qualified as Map
import Data.Map.Strict (Map)
import Keelung.Compiler.Compile.Relations.Util
import Keelung.Data.N (N (..))
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

class Monoid rel => IsRelation var rel | rel -> var where
  -- | Render a relation to some child as a string
  relationToString :: (var, rel) -> String

  -- | Given `parent = rel child`, executes `rel` on `child`
  --   such that if `child = n`, then `parent = execRelation rel n`
  execRel :: rel -> n -> n

  -- | Computes the inverse of a relation
  invertRel :: rel -> rel

--------------------------------------------------------------------------------

data VarType var n rel = IsConstant n | IsRoot (Map var rel) | IsChildOf var rel

newtype Relations var n rel = Relations {unRelations :: Map var (VarType var n rel)}

instance (GaloisField n, Integral n, Show var, IsRelation var rel) => Show (Relations var n rel) where
  show (Relations relations) =
    "Relations\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList relations)))
    where
      showVar :: var -> String
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString :: (var, VarType var n rel) -> [String]
      toString (var, IsConstant value) = [showVar var <> " = " <> show (N value)]
      toString (var, IsRoot children) = case map relationToString (Map.toList children) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

-- | Creates a new Relations, O(1)
new :: Ord var => Relations var n rel
new = Relations mempty

-- | Returns the result of looking up a variable in the UIntRelations, O(lg n)
lookup :: (GaloisField n, Integral n, Ord var) => var -> Relations var n rel -> VarType var n rel
lookup var (Relations relations) = case Map.lookup var relations of
  Nothing -> IsRoot mempty
  Just result -> result

-- | Assigns a value to a variable, O(lg n)
assign :: (GaloisField n, Integral n, Ord var, IsRelation var rel) => var -> n -> Relations var n rel -> Except (n, n) (Relations var n rel)
assign var value (Relations relations) = case Map.lookup var relations of
  -- The variable is not in the map, so we add it as a constant
  Nothing -> return $ Relations $ Map.insert var (IsConstant value) relations
  -- The variable is already a constant, so we check if the value is the same
  Just (IsConstant oldValue) ->
    if oldValue == value
      then return (Relations relations)
      else throwError (oldValue, value)
  -- The variable is already a root, so we:
  --    1. Make its children constants
  --    2. Make the root itself a constant
  Just (IsRoot children) ->
    return $
      Relations $
        foldl
          ( \rels (child, relationWithParent) ->
              Map.insert
                child
                (IsConstant (execRel (invertRel relationWithParent) value))
                rels
          )
          (Map.insert var (IsConstant value) relations)
          (Map.toList children)
  -- The variable is already a child of another variable, so we:
  --    1. Make the parent a constant (by calling `assign` recursively)
  Just (IsChildOf root relation) ->
    assign root (execRel relation value) (Relations relations)

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relate :: (GaloisField n, Integral n, Seniority var, IsRelation var rel, Ord var) => var -> rel -> var -> Relations var n rel -> Except (n, n) (Relations var n rel)
relate a relation b relations =
  case compareSeniority a b of
    LT -> relateChildToParent a relation b relations
    GT -> relateChildToParent b (invertRel relation) a relations
    EQ -> case compare (childrenSizeOf a) (childrenSizeOf b) of
      LT -> relateChildToParent a relation b relations
      GT -> relateChildToParent b (invertRel relation) a relations
      EQ -> relateChildToParent a relation b relations
      where
        childrenSizeOf ref = case lookup ref relations of
          IsRoot children -> Map.size children
          IsConstant _ -> 0
          IsChildOf parent _ -> childrenSizeOf parent

-- | Relates a child to a parent, O(lg n)
relateChildToParent :: (GaloisField n, Integral n, Ord var, IsRelation var rel) => var -> rel -> var -> Relations var n rel -> Except (n, n) (Relations var n rel)
relateChildToParent child relation parent relations = case lookup parent relations of
  -- The parent is a constant, so we make the child a constant, too
  IsConstant value -> assign child (execRel (invertRel relation) value) relations
  -- The parent has other children
  IsRoot children -> case lookup child relations of
    -- The child also has its grandchildren, so we relate all these grandchildren to the parent, too
    IsRoot grandchildren -> do
      let relations' = Map.insert child (IsChildOf parent relation) (unRelations relations)
      let newSiblings = Map.map (<> relation) grandchildren
      return $ Relations $ Map.insert parent (IsRoot (children <> newSiblings)) relations'
    -- The child is a constant, so we make the parent a constant, too
    IsConstant value -> assign parent (execRel relation value) relations
    -- The child is already a child of another variable, so we relate the child to the grandparent instead
    IsChildOf parent' relationWithParent ->
      -- child = relation parent
      -- child = relationWithParent parent'
      -- =>
      -- parent' = (inv(relationWithParent) <> relation) parent
      relateChildToParent parent' (invertRel relationWithParent <> relation) parent $
        Relations (Map.insert child (IsChildOf parent relation) (unRelations relations))
  -- The parent is a child of another variable, so we relate the child to the grandparent instead
  IsChildOf grandparent relationWithGrandparent -> relateChildToParent child (relation <> relationWithGrandparent) grandparent relations

-- | Calculates the relation between two variables, O(lg n)
relationBetween :: (GaloisField n, Integral n, Ord var, IsRelation var rel) => var -> var -> Relations var n rel -> Maybe rel
relationBetween var1 var2 xs = case (lookup var1 xs, lookup var2 xs) of
  (IsConstant _, _) -> Nothing
  (_, IsConstant _) -> Nothing
  (IsRoot _, IsRoot _) ->
    if var1 == var2
      then Just mempty
      else Nothing
  (IsRoot _, IsChildOf parent2 relationWithParent2) ->
    if var1 == parent2
      then -- var2 = relationWithParent2 parent2
      -- var1 = parent2
      -- =>
      -- var2 = relationWithParent2 var1
        Just (invertRel relationWithParent2)
      else Nothing
  (IsChildOf parent1 relationWithParent1, IsRoot _) ->
    if parent1 == var2
      then -- var1 = relationWithParent1 parent1
      -- parent1 = var2
      -- =>
      -- var1 = relationWithParent1 var2
        Just relationWithParent1
      else Nothing
  (IsChildOf parent1 relationWithParent1, IsChildOf parent2 relationWithParent2) ->
    if parent1 == parent2
      then -- var1 = relationWithParent1 parent1
      -- var2 = relationWithParent2 parent2
      -- parent1 == parent2
      -- =>
      -- var1 = relationWithParent1 parent2
      -- var2 = relationWithParent2 parent2
        Just $ relationWithParent1 <> invertRel relationWithParent2
      else Nothing

-- | Export the internal representation of the relations as a map from variables to their relations
toIntMap :: Relations var n rel -> Map var (VarType var n rel)
toIntMap = unRelations

-- | Returns the number of variables in the Relations, O(1)
size :: Relations var n rel -> Int
size = Map.size . unRelations

-- | A Relations is valid if all children of a parent recognize the parent as their parent
isValid :: (GaloisField n, Integral n, Ord var, IsRelation var rel, Eq rel) => Relations var n rel -> Bool
isValid relations =
  let families = Map.mapMaybe isParent (unRelations relations)

      isParent (IsRoot children) = Just children
      isParent _ = Nothing

      recognizeParent parent child relation = case lookup child relations of
        IsChildOf parent' relation' -> parent == parent' && relation == relation'
        _ -> False
      childrenAllRecognizeParent parent = and . Map.elems . Map.mapWithKey (recognizeParent parent)
   in Map.foldlWithKey' (\acc parent children -> acc && childrenAllRecognizeParent parent children) True families