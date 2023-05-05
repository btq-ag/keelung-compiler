{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile.Relations.EquivClass
  ( IsRelation (..),
    ExecRelation (..),
    EquivClass,
    VarStatus (..),
    M,
    runM,
    mapError,
    markChanged,
    new,
    assign,
    relate,
    relationBetween,
    toMap,
    isValid,
    size,
    lookup,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Control.Monad.Writer
import Data.Field.Galois (Binary, Prime)
import Data.Map qualified as Map
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import GHC.TypeLits
import Keelung.Compiler.Compile.Relations.Util
import Keelung.Data.N (N (..))
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

class Monoid rel => IsRelation rel where
  -- | Render a relation to some child as a string
  relationToString :: (String, rel) -> String

  -- | Computes the inverse of a relation
  invertRel :: rel -> rel

class ExecRelation n rel where
  -- | Given `parent = rel child`, executes `rel` on `child`
  --   such that if `child = n`, then `parent = execRel rel n`
  execRel :: rel -> n -> n

--------------------------------------------------------------------------------

type M err = WriterT [()] (Except err)

runM :: M err a -> Except err (Maybe a)
runM xs = do
  (x, changes) <- runWriterT xs
  if null changes
    then return Nothing
    else return (Just x)

markChanged :: M err ()
markChanged = tell [()]

mapError :: (err -> err') -> M err a -> M err' a
mapError f xs = case runExcept (runWriterT xs) of
  Left err -> throwError (f err)
  Right (x, changes) -> tell changes >> return x

--------------------------------------------------------------------------------

data VarStatus var n rel
  = IsConstant n
  | IsRoot (Map var rel)
  | -- | var = relation root
    IsChildOf var rel
  deriving (Show, Eq, Generic, NFData)

data EquivClass var n rel = EquivClass
  { eqPoolName :: String,
    eqPoolEquivClass :: Map var (VarStatus var n rel)
  }
  deriving (Eq, Generic)

instance (NFData var, NFData n, NFData rel) => NFData (EquivClass var n rel)

-- | Instance for pretty-printing EquivClass with Galois fields as constant values
instance {-# OVERLAPS #-} (KnownNat n, Show var, IsRelation rel) => Show (EquivClass var (Prime n) rel) where
  show (EquivClass name relations) =
    name
      <> "\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList relations)))
    where
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show (N value)]
      toString (var, IsRoot children) = case map relationToString (Map.toList $ Map.mapKeys show children) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

-- | Instance for pretty-printing EquivClass with Galois fields as constant values
instance {-# OVERLAPPING #-} (KnownNat n, Show var, IsRelation rel) => Show (EquivClass var (Binary n) rel) where
  show (EquivClass name relations) =
    name
      <> "\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList relations)))
    where
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show (N value)]
      toString (var, IsRoot children) = case map relationToString (Map.toList $ Map.mapKeys show children) of
        [] -> [showVar var <> " = []"]
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

instance (Show var, IsRelation rel, Show n) => Show (EquivClass var n rel) where
  show (EquivClass name relations) =
    name
      <> "\n"
      <> mconcat (map (<> "\n") (concatMap toString (Map.toList relations)))
    where
      showVar var = let varString = show var in "  " <> varString <> replicate (8 - length varString) ' '

      toString (var, IsConstant value) = [showVar var <> " = " <> show value]
      toString (var, IsRoot children) = case map relationToString (Map.toList $ Map.mapKeys show children) of
        [] -> [showVar var <> " = []"] -- should never happen
        (x : xs) -> showVar var <> " = " <> x : map ("           = " <>) xs
      toString (_var, IsChildOf _parent _relation) = []

-- | Creates a new EquivClass, O(1)
new :: Ord var => String -> EquivClass var n rel
new name = EquivClass name mempty

-- | Returns the result of looking up a variable in the UIntEquivClass, O(lg n)
lookup :: (Ord var) => var -> EquivClass var n rel -> VarStatus var n rel
lookup var (EquivClass _ relations) = case Map.lookup var relations of
  Nothing -> IsRoot mempty
  Just result -> result

-- | Assigns a value to a variable, O(lg n)
assign :: (Ord var, IsRelation rel, Eq n, ExecRelation n rel) => var -> n -> EquivClass var n rel -> M (n, n) (EquivClass var n rel)
assign var value (EquivClass name relations) = case Map.lookup var relations of
  -- The variable is not in the map, so we add it as a constant
  Nothing -> do
    markChanged
    return $ EquivClass name $ Map.insert var (IsConstant value) relations
  -- The variable is already a constant, so we check if the value is the same
  Just (IsConstant oldValue) ->
    if oldValue == value
      then return (EquivClass name relations)
      else throwError (oldValue, value)
  -- The variable is already a root, so we:
  --    1. Make its children constants
  --    2. Make the root itself a constant
  Just (IsRoot children) -> do
    markChanged
    return $
      EquivClass name $
        foldl
          ( \rels (child, relationWithParent) ->
              Map.insert
                child
                (IsConstant (execRel relationWithParent value))
                rels
          )
          (Map.insert var (IsConstant value) relations)
          (Map.toList children)
  -- The variable is already a child of another variable, so we:
  --    1. Make the parent a constant (by calling `assign` recursively)
  -- child = relation root
  -- =>
  -- root = relation^-1 child
  Just (IsChildOf root relation) ->
    assign root (execRel (invertRel relation) value) (EquivClass name relations)

-- | Relates two variables, using the more "senior" one as the root, if they have the same seniority, the one with the most children is used, O(lg n)
relate :: (Seniority var, IsRelation rel, Ord var, Eq n, ExecRelation n rel) => var -> rel -> var -> EquivClass var n rel -> M (n, n) (EquivClass var n rel)
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
relateChildToParent :: (Ord var, IsRelation rel, Eq n, Seniority var, ExecRelation n rel) => var -> rel -> var -> EquivClass var n rel -> M (n, n) (EquivClass var n rel)
relateChildToParent child relation parent relations =
  if child == parent
    then return relations
    else case lookup parent relations of
      -- The parent is a constant, so we make the child a constant:
      --    * for the parent: do nothing
      --    * for the child: assign it the value of the parent with the inverted relation applied
      IsConstant value -> assign child (execRel (invertRel relation) value) relations
      -- The parent has other children
      IsRoot children -> case lookup child relations of
        -- The child also has its grandchildren, so we relate all these grandchildren to the parent, too:
        --    * for the parent: add the child and its grandchildren to the children map
        --    * for the child: point the child to the parent and add the relation
        --    * for the grandchildren: point them to the new parent
        IsRoot grandchildren -> do
          markChanged
          let newSiblings = Map.insert child relation $ Map.map (<> relation) grandchildren
          return $
            EquivClass (eqPoolName relations) $
              Map.insert parent (IsRoot (children <> newSiblings)) $ -- add the child and its grandchildren to the parent
                Map.insert child (IsChildOf parent relation) $ -- point the child to the parent
                  Map.foldlWithKey' -- point the grandchildren to the new parent
                    ( \rels grandchild rel -> Map.insert grandchild (IsChildOf parent (rel <> relation)) rels
                    )
                    (eqPoolEquivClass relations)
                    grandchildren
        --
        -- The child is a constant, so we make the parent a constant, too:
        --  * for the parent: assign it the value of the child with the relation applied
        --  * for the child: do nothing
        IsConstant value -> assign parent (execRel relation value) relations
        -- The child is already a child of another variable:
        --    * for the another variable: point it to the parent with `invertRel relationWithParent <> relation`
        --    * for the parent: add the child and the another variable to the children map
        --    * for the child: point it to the parent with `relation`
        IsChildOf parent' relationWithParent ->
          if parent' `compareSeniority` parent == GT
            then --
            -- child = relation parent
            -- child = relationWithParent parent'
            -- => parent = (invertRel relation <> relationWithParent) parent'
              relate parent (invertRel relation <> relationWithParent) parent' relations
            else do
              --
              -- child = relation parent
              -- child = relationWithParent parent'
              -- => parent' = (invertRel relationWithParent <> relation) parent
              markChanged
              relate parent' (invertRel relationWithParent <> relation) parent $
                EquivClass (eqPoolName relations) $
                  Map.insert child (IsChildOf parent relation) $
                    eqPoolEquivClass relations
      -- The parent is a child of another variable, so we relate the child to the grandparent instead
      IsChildOf grandparent relationWithGrandparent -> relate child (relation <> relationWithGrandparent) grandparent relations

-- | Calculates the relation between two variables, O(lg n)
relationBetween :: (Ord var, IsRelation rel) => var -> var -> EquivClass var n rel -> Maybe rel
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
toMap :: EquivClass var n rel -> Map var (VarStatus var n rel)
toMap = eqPoolEquivClass

-- | Returns the number of variables in the EquivClass, O(1)
size :: EquivClass var n rel -> Int
size = Map.size . eqPoolEquivClass

-- | A EquivClass is valid if:
--          1. all children of a parent recognize the parent as their parent
isValid :: (Ord var, IsRelation rel, Eq rel, Seniority var) => EquivClass var n rel -> Bool
isValid relations = allChildrenRecognizeTheirParent relations && rootsAreSenior relations

-- | A EquivClass is valid if all children of a parent recognize the parent as their parent
allChildrenRecognizeTheirParent :: (Ord var, IsRelation rel, Eq rel) => EquivClass var n rel -> Bool
allChildrenRecognizeTheirParent relations =
  let families = Map.mapMaybe isParent (eqPoolEquivClass relations)

      isParent (IsRoot children) = Just children
      isParent _ = Nothing

      recognizeParent parent child relation = case lookup child relations of
        IsChildOf parent' relation' -> parent == parent' && relation == relation'
        _ -> False
      childrenAllRecognizeParent parent = and . Map.elems . Map.mapWithKey (recognizeParent parent)
   in Map.foldlWithKey' (\acc parent children -> acc && childrenAllRecognizeParent parent children) True families

-- | A EquivClass is valid if the seniority of the root of a family is greater than equal the seniority of all its children
rootsAreSenior :: (Ord var, IsRelation rel, Eq rel, Seniority var) => EquivClass var n rel -> Bool
rootsAreSenior = Map.foldlWithKey' go True . eqPoolEquivClass
  where
    go :: Seniority var => Bool -> var -> VarStatus var n rel -> Bool
    go False _ _ = False
    go True _ (IsConstant _) = True
    go True var (IsRoot children) = all (\child -> compareSeniority var child /= LT) (Map.keys children)
    go True var (IsChildOf parent _) = compareSeniority parent var /= LT