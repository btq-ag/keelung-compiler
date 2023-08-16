{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Field
  ( Relations,
    new,
    assignF,
    assignB,
    relateB,
    relateRefs,
    relationBetween,
    toInt,
    size,
    lookup,
    Lookup (..),
    exportBooleanRelations,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung (N (N))
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.Boolean qualified as Boolean
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Data.Reference
import Prelude hiding (lookup)

type FieldRelations n = EquivClass.EquivClass Ref n (LinRel n)

data Relations n = Relations
  { relationsF :: FieldRelations n,
    relationsB :: Boolean.BooleanRelations
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (Relations n) where
  show (Relations f b) = show f <> show b

mapError :: EquivClass.M (n, n) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesF)

updateRelationsF ::
  (FieldRelations n -> EquivClass.M (n, n) (FieldRelations n)) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsF f xs = mapError $ do
  relations <- f (relationsF xs)
  return $ xs {relationsF = relations}

updateRelationsB ::
  (Boolean.BooleanRelations -> EquivClass.M (Error n) Boolean.BooleanRelations) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsB f xs = do
  relations <- f (relationsB xs)
  return $ xs {relationsB = relations}

--------------------------------------------------------------------------------

new :: Relations n
new = Relations (EquivClass.new "Field") Boolean.new

assignF :: (GaloisField n, Integral n) => Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
assignF var val = updateRelationsF $ EquivClass.assign var val

assignB :: RefB -> Bool -> Relations n -> EquivClass.M (Error n) (Relations n)
assignB ref val = updateRelationsB $ Boolean.assign ref val

relateF :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
relateF var1 slope var2 intercept = updateRelationsF $ EquivClass.relate var1 (LinRel slope intercept) var2

relateB :: GaloisField n => RefB -> (Bool, RefB) -> Relations n -> EquivClass.M (Error n) (Relations n)
relateB refA (polarity, refB) = updateRelationsB (Boolean.relate refA polarity refB)

-- var = slope * var2 + intercept
relateRefs :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
relateRefs x slope y intercept xs =
  case (x, y, slope, intercept) of
    (B refB, _, 0, value) -> assignB refB (value == 1) xs
    (_, _, 0, value) -> assignF x value xs
    (B refA, B refB, 1, 0) -> relateB refA (True, refB) xs
    (B refA, B refB, -1, 1) -> relateB refA (False, refB) xs
    (refA, refB, _, _) ->
      composeLookup
        xs
        refA
        refB
        slope
        intercept
        (lookup' refA xs)
        (lookup' refB xs)

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> Relations n -> Maybe (n, n)
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 (relationsF xs) of
  Nothing -> Nothing
  Just (LinRel a b) -> Just (a, b)

toInt :: (Ref -> Bool) -> Relations n -> Map Ref (Either (n, Ref, n) n)
toInt shouldBeKept xs = Map.mapMaybeWithKey convert $ EquivClass.toMap (relationsF xs)
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          EquivClass.IsConstant val -> Just (Right val)
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf parent (LinRel slope intercept) ->
            if shouldBeKept parent
              then Just $ Left (slope, parent, intercept)
              else Nothing
        else Nothing

size :: Relations n -> Int
size = Map.size . EquivClass.toMap . relationsF

--------------------------------------------------------------------------------

-- \| Result of looking up a variable in the Relations
data Lookup n = Root | Value n | ChildOf n Ref n
  deriving (Eq, Show)

lookup :: GaloisField n => Ref -> Relations n -> Lookup n
lookup var xs = fromLinRel $ lookup' var xs
  
lookup' :: GaloisField n => Ref -> Relations n -> EquivClass.VarStatus Ref n (LinRel n)
lookup' (B var) xs = fromBooleanLookup $ EquivClass.lookup var (relationsB xs)
lookup' (F var) xs = EquivClass.lookup (F var) (relationsF xs)

fromLinRel :: EquivClass.VarStatus Ref n (LinRel n) -> Lookup n
fromLinRel (EquivClass.IsRoot _) = Root
fromLinRel (EquivClass.IsConstant val) = Value val
fromLinRel (EquivClass.IsChildOf parent (LinRel a b)) = ChildOf a parent b

--------------------------------------------------------------------------------

-- | Relation representing a linear function between two variables, i.e. x = ay + b
data LinRel n
  = LinRel
      n
      -- ^ slope
      n
      -- ^ intercept
  deriving (Show, Eq, NFData, Generic)

instance Num n => Semigroup (LinRel n) where
  -- x = a1 * y + b1
  -- y = a2 * z + b2
  -- =>
  -- x = a1 * (a2 * z + b2) + b1
  --   = (a1 * a2) * z + (a1 * b2 + b1)
  LinRel a1 b1 <> LinRel a2 b2 = LinRel (a1 * a2) (a1 * b2 + b1)

instance Num n => Monoid (LinRel n) where
  mempty = LinRel 1 0

instance (GaloisField n, Integral n) => EquivClass.IsRelation (LinRel n) where
  relationToString (var, LinRel x y) = f (EquivClass.invertRel $ LinRel x y)
    where
      f (LinRel a b) =
        let slope = case a of
              1 -> var
              (-1) -> "-" <> var
              _ -> show (N a) <> var
            intercept = case b of
              0 -> ""
              -- -1 -> " - 1"
              _ -> " + " <> show (N b)
         in slope <> intercept

  -- x = ay + b
  -- =>
  -- y = (x - b) / a
  invertRel (LinRel a b) = LinRel (recip a) (-b / a)

instance (GaloisField n, Integral n) => EquivClass.ExecRelation n (LinRel n) where
  execRel (LinRel a b) value = a * value + b

--------------------------------------------------------------------------------

fromBooleanLookup :: GaloisField n => EquivClass.VarStatus RefB Bool Boolean.Polarity -> EquivClass.VarStatus Ref n (LinRel n)
fromBooleanLookup (EquivClass.IsRoot children) = EquivClass.IsRoot $ Map.mapKeys B $ Map.map (\b -> if Boolean.unPolarity b then LinRel 1 0 else LinRel (-1) 1) children
fromBooleanLookup (EquivClass.IsConstant True) = EquivClass.IsConstant 1
fromBooleanLookup (EquivClass.IsConstant False) = EquivClass.IsConstant 0
fromBooleanLookup (EquivClass.IsChildOf parent (Boolean.Polarity True)) = EquivClass.IsChildOf (B parent) (LinRel 1 0)
fromBooleanLookup (EquivClass.IsChildOf parent (Boolean.Polarity False)) = EquivClass.IsChildOf (B parent) (LinRel (-1) 1)

composeLookup :: (GaloisField n, Integral n) => Relations n -> Ref -> Ref -> n -> n -> EquivClass.VarStatus Ref n (LinRel n) -> EquivClass.VarStatus Ref n (LinRel n) -> EquivClass.M (Error n) (Relations n)
composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
  (EquivClass.IsRoot _, EquivClass.IsRoot _) ->
    -- rootA = slope * rootB + intercept
    relateF refA slope refB intercept xs
  (EquivClass.IsRoot _, EquivClass.IsConstant n) ->
    -- rootA = slope * n + intercept
    assignF refA (slope * n + intercept) xs
  (EquivClass.IsRoot _, EquivClass.IsChildOf rootB (LinRel slopeB interceptB)) ->
    -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
    -- =>
    -- rootA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
    relateF refA (slope * slopeB) rootB (slope * interceptB + intercept) xs
  (EquivClass.IsConstant n, EquivClass.IsRoot _) ->
    -- n = slope * rootB + intercept
    -- =>
    -- rootB = (n - intercept) / slope
    assignF refB ((n - intercept) / slope) xs
  (EquivClass.IsConstant n, EquivClass.IsConstant m) ->
    -- n = slope * m + intercept
    -- =>
    -- n - intercept = slope * m
    -- =>
    -- m = (n - intercept) / slope
    if m == (n - intercept) / slope
      then return xs
      else throwError $ ConflictingValuesF m ((n - intercept) / slope)
  (EquivClass.IsConstant n, EquivClass.IsChildOf rootB (LinRel slopeB interceptB)) ->
    -- n = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slope * (slopeB * rootB + interceptB) = n - intercept
    -- =>
    -- slopeB * rootB + interceptB = (n - intercept) / slope
    -- =>
    -- slopeB * rootB = (n - intercept) / slope - interceptB
    -- =>
    -- rootB = ((n - intercept) / slope - interceptB) / slopeB
    assignF rootB (((n - intercept) / slope - interceptB) / slopeB) xs
  (EquivClass.IsChildOf rootA (LinRel slopeA interceptA), EquivClass.IsRoot _) ->
    -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    relateF rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
  (EquivClass.IsChildOf rootA (LinRel slopeA interceptA), EquivClass.IsConstant n) ->
    -- refA = slopeA * rootA + interceptA = slope * n + intercept
    -- =>
    -- rootA = (slope * n + intercept - interceptA) / slopeA
    assignF rootA ((slope * n + intercept - interceptA) / slopeA) xs
  (EquivClass.IsChildOf rootA (LinRel slopeA interceptA), EquivClass.IsChildOf rootB (LinRel slopeB interceptB)) ->
    -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
    -- =>
    -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
    relateF rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs

exportBooleanRelations :: Relations n -> Boolean.BooleanRelations
exportBooleanRelations = relationsB