{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Field
  ( Relations,
    new,
    assignF,
    assignB,
    assignL,
    assignU,
    relateB,
    relateL,
    relateU,
    relateRefs,
    relationBetween,
    toInt,
    size,
    lookup,
    Lookup (..),
    exportBooleanRelations,
    exportLimbRelations,
    exportUIntRelations,
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
import Keelung.Compiler.Relations.Limb qualified as Limb
import Keelung.Compiler.Relations.UInt qualified as UInt
import Keelung.Data.Reference
import Prelude hiding (lookup)

type FieldRelations n = EquivClass.EquivClass Ref n (LinRel n)

data Relations n = Relations
  { relationsF :: FieldRelations n,
    relationsB :: Boolean.BooleanRelations,
    relationsL :: Limb.LimbRelations,
    relationsU :: UInt.UIntRelations
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (Relations n) where
  show (Relations f b l u) =
    (if EquivClass.size f == 0 then "" else show f)
      <> (if EquivClass.size b == 0 then "" else show b)
      <> (if EquivClass.size l == 0 then "" else show l)
      <> (if EquivClass.size u == 0 then "" else show u)

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

updateRelationsL ::
  (Limb.LimbRelations -> EquivClass.M (Error n) Limb.LimbRelations) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsL f xs = do
  relations <- f (relationsL xs)
  return $ xs {relationsL = relations}

updateRelationsU ::
  (UInt.UIntRelations -> EquivClass.M (Error n) UInt.UIntRelations) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsU f xs = do
  relations <- f (relationsU xs)
  return $ xs {relationsU = relations}

--------------------------------------------------------------------------------

new :: Relations n
new = Relations (EquivClass.new "Field") Boolean.new Limb.new UInt.new

assignF :: (GaloisField n, Integral n) => Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
assignF var val = updateRelationsF $ EquivClass.assign var val

assignB :: RefB -> Bool -> Relations n -> EquivClass.M (Error n) (Relations n)
assignB ref val = updateRelationsB $ Boolean.assign ref val

assignL :: (GaloisField n, Integral n) => Limb -> Integer -> Relations n -> EquivClass.M (Error n) (Relations n)
assignL var val = updateRelationsL $ Limb.assign var val

assignU :: (GaloisField n, Integral n) => RefU -> Integer -> Relations n -> EquivClass.M (Error n) (Relations n)
assignU var val = updateRelationsU $ UInt.assign var val

relateF :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
relateF var1 slope var2 intercept = updateRelationsF $ EquivClass.relate var1 (LinRel slope intercept) var2

relateB :: GaloisField n => RefB -> (Bool, RefB) -> Relations n -> EquivClass.M (Error n) (Relations n)
relateB refA (polarity, refB) = updateRelationsB (Boolean.relate refA polarity refB)

relateL :: (GaloisField n, Integral n) => Limb -> Limb -> Relations n -> EquivClass.M (Error n) (Relations n)
relateL var1 var2 = updateRelationsL $ Limb.relate var1 var2

relateU :: (GaloisField n, Integral n) => RefU -> RefU -> Relations n -> EquivClass.M (Error n) (Relations n)
relateU var1 var2 = updateRelationsU $ UInt.relate var1 var2

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
        (lookup refA xs)
        (lookup refB xs)

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
size (Relations f b l u) = EquivClass.size f + Boolean.size b + Limb.size l + UInt.size u

--------------------------------------------------------------------------------

-- | Result of looking up a variable in the Relations
data Lookup n = Root | Value n | ChildOf n Ref n
  deriving
    ( -- | ChildOfU RefU
      Eq,
      Show
    )

lookup :: GaloisField n => Ref -> Relations n -> Lookup n
lookup (B var) xs =
  case var of
    RefUBit _ refU _index -> case EquivClass.lookup refU (relationsU xs) of
      EquivClass.IsConstant _value -> Root
      -- Value (if Data.Bits.testBit value index then 1 else 0)
      -- Root -- Value (if Data.Bits.testBit value index then 1 else 0)
      EquivClass.IsRoot _ -> Root
      EquivClass.IsChildOf _parent () -> Root
    _ ->
      case EquivClass.lookup var (relationsB xs) of
        EquivClass.IsConstant True -> Value 1
        EquivClass.IsConstant False -> Value 0
        EquivClass.IsRoot _ -> Root
        EquivClass.IsChildOf parent (Boolean.Polarity True) -> ChildOf 1 (B parent) 0
        EquivClass.IsChildOf parent (Boolean.Polarity False) -> ChildOf (-1) (B parent) 1
lookup (F var) xs = case EquivClass.lookup (F var) (relationsF xs) of
  EquivClass.IsConstant value -> Value value
  EquivClass.IsRoot _ -> Root
  EquivClass.IsChildOf parent (LinRel a b) -> ChildOf a parent b

-- fromBooleanLookup :: GaloisField n => EquivClass.VarStatus RefB Bool Boolean.Polarity -> EquivClass.VarStatus Ref n (LinRel n)
-- fromBooleanLookup (EquivClass.IsRoot children) = EquivClass.IsRoot $ Map.mapKeys B $ Map.map (\b -> if Boolean.unPolarity b then LinRel 1 0 else LinRel (-1) 1) children

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
  relationToString (var, LinRel x y) = f (LinRel (recip x) (-y / x))
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
  invertRel (LinRel a b) = Just (LinRel (recip a) (-b / a))

instance (GaloisField n, Integral n) => EquivClass.ExecRelation n (LinRel n) where
  execRel (LinRel a b) value = a * value + b

--------------------------------------------------------------------------------

composeLookup :: (GaloisField n, Integral n) => Relations n -> Ref -> Ref -> n -> n -> Lookup n -> Lookup n -> EquivClass.M (Error n) (Relations n)
composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
  (Root, Root) ->
    -- rootA = slope * rootB + intercept
    relateF refA slope refB intercept xs
  (Root, Value n) ->
    -- rootA = slope * n + intercept
    assignF refA (slope * n + intercept) xs
  (Root, ChildOf slopeB rootB interceptB) ->
    -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
    -- =>
    -- rootA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
    relateF refA (slope * slopeB) rootB (slope * interceptB + intercept) xs
  (Value n, Root) ->
    -- n = slope * rootB + intercept
    -- =>
    -- rootB = (n - intercept) / slope
    assignF refB ((n - intercept) / slope) xs
  (Value n, Value m) ->
    -- n = slope * m + intercept
    -- =>
    -- n - intercept = slope * m
    -- =>
    -- m = (n - intercept) / slope
    if m == (n - intercept) / slope
      then return xs
      else throwError $ ConflictingValuesF m ((n - intercept) / slope)
  (Value n, ChildOf slopeB rootB interceptB) ->
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
  (ChildOf slopeA rootA interceptA, Root) ->
    -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    relateF rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, Value n) ->
    -- refA = slopeA * rootA + interceptA = slope * n + intercept
    -- =>
    -- rootA = (slope * n + intercept - interceptA) / slopeA
    assignF rootA ((slope * n + intercept - interceptA) / slopeA) xs
  (ChildOf slopeA rootA interceptA, ChildOf slopeB rootB interceptB) ->
    -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
    -- =>
    -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
    relateF rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs

exportBooleanRelations :: Relations n -> Boolean.BooleanRelations
exportBooleanRelations = relationsB

exportLimbRelations :: Relations n -> Limb.LimbRelations
exportLimbRelations = relationsL

exportUIntRelations :: Relations n -> UInt.UIntRelations
exportUIntRelations = relationsU