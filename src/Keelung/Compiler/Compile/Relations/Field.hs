{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile.Relations.Field
  ( AllRelations,
    new,
    assignF,
    assignB,
    assignU,
    relateB,
    relateRefs,
    assertEqual,
    assertEqualU,
    relationBetween,
    toInt,
    size,
    isValid,
    lookup,
    lookup',
    Lookup (..),
    exportBooleanRelations,
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
import Keelung.Compiler.Compile.Relations.Boolean qualified as Boolean
import Keelung.Compiler.Compile.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Compile.Relations.UInt qualified as UInt
import Keelung.Compiler.Constraint
import Prelude hiding (lookup)

type FieldRelations n = EquivClass.EquivClass Ref n (LinRel n)

data AllRelations n = AllRelations
  { relationsF :: FieldRelations n,
    relationsB :: Boolean.BooleanRelations,
    relationsU :: UInt.UIntRelations n
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (AllRelations n) where
  show (AllRelations f b u) = show f <> show b <> show u

mapError :: EquivClass.M (n, n) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesF)

updateRelationsF ::
  (FieldRelations n -> EquivClass.M (n, n) (FieldRelations n)) ->
  AllRelations n ->
  EquivClass.M (Error n) (AllRelations n)
updateRelationsF f xs = mapError $ do
  relations <- f (relationsF xs)
  return $ xs {relationsF = relations}

updateRelationsB ::
  (Boolean.BooleanRelations -> EquivClass.M (Error n) Boolean.BooleanRelations) ->
  AllRelations n ->
  EquivClass.M (Error n) (AllRelations n)
updateRelationsB f xs = do
  relations <- f (relationsB xs)
  return $ xs {relationsB = relations}

updateRelationsU ::
  (UInt.UIntRelations n -> EquivClass.M (Error n) (UInt.UIntRelations n)) ->
  AllRelations n ->
  EquivClass.M (Error n) (AllRelations n)
updateRelationsU f xs = do
  relations <- f (relationsU xs)
  return $ xs {relationsU = relations}

--------------------------------------------------------------------------------

new :: AllRelations n
new = AllRelations (EquivClass.new "Field") Boolean.new UInt.new

assignF :: (GaloisField n, Integral n) => Ref -> n -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
assignF var val = updateRelationsF $ EquivClass.assign var val

assignB :: RefB -> Bool -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
assignB ref val = updateRelationsB $ Boolean.assign ref val

assignU :: (GaloisField n, Integral n) => RefU -> n -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
assignU ref val = updateRelationsU $ UInt.assign ref val

relate :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
relate var1 slope var2 intercept = updateRelationsF $ EquivClass.relate var1 (LinRel slope intercept) var2

relateB :: GaloisField n => RefB -> (Bool, RefB) -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
relateB refA (polarity, refB) = updateRelationsB (Boolean.relate refA polarity refB)

-- var = slope * var2 + intercept
relateRefs :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
relateRefs x slope y intercept xs =
  case (x, y, slope, intercept) of
    (B refB, _, 0, value) -> assignB refB (value == 1) xs
    (U refU, _, 0, value) -> assignU refU value xs
    (_, _, 0, value) -> assignF x value xs
    (B refA, B refB, 1, 0) -> relateB refA (True, refB) xs
    (U refA, U refB, 1, 0) -> assertEqualU refA refB xs
    (B refA, B refB, -1, 1) -> relateB refA (False, refB) xs
    (F refA, F refB, _, _) -> relate (F refA) slope (F refB) intercept xs
    (F refA, B refB, _, _) ->
      composeLookup
        xs
        (F refA)
        (B refB)
        slope
        intercept
        (EquivClass.lookup (F refA) (relationsF xs))
        (fromBooleanLookup (EquivClass.lookup refB (relationsB xs)))
    (F refA, U refB, _, _) ->
      composeLookup
        xs
        (F refA)
        (U refB)
        slope
        intercept
        (EquivClass.lookup (F refA) (relationsF xs))
        (fromUIntLookup (EquivClass.lookup refB (relationsU xs)))
    (B refA, F refB, _, _) ->
      composeLookup
        xs
        (F refB)
        (B refA)
        (recip slope)
        (-intercept / slope)
        (EquivClass.lookup (F refB) (relationsF xs))
        (fromBooleanLookup (EquivClass.lookup refA (relationsB xs)))
    (B refA, B refB, _, _) ->
      composeLookup
        xs
        (B refA)
        (B refB)
        slope
        intercept
        (fromBooleanLookup (EquivClass.lookup refA (relationsB xs)))
        (fromBooleanLookup (EquivClass.lookup refB (relationsB xs)))
    (B refA, U refB, _, _) ->
      composeLookup
        xs
        (B refA)
        (U refB)
        slope
        intercept
        (fromBooleanLookup (EquivClass.lookup refA (relationsB xs)))
        (fromUIntLookup (EquivClass.lookup refB (relationsU xs)))
    (U refA, F refB, _, _) ->
      composeLookup
        xs
        (F refB)
        (U refA)
        (recip slope)
        (-intercept / slope)
        (EquivClass.lookup (F refB) (relationsF xs))
        (fromUIntLookup (EquivClass.lookup refA (relationsU xs)))
    (U refA, B refB, _, _) ->
      composeLookup
        xs
        (U refA)
        (B refB)
        (recip slope)
        (-intercept / slope)
        (fromBooleanLookup (EquivClass.lookup refB (relationsB xs)))
        (fromUIntLookup (EquivClass.lookup refA (relationsU xs)))
    (U refA, U refB, _, _) ->
      composeLookup
        xs
        (U refA)
        (U refB)
        slope
        intercept
        (fromUIntLookup (EquivClass.lookup refA (relationsU xs)))
        (fromUIntLookup (EquivClass.lookup refB (relationsU xs)))

assertEqual :: (GaloisField n, Integral n) => Ref -> Ref -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
assertEqual var1 var2 = relate var1 1 var2 0

assertEqualU :: (GaloisField n, Integral n) => RefU -> RefU -> AllRelations n -> EquivClass.M (Error n) (AllRelations n)
assertEqualU var1 var2 = updateRelationsU $ UInt.assertEqual var1 var2

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> AllRelations n -> Maybe (n, n)
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 (relationsF xs) of
  Nothing -> Nothing
  Just (LinRel a b) -> Just (a, b)

toInt :: (Ref -> Bool) -> AllRelations n -> Map Ref (Either (n, Ref, n) n)
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

size :: AllRelations n -> Int
size = Map.size . EquivClass.toMap . relationsF

isValid :: (GaloisField n, Integral n) => AllRelations n -> Bool
isValid = EquivClass.isValid . relationsF

--------------------------------------------------------------------------------

-- \| Result of looking up a variable in the AllRelations
data Lookup n = Root | Value n | ChildOf n Ref n
  deriving (Eq, Show)

lookup :: GaloisField n => Ref -> AllRelations n -> Lookup n
lookup var xs = toLookup $ lookup' var xs

toLookup :: EquivClass.VarStatus Ref n (n, n) -> Lookup n
toLookup (EquivClass.IsRoot _) = Root
toLookup (EquivClass.IsConstant val) = Value val
toLookup (EquivClass.IsChildOf parent (slope, intercept)) = ChildOf slope parent intercept

lookup' :: GaloisField n => Ref -> AllRelations n -> EquivClass.VarStatus Ref n (n, n)
lookup' (U var) xs = fromLinRel $ fromUIntLookup (EquivClass.lookup var (relationsU xs))
lookup' (B var) xs = fromLinRel $ fromBooleanLookup $ EquivClass.lookup var (relationsB xs)
lookup' (F var) xs = fromLinRel $ EquivClass.lookup (F var) (relationsF xs)

fromLinRel :: EquivClass.VarStatus Ref n (LinRel n) -> EquivClass.VarStatus Ref n (n, n)
fromLinRel (EquivClass.IsRoot children) = EquivClass.IsRoot $ fmap (\(LinRel a b) -> (a, b)) children
fromLinRel (EquivClass.IsConstant val) = EquivClass.IsConstant val
fromLinRel (EquivClass.IsChildOf parent (LinRel a b)) = EquivClass.IsChildOf parent (a, b)

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

fromUIntLookup :: GaloisField n => EquivClass.VarStatus RefU n UInt.Rotation -> EquivClass.VarStatus Ref n (LinRel n)
fromUIntLookup (EquivClass.IsRoot children) =
  EquivClass.IsRoot $
    Map.mapKeys U $
      Map.map
        ( \case
            UInt.Rotation _ 0 -> LinRel 1 0
            _ -> error "[ panic ]: Don't know how to relate a Field to a rotated UInt"
        )
        children
fromUIntLookup (EquivClass.IsConstant n) = EquivClass.IsConstant n
fromUIntLookup (EquivClass.IsChildOf parent (UInt.Rotation _ 0)) = EquivClass.IsChildOf (U parent) (LinRel 1 0)
fromUIntLookup (EquivClass.IsChildOf _ _) = error "[ panic ]: Don't know how to relate a Field to a rotated UInt"

composeLookup :: (GaloisField n, Integral n) => AllRelations n -> Ref -> Ref -> n -> n -> EquivClass.VarStatus Ref n (LinRel n) -> EquivClass.VarStatus Ref n (LinRel n) -> EquivClass.M (Error n) (AllRelations n)
composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
  (EquivClass.IsRoot _, EquivClass.IsRoot _) ->
    -- rootA = slope * rootB + intercept
    relate refA slope refB intercept xs
  (EquivClass.IsRoot _, EquivClass.IsConstant n) ->
    -- rootA = slope * n + intercept
    assignF refA (slope * n + intercept) xs
  (EquivClass.IsRoot _, EquivClass.IsChildOf rootB (LinRel slopeB interceptB)) ->
    -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
    -- =>
    -- rootA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
    relate refA (slope * slopeB) rootB (slope * interceptB + intercept) xs
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
    relate rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
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
    relate rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs

exportBooleanRelations :: AllRelations n -> Boolean.BooleanRelations
exportBooleanRelations = relationsB

exportUIntRelations :: AllRelations n -> UInt.UIntRelations n
exportUIntRelations = relationsU
