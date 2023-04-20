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
    relateRefs,
    assertEqual,
    assertEqualU,
    relationBetween,
    toIntMap,
    size,
    isValid,
    lookup,
    lookup',
    Lookup (..),
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.Boolean qualified as Relations.Boolean
import Keelung.Compiler.Compile.Relations.Relations qualified as Relations
import Keelung.Compiler.Compile.Relations.UInt qualified as Relations.UInt
import Keelung.Compiler.Constraint
import Prelude hiding (lookup)

type FieldRelations n = Relations.Relations Ref n (LinRel n)

data AllRelations n = AllRelations
  { relationsF :: FieldRelations n,
    relationsB :: Relations.Boolean.BooleanRelations,
    relationsU :: Relations.UInt.UIntRelations n
  }

mapError :: Relations.M (n, n) a -> Relations.M (Error n) a
mapError = Relations.mapError (uncurry ConflictingValuesU)

updateRelationsF ::
  (FieldRelations n -> Relations.M (n, n) (FieldRelations n)) ->
  AllRelations n ->
  Relations.M (Error n) (AllRelations n)
updateRelationsF f xs = mapError $ do
  relations <- f (relationsF xs)
  return $ xs {relationsF = relations}

updateRelationsB ::
  (Relations.Boolean.BooleanRelations -> Relations.M (Error n) Relations.Boolean.BooleanRelations) ->
  AllRelations n ->
  Relations.M (Error n) (AllRelations n)
updateRelationsB f xs = do
  relations <- f (relationsB xs)
  return $ xs {relationsB = relations}

updateRelationsU ::
  (Relations.UInt.UIntRelations n -> Relations.M (Error n) (Relations.UInt.UIntRelations n)) ->
  AllRelations n ->
  Relations.M (Error n) (AllRelations n)
updateRelationsU f xs = do
  relations <- f (relationsU xs)
  return $ xs {relationsU = relations}

--------------------------------------------------------------------------------

new :: AllRelations n
new = AllRelations Relations.new Relations.Boolean.new Relations.UInt.new

assignF :: (GaloisField n, Integral n) => Ref -> n -> AllRelations n -> Relations.M (Error n) (AllRelations n)
assignF var val = updateRelationsF $ Relations.assign var val

assignB :: RefB -> Bool -> AllRelations n -> Relations.M (Error n) (AllRelations n)
assignB ref val = updateRelationsB $ Relations.Boolean.assign ref val

assignU :: (GaloisField n, Integral n) => RefU -> n -> AllRelations n -> Relations.M (Error n) (AllRelations n)
assignU ref val = updateRelationsU $ Relations.UInt.assign ref val

relate :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> AllRelations n -> Relations.M (Error n) (AllRelations n)
relate var1 slope var2 intercept = updateRelationsF $ Relations.relate var1 (LinRel slope intercept) var2

relateB :: RefB -> (Bool, RefB) -> AllRelations n -> Relations.M (Error n) (AllRelations n)
relateB refA (polarity, refB) = updateRelationsB $ Relations.Boolean.relate refA polarity refB

relateRefs :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> AllRelations n -> Relations.M (Error n) (AllRelations n)
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
        (Relations.lookup (F refA) (relationsF xs))
        (fromBooleanLookup (Relations.Boolean.lookup' refB (relationsB xs)))
    (F refA, U refB, _, _) ->
      composeLookup
        xs
        (F refA)
        (U refB)
        slope
        intercept
        (Relations.lookup (F refA) (relationsF xs))
        (fromUIntLookup (Relations.UInt.lookup' refB (relationsU xs)))
    (B refA, F refB, _, _) -> 
      composeLookup
        xs
        (F refB)
        (B refA)
        (recip slope)
        (-intercept / slope)
        (Relations.lookup (F refB) (relationsF xs))
        (fromBooleanLookup (Relations.Boolean.lookup' refA (relationsB xs)))
    (B refA, B refB, _, _) -> 
      composeLookup
        xs
        (B refA)
        (B refB)
        slope
        intercept
        (fromBooleanLookup (Relations.Boolean.lookup' refA (relationsB xs)))
        (fromBooleanLookup (Relations.Boolean.lookup' refB (relationsB xs)))
    (B refA, U refB, _, _) -> 
      composeLookup
        xs
        (B refA)
        (U refB)
        slope
        intercept
        (fromBooleanLookup (Relations.Boolean.lookup' refA (relationsB xs)))
        (fromUIntLookup (Relations.UInt.lookup' refB (relationsU xs)))
    (U refA, F refB, _, _) -> 
      composeLookup
        xs
        (F refB)
        (U refA)
        (recip slope)
        (-intercept / slope)
        (Relations.lookup (F refB) (relationsF xs))
        (fromUIntLookup (Relations.UInt.lookup' refA (relationsU xs)))
    (U refA, B refB, _, _) -> 
      composeLookup
        xs
        (U refA)
        (B refB)
        (recip slope)
        (-intercept / slope)
        (fromBooleanLookup (Relations.Boolean.lookup' refB (relationsB xs)))
        (fromUIntLookup (Relations.UInt.lookup' refA (relationsU xs)))
    (U refA, U refB, _, _) -> 
      composeLookup
        xs
        (U refA)
        (U refB)
        slope
        intercept
        (fromUIntLookup (Relations.UInt.lookup' refA (relationsU xs)))
        (fromUIntLookup (Relations.UInt.lookup' refB (relationsU xs)))

assertEqual :: (GaloisField n, Integral n) => Ref -> Ref -> AllRelations n -> Relations.M (Error n) (AllRelations n)
assertEqual var1 var2 = relate var1 1 var2 0

assertEqualU :: (GaloisField n, Integral n) => RefU -> RefU -> AllRelations n -> Relations.M (Error n) (AllRelations n)
assertEqualU var1 var2 = updateRelationsU $ Relations.UInt.assertEqual var1 var2

relationBetween :: (Eq n, Fractional n, Show n) => Ref -> Ref -> AllRelations n -> Maybe (n, n)
relationBetween var1 var2 xs = case Relations.relationBetween var1 var2 (relationsF xs) of
  Nothing -> Nothing
  Just (LinRel a b) -> Just (a, b)

toIntMap :: AllRelations n -> Map Ref (Either (n, Ref, n) n)
toIntMap xs = Map.mapMaybe convert $ Relations.toMap (relationsF xs)
  where
    convert (Relations.IsConstant val) = Just (Right val)
    convert (Relations.IsRoot _) = Nothing
    convert (Relations.IsChildOf parent (LinRel slope intercept)) = Just $ Left (slope, parent, intercept)

size :: AllRelations n -> Int
size = Map.size . Relations.toMap . relationsF

isValid :: (Eq n, Fractional n, Show n) => AllRelations n -> Bool
isValid = Relations.isValid . relationsF

--------------------------------------------------------------------------------

-- \| Result of looking up a variable in the AllRelations
data Lookup n = Root | Value n | ChildOf n Ref n
  deriving (Eq, Show)

lookup :: Ref -> AllRelations n -> Lookup n
lookup var xs = case Relations.lookup var (relationsF xs) of
  Relations.IsRoot _ -> Root
  Relations.IsConstant val -> Value val
  Relations.IsChildOf parent (LinRel slope intercept) -> ChildOf slope parent intercept

lookup' :: Ref -> AllRelations n -> Relations.VarStatus Ref n (n, n)
lookup' var xs = case Relations.lookup var (relationsF xs) of
  Relations.IsRoot children -> Relations.IsRoot $ fmap (\(LinRel a b) -> (a, b)) children
  Relations.IsConstant val -> Relations.IsConstant val
  Relations.IsChildOf parent (LinRel a b) -> Relations.IsChildOf parent (a, b)

--------------------------------------------------------------------------------

-- | Relation representing a linear function between two variables, i.e. x = ay + b
data LinRel n
  = LinRel
      n
      -- ^ slope
      n
      -- ^ intercept
  deriving (Eq, NFData, Generic)

instance Num n => Semigroup (LinRel n) where
  -- x = a1 * y + b1
  -- y = a2 * z + b2
  -- =>
  -- x = a1 * (a2 * z + b2) + b1
  --   = (a1 * a2) * z + (a1 * b2 + b1)
  LinRel a1 b1 <> LinRel a2 b2 = LinRel (a1 * a2) (a1 * b2 + b1)

instance Num n => Monoid (LinRel n) where
  mempty = LinRel 1 0

instance (Num n, Eq n, Show n, Fractional n) => Relations.IsRelation (LinRel n) where
  relationToString (var, LinRel a b) =
    let slope = case a of
          1 -> var
          (-1) -> "-" <> var
          _ -> show a <> var
        intercept = case b of
          0 -> ""
          _ -> " + " <> show b
     in slope <> intercept

  -- x = ay + b
  -- =>
  -- y = (x - b) / a
  invertRel (LinRel a b) = LinRel (recip a) (-b / a)

instance (GaloisField n, Integral n) => Relations.ExecRelation n (LinRel n) where
  execRel (LinRel a b) value = a * value + b

--------------------------------------------------------------------------------

fromBooleanLookup :: GaloisField n => Relations.VarStatus RefB Bool Bool -> Relations.VarStatus Ref n (LinRel n)
fromBooleanLookup (Relations.IsRoot children) = Relations.IsRoot $ Map.mapKeys B $ Map.map (\b -> if b then LinRel 1 0 else LinRel (-1) 1) children
fromBooleanLookup (Relations.IsConstant True) = Relations.IsConstant 1
fromBooleanLookup (Relations.IsConstant False) = Relations.IsConstant 0
fromBooleanLookup (Relations.IsChildOf parent True) = Relations.IsChildOf (B parent) (LinRel 1 0)
fromBooleanLookup (Relations.IsChildOf parent False) = Relations.IsChildOf (B parent) (LinRel (-1) 1)

fromUIntLookup :: GaloisField n => Relations.VarStatus RefU n Int -> Relations.VarStatus Ref n (LinRel n)
fromUIntLookup (Relations.IsRoot children) =
  Relations.IsRoot $
    Map.mapKeys U $
      Map.map
        ( \case
            0 -> LinRel 1 0
            _ -> error "[ panic ]: Don't know how to relate a Field to a rotated UInt"
        )
        children
fromUIntLookup (Relations.IsConstant n) = Relations.IsConstant n
fromUIntLookup (Relations.IsChildOf parent 0) = Relations.IsChildOf (U parent) (LinRel 1 0)
fromUIntLookup (Relations.IsChildOf _ _) = error "[ panic ]: Don't know how to relate a Field to a rotated UInt"

composeLookup :: (GaloisField n, Integral n) => AllRelations n -> Ref -> Ref -> n -> n -> Relations.VarStatus Ref n (LinRel n) -> Relations.VarStatus Ref n (LinRel n) -> Relations.M (Error n) (AllRelations n)
composeLookup xs refA refB slope intercept relationA relationB = case (relationA, relationB) of
  (Relations.IsRoot _, Relations.IsRoot _) ->
    -- rootA = slope * rootB + intercept
    relate refA slope refB intercept xs
  (Relations.IsRoot _, Relations.IsConstant n) ->
    -- rootA = slope * n + intercept
    assignF refA (slope * n + intercept) xs
  (Relations.IsRoot _, Relations.IsChildOf rootB (LinRel slopeB interceptB)) ->
    -- rootA = slope * refB + intercept && refB = slopeB * rootB + interceptB
    -- =>
    -- rootA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- rootA = slope * slopeB * rootB + slope * interceptB + intercept
    relate refA (slope * slopeB) rootB (slope * interceptB + intercept) xs
  (Relations.IsConstant n, Relations.IsRoot _) ->
    -- n = slope * rootB + intercept
    -- =>
    -- rootB = (n - intercept) / slope
    assignF refB ((n - intercept) / slope) xs
  (Relations.IsConstant n, Relations.IsConstant m) ->
    -- n = slope * m + intercept
    -- =>
    -- n - intercept = slope * m
    -- =>
    -- m = (n - intercept) / slope
    if m == (n - intercept) / slope
      then return xs
      else throwError $ ConflictingValuesF m ((n - intercept) / slope)
  (Relations.IsConstant n, Relations.IsChildOf rootB (LinRel slopeB interceptB)) ->
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
  (Relations.IsChildOf rootA (LinRel slopeA interceptA), Relations.IsRoot _) ->
    -- refA = slopeA * rootA + interceptA = slope * rootB + intercept
    -- =>
    -- rootA = (slope * rootB + intercept - interceptA) / slopeA
    relate rootA (slope / slopeA) refB ((intercept - interceptA) / slopeA) xs
  (Relations.IsChildOf rootA (LinRel slopeA interceptA), Relations.IsConstant n) ->
    -- refA = slopeA * rootA + interceptA = slope * n + intercept
    -- =>
    -- rootA = (slope * n + intercept - interceptA) / slopeA
    assignF rootA ((slope * n + intercept - interceptA) / slopeA) xs
  (Relations.IsChildOf rootA (LinRel slopeA interceptA), Relations.IsChildOf rootB (LinRel slopeB interceptB)) ->
    -- refA = slopeA * rootA + interceptA = slope * (slopeB * rootB + interceptB) + intercept
    -- =>
    -- slopeA * rootA = slope * slopeB * rootB + slope * interceptB + intercept - interceptA
    -- =>
    -- rootA = (slope * slopeB * rootB + slope * interceptB + intercept - interceptA) / slopeA
    relate rootA (slope * slopeB / slopeA) rootB ((slope * interceptB + intercept - interceptA) / slopeA) xs
