{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile.Relations.Field
  ( AllRelations,
    new,
    assignF,
    assignB,
    assignU,
    relate,
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

-- relate' :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> AllRelations n -> Except (Error n) (AllRelations n)
-- relate' x (slope, y, intercept) =
--   case (x, y, slope, intercept) of
--     (B refB, _, 0, value) -> Just <$> assignB refB (value == 1) xs
--     (U refU, _, 0, value) -> Just <$> assignU refU value xs
--     (_, _, 0, value) -> Just <$> assignF x value xs
--     (B refA, B refB, 1, 0) -> Just <$> relateB refA (True, refB) xs
--     (U refA, U refB, 1, 0) -> Just <$> assertEqualU refA refB xs
--     (B refA, B refB, -1, 1) -> Just <$> relateB refA (False, refB) xs
--     -- (F refA, F refB, _, _) -> relateRefFwithRefF refA (slope, refB, intercept) xs
--     (F _, F _, _, _) -> relateTwoRefs x (slope, y, intercept) xs
--     (F refA, B refB, _, _) -> relateRefFwithRefB'' refA (slope, refB, intercept) xs
--     (F refA, U refB, _, _) -> relateRefFWithRefU refA (slope, refB, intercept) xs
--     (B refA, F refB, _, _) -> relateRefFwithRefB'' refB (recip slope, refA, -intercept / slope) xs
--     (B refA, B refB, _, _) -> relateRefBWithRefB refA (slope, refB, intercept) xs
--     (B refA, U refB, _, _) -> relateRefBWithRefU refA (slope, refB, intercept) xs
--     (U refA, F refB, _, _) -> relateRefFWithRefU refB (recip slope, refA, -intercept / slope) xs
--     (U refA, B refB, _, _) -> relateRefBWithRefU refB (recip slope, refA, -intercept / slope) xs
--     (U refA, U refB, _, _) -> relateRefUWithRefU refA (slope, refB, intercept) xs
-- updateRelationsF $ Relations.relate (F var1) (LinRel slope intercept) (F var2)

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
