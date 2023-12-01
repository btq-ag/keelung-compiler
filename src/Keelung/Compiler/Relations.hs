{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations
  ( Relations,
    new,
    assignR,
    assignB,
    assignL,
    assignU,
    relateB,
    relateL,
    relateU,
    relateR,
    relationBetween,
    toInt,
    size,
    lookup,
    Ref.Lookup (..),
    exportLimbRelations,
    exportUIntRelations,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Limb qualified as LimbRelations
import Keelung.Compiler.Relations.Reference qualified as Ref
import Keelung.Compiler.Relations.UInt qualified as UInt
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Prelude hiding (lookup)

data Relations n = Relations
  { relationsR :: Ref.RefRelations n,
    relationsL :: LimbRelations.LimbRelations,
    relationsU :: UInt.UIntRelations
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (Relations n) where
  show (Relations f l u) =
    (if EquivClass.size f == 0 then "" else show f)
      <> (if EquivClass.size l == 0 then "" else show l)
      <> (if EquivClass.size u == 0 then "" else show u)

updateRelationsR ::
  (Ref.RefRelations n -> EquivClass.M (Error n) (Ref.RefRelations n)) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsR f xs = do
  relations <- f (relationsR xs)
  return $ xs {relationsR = relations}

updateRelationsL ::
  (LimbRelations.LimbRelations -> EquivClass.M (Error n) LimbRelations.LimbRelations) ->
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
new = Relations Ref.new LimbRelations.new UInt.new

assignR :: (GaloisField n, Integral n) => Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
assignR var val = updateRelationsR $ Ref.assignF var val

assignB :: (GaloisField n, Integral n) => RefB -> Bool -> Relations n -> EquivClass.M (Error n) (Relations n)
assignB ref val = assignR (B ref) (if val then 1 else 0)

-- | Lookup the RefU of the Limb first before assigning value to it
assignL :: (GaloisField n, Integral n) => Limb -> Integer -> Relations n -> EquivClass.M (Error n) (Relations n)
assignL var val relations = case UInt.lookupRefU (exportUIntRelations relations) (Limb.lmbRef var) of
  Left rootVar -> updateRelationsL (LimbRelations.assign (var {Limb.lmbRef = rootVar}) val) relations
  Right rootVal ->
    -- the parent of this limb turned out to be a constant
    if toInteger rootVal == val
      then return relations -- do nothing
      else throwError $ ConflictingValuesU (toInteger rootVal) val

assignU :: (GaloisField n, Integral n) => RefU -> Integer -> Relations n -> EquivClass.M (Error n) (Relations n)
assignU var val = updateRelationsU $ UInt.assignRefU var val

relateB :: (GaloisField n, Integral n) => GaloisField n => RefB -> (Bool, RefB) -> Relations n -> EquivClass.M (Error n) (Relations n)
relateB refA (polarity, refB) = updateRelationsR (Ref.relateB refA (polarity, refB))

-- | Lookup the relation between the RefUs of the Limbs first before relating the Limbs
relateL :: (GaloisField n, Integral n) => Limb -> Limb -> Relations n -> EquivClass.M (Error n) (Relations n)
relateL var1 var2 relations = case EquivClass.relationBetween (UInt.Ref (Limb.lmbRef var1)) (UInt.Ref (Limb.lmbRef var2)) (exportUIntRelations relations) of
  Nothing ->
    -- no relations between the RefUs of the Limbs, so we relate the Limbs instead
    updateRelationsL (LimbRelations.relate var1 var2) relations
  Just UInt.Equal ->
    -- the RefUs of the Limbs are equal, so we do nothing (no need to relate the Limbs)
    return relations

relateU :: (GaloisField n, Integral n) => RefU -> RefU -> Relations n -> EquivClass.M (Error n) (Relations n)
relateU var1 var2 = updateRelationsU $ UInt.relateRefU var1 var2

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
relateR x slope y intercept xs = updateRelationsR (Ref.relateR (relationsU xs) x slope y intercept) xs

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> Relations n -> Maybe (n, n)
relationBetween var1 var2 = Ref.relationBetween var1 var2 . relationsR

toInt :: (Ref -> Bool) -> Relations n -> Map Ref (Either (n, Ref, n) n)
toInt shouldBeKept = Ref.toInt shouldBeKept . relationsR

size :: Relations n -> Int
size (Relations f l u) = EquivClass.size f + LimbRelations.size l + UInt.size u

--------------------------------------------------------------------------------

lookup :: GaloisField n => Ref -> Relations n -> Ref.Lookup n
lookup var xs = Ref.lookup (relationsU xs) var (relationsR xs)

--------------------------------------------------------------------------------

exportLimbRelations :: Relations n -> LimbRelations.LimbRelations
exportLimbRelations = relationsL

exportUIntRelations :: Relations n -> UInt.UIntRelations
exportUIntRelations = relationsU