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
    assignS,
    relateB,
    relateL,
    relateU,
    relateR,
    relateS,
    relationBetween,
    toInt,
    size,
    lookup,
    Ref.Lookup (..),
    exportLimbRelations,
    exportUIntRelations,
    exportSliceRelations,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import GHC.Generics (Generic)
import Keelung (widthOf)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Options
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Limb qualified as LimbRelations
import Keelung.Compiler.Relations.Reference qualified as Ref
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Compiler.Relations.UInt qualified as UInt
import Keelung.Data.Limb (Limb)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Prelude hiding (lookup)
import Keelung.Data.Slice (Slice)

data Relations n = Relations
  { relationsR :: Ref.RefRelations n,
    relationsL :: LimbRelations.LimbRelations,
    relationsU :: UInt.UIntRelations,
    relationsS :: SliceRelations.SliceRelations,
    relationsOptions :: Options
  }
  deriving (Eq, Generic, NFData)

instance (GaloisField n, Integral n) => Show (Relations n) where
  show (Relations f l u s options) =
    (if EquivClass.size f == 0 then "" else show f)
      <> ( if optUseUIntUnionFind options
             then (if SliceRelations.size s == 0 then "" else show u)
             else (if EquivClass.size l == 0 then "" else show l) <> (if EquivClass.size u == 0 then "" else show u)
         )

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

updateRelationsS ::
  (SliceRelations.SliceRelations -> EquivClass.M (Error n) SliceRelations.SliceRelations) ->
  Relations n ->
  EquivClass.M (Error n) (Relations n)
updateRelationsS f xs = do
  relations <- f (relationsS xs)
  return $ xs {relationsS = relations}

--------------------------------------------------------------------------------

new :: Options -> Relations n
new = Relations Ref.new LimbRelations.new UInt.new SliceRelations.new

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

assignS :: (GaloisField n, Integral n) => Limb -> Integer -> Relations n -> EquivClass.M (Error n) (Relations n)
assignS limb int = updateRelationsS $ return . SliceRelations.assign (Slice.fromLimb limb) (U.new (widthOf limb) int)

relateB :: (GaloisField n, Integral n) => (GaloisField n) => RefB -> (Bool, RefB) -> Relations n -> EquivClass.M (Error n) (Relations n)
relateB refA (polarity, refB) = updateRelationsR (Ref.relateB refA (polarity, refB))

relateL :: (GaloisField n, Integral n) => Limb -> Limb -> Relations n -> EquivClass.M (Error n) (Relations n)
relateL limb1 limb2 relations =
  let result1 = lookupLimb limb1 relations
      result2 = lookupLimb limb2 relations
   in case (result1, result2) of
        (Left limb1', Left limb2') -> case EquivClass.relationBetween (UInt.Ref (Limb.lmbRef limb1)) (UInt.Ref (Limb.lmbRef limb2)) (exportUIntRelations relations) of
          Nothing ->
            -- no relations between the RefUs of the Limbs, so we relate the Limbs instead
            updateRelationsL (LimbRelations.relate limb1' limb2') relations
          Just UInt.Equal ->
            -- the RefUs of the Limbs are equal, so we do nothing (no need to relate the Limbs)
            return relations
        (Left limb1', Right val2') -> updateRelationsL (LimbRelations.assign limb1' (toInteger val2')) relations
        (Right val1', Left limb2') -> updateRelationsL (LimbRelations.assign limb2' (toInteger val1')) relations
        (Right val1', Right val2') -> if val1' == val2' then return relations else throwError $ ConflictingValuesU (toInteger val1') (toInteger val2')

lookupLimb :: (GaloisField n, Integral n) => Limb -> Relations n -> Either Limb U
lookupLimb limb relations = case UInt.lookupRefU (exportUIntRelations relations) (Limb.lmbRef limb) of
  Left rootVar -> Left (limb {Limb.lmbRef = rootVar}) -- replace the RefU of the Limb with the root of that RefU
  Right rootVal -> Right (U.slice rootVal (Limb.lmbOffset limb) (Limb.lmbWidth limb)) -- the parent of this limb turned out to be a constant

relateU :: (GaloisField n, Integral n) => RefU -> RefU -> Relations n -> EquivClass.M (Error n) (Relations n)
relateU var1 var2 = updateRelationsU $ UInt.relateRefU var1 var2

-- var = slope * var2 + intercept
relateR :: (GaloisField n, Integral n) => Ref -> n -> Ref -> n -> Relations n -> EquivClass.M (Error n) (Relations n)
relateR x slope y intercept xs = updateRelationsR (Ref.relateR (relationsOptions xs) (relationsU xs) x slope y intercept) xs

relateS :: (GaloisField n, Integral n) => Slice -> Slice -> Relations n -> EquivClass.M (Error n) (Relations n)
relateS slice1 slice2 = updateRelationsS $ return . SliceRelations.relate slice1 slice2

relationBetween :: (GaloisField n, Integral n) => Ref -> Ref -> Relations n -> Maybe (n, n)
relationBetween var1 var2 = Ref.relationBetween var1 var2 . relationsR

toInt :: (Ref -> Bool) -> Relations n -> Map Ref (Either (n, Ref, n) n)
toInt shouldBeKept = Ref.toInt shouldBeKept . relationsR

size :: Relations n -> Int
size (Relations f l u s options) = EquivClass.size f + LimbRelations.size l + UInt.size u + if optUseUIntUnionFind options then SliceRelations.size s else 0

--------------------------------------------------------------------------------

lookup :: (GaloisField n) => Ref -> Relations n -> Ref.Lookup n
lookup var xs = Ref.lookup (relationsOptions xs) (relationsU xs) var (relationsR xs)

--------------------------------------------------------------------------------

exportLimbRelations :: Relations n -> LimbRelations.LimbRelations
exportLimbRelations = relationsL

exportUIntRelations :: Relations n -> UInt.UIntRelations
exportUIntRelations = relationsU

exportSliceRelations :: Relations n -> SliceRelations.SliceRelations
exportSliceRelations = relationsS