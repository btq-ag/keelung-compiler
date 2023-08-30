{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.UInt
  ( UIntRelations,
    new,
    assign,
    relate,
    relationBetween,
    toMap,
    size,
    isValid,
  )
where

-- import Control.DeepSeq (NFData)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
-- import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Data.Reference
import Prelude hiding (lookup)

type UIntRelations =
  EquivClass.EquivClass
    RefL
    Integer -- constants can be represented as integers
    () -- only allowing RefLs of the same width to be related (as equal) at the moment

new :: UIntRelations
new = EquivClass.new "UInt (RefL Equivalence)"

instance EquivClass.IsRelation () where
  relationToString (var, ()) = var
  invertRel () = Just ()

instance EquivClass.ExecRelation Integer () where
  execRel () value = value

-- | Assigning a constant value to a limb
assign :: RefL -> Integer -> UIntRelations -> EquivClass.M (Error n) UIntRelations
assign var val xs = mapError $ EquivClass.assign var val xs

-- | Relate two limbs (that has the same width)
relate :: RefL -> RefL -> UIntRelations -> EquivClass.M (Error n) UIntRelations
relate var1 var2 xs =
  if lmbWidth (refLLimb var1) /= lmbWidth (refLLimb var2) || refLPowerOffset var1 /= refLPowerOffset var2
    then pure xs
    else mapError $ EquivClass.relate var1 () var2 xs

-- | Examine the relation between two limbs
relationBetween :: RefL -> RefL -> UIntRelations -> Bool
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 xs of
  Nothing -> False
  Just () -> True

-- | Given a predicate, convert the relations to a mapping of Limbs to either some other Limb or a constant value
toMap :: (RefL -> Bool) -> UIntRelations -> Map RefL (Either RefL Integer)
toMap shouldBeKept xs = Map.mapMaybeWithKey convert $ EquivClass.toMap xs
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          EquivClass.IsConstant val -> Just (Right val)
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf parent () ->
            if shouldBeKept parent
              then Just $ Left parent
              else Nothing
        else Nothing

-- | Helper function for lifting errors
mapError :: EquivClass.M (Integer, Integer) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesU)

size :: UIntRelations -> Int
size = Map.size . EquivClass.toMap

isValid :: UIntRelations -> Bool
isValid = EquivClass.isValid