{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Limb
  ( LimbRelations,
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
import Keelung.Data.Limb (Limb (..))
import Prelude hiding (lookup)

type LimbRelations =
  EquivClass.EquivClass
    Limb
    Integer -- constants can be represented as integers
    () -- only allowing Limbs of the same width to be related (as equal) at the moment

new :: LimbRelations
new = EquivClass.new "Limb Equivalence"

-- | Assigning a constant value to a limb
assign :: Limb -> Integer -> LimbRelations -> EquivClass.M (Error n) LimbRelations
assign var val xs = mapError $ EquivClass.assign var val xs

-- | Relate two limbs (that has the same width)
relate :: Limb -> Limb -> LimbRelations -> EquivClass.M (Error n) LimbRelations
relate var1 var2 xs =
  if lmbWidth var1 /= lmbWidth var2
    then pure xs
    else mapError $ EquivClass.relate var1 () var2 xs

-- | Examine the relation between two limbs
relationBetween :: Limb -> Limb -> LimbRelations -> Bool
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 xs of
  Nothing -> False
  Just () -> True

-- | Given a predicate, convert the relations to a mapping of Limbs to either some other Limb or a constant value
toMap :: (Limb -> Bool) -> LimbRelations -> Map Limb (Either Limb Integer)
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

size :: LimbRelations -> Int
size = Map.size . EquivClass.toMap

isValid :: LimbRelations -> Bool
isValid = EquivClass.isValid
