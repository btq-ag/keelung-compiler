{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}

module Keelung.Compiler.Relations.UInt
  ( UIntRelations,
    Element (..),
    Relation (..),
    new,
    assignRefU,
    relateRefU,
    lookupRefU,
    toConstraints,
    size,
    isValid,
  )
where

import Control.DeepSeq (NFData)
import Data.Foldable (Foldable (toList))
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import GHC.Generics (Generic)
import Keelung (HasWidth (widthOf))
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Util (Seniority (..))
import Keelung.Data.Constraint
import Keelung.Data.Reference
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Prelude hiding (lookup)

type UIntRelations =
  EquivClass.EquivClass
    Element -- relations on RefUs
    Integer -- constants can be represented as integers
    Relation -- only allowing RefU of the same width to be related (as equal) at the moment

--------------------------------------------------------------------------------

newtype Element = Ref RefU
  deriving (Eq, Ord, Generic, NFData)

instance Show Element where
  show (Ref ref) = show ref

instance Seniority Element where
  compareSeniority (Ref ref1) (Ref ref2) = compareSeniority ref1 ref2

--------------------------------------------------------------------------------

-- | Relation on RefUs
data Relation
  = Equal -- a = b
  deriving
    ( -- | ShiftLeft Int -- a = b << n
      Show, Eq,
      Generic,
      NFData
    )

instance Semigroup Relation where
  Equal <> r = r

-- r <> Equal = r
-- ShiftLeft n <> ShiftLeft m = ShiftLeft (n + m)

instance Monoid Relation where
  mempty = Equal

instance EquivClass.IsRelation Relation where
  -- Render a relation to some child as a string
  relationToString (var, Equal) = var -- " = " <> var

  -- relationToString (var, ShiftLeft n) = " = " <> var <> " << " <> show n

  -- Computes the inverse of a relation
  invertRel Equal = Just Equal

-- invertRel (ShiftLeft 0) = Just Equal
-- invertRel (ShiftLeft _) = Nothing

instance EquivClass.ExecRelation Integer Relation where
  execRel Equal val = val

-- execRel (ShiftLeft n) val = val `Data.Bits.shiftL` n

--------------------------------------------------------------------------------

new :: UIntRelations
new = EquivClass.new "UInt Relations"

-- | Assigning a constant value to a RefU
assignRefU :: RefU -> Integer -> UIntRelations -> EquivClass.M (Error n) UIntRelations
assignRefU var val xs = mapError $ EquivClass.assign (Ref var) val xs

-- | Relate two RefUs of the same width
relateRefU :: RefU -> RefU -> UIntRelations -> EquivClass.M (Error n) UIntRelations
relateRefU var1 var2 xs =
  if widthOf var1 /= widthOf var2
    then pure xs
    else mapError $ EquivClass.relate (Ref var1) Equal (Ref var2) xs

lookupRefU :: UIntRelations -> RefU -> Either RefU U
lookupRefU xs var = case EquivClass.lookup (Ref var) xs of
  EquivClass.IsConstant constant -> Right (U.new (widthOf var) constant)
  EquivClass.IsRoot _ -> Left var
  EquivClass.IsChildOf (Ref parent) Equal -> Left parent

-- | Convert the relations to specialized constraints
toConstraints :: (RefU -> Bool) -> UIntRelations -> Seq (Constraint n)
toConstraints refUShouldBeKept = Seq.fromList . toList . Map.mapMaybeWithKey convert . EquivClass.toMap
  where
    convert :: Element -> EquivClass.VarStatus Element Integer Relation -> Maybe (Constraint n)
    convert (Ref var) status
      | refUShouldBeKept var = case status of
          EquivClass.IsConstant val -> Just $ CRefUVal var val
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf (Ref parent) Equal ->
            if refUShouldBeKept parent
              then Just $ CRefUEq var parent
              else Nothing
      | otherwise = Nothing

-- | Helper function for lifting errors
mapError :: EquivClass.M (Integer, Integer) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesU)

size :: UIntRelations -> Int
size = Map.size . EquivClass.toMap

isValid :: UIntRelations -> Bool
isValid = EquivClass.isValid
