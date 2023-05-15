{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
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
    assertEqual,
    Rotation (..)
  )
where

import Control.DeepSeq (NFData)
import Data.Field.Galois (GaloisField)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Constraint
import Keelung.Interpreter.Arithmetics qualified as Arith
import Keelung.Syntax (HasWidth (widthOf), Width)
import Prelude hiding (lookup)

type UIntRelations n = EquivClass.EquivClass RefU n Rotation

data Rotation
  = Rotation Width Int
  | NoRotation
  deriving (Eq, NFData, Generic)

instance Show Rotation where
  show (Rotation _ n) = show n
  show NoRotation = show "0"

instance Semigroup Rotation where
  Rotation w a <> Rotation _ b = Rotation w ((a + b) `mod` w)
  NoRotation <> x = x
  x <> NoRotation = x

instance Monoid Rotation where
  mempty = NoRotation

instance EquivClass.IsRelation Rotation where
  relationToString (var, Rotation w n) =
    let n' = (-n) `mod` w
     in if n' == 0
          then var
          else var <> " <<< " <> show n'
  relationToString (var, NoRotation) = var

  invertRel (Rotation w n) = Rotation w ((-n) `mod` w)
  invertRel NoRotation = NoRotation

instance (GaloisField n, Integral n) => EquivClass.ExecRelation n Rotation where
  execRel (Rotation w n) value = Arith.bitWiseRotateL w n value
  execRel NoRotation value = value

rotationAmount :: Rotation -> Int
rotationAmount (Rotation _ n) = n
rotationAmount NoRotation = 0

mapError :: EquivClass.M (n, n) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesU)

new :: UIntRelations n
new = EquivClass.new "UInt"

assign :: (GaloisField n, Integral n) => RefU -> n -> UIntRelations n -> EquivClass.M (Error n) (UIntRelations n)
assign var val xs = mapError $ EquivClass.assign var val xs

relate :: (GaloisField n, Integral n) => RefU -> Int -> RefU -> UIntRelations n -> EquivClass.M (Error n) (UIntRelations n)
relate var1 0 var2 xs = mapError $ EquivClass.relate var1 NoRotation var2 xs
relate var1 rotation var2 xs = mapError $ EquivClass.relate var1 (Rotation (widthOf var1) rotation) var2 xs

assertEqual :: (GaloisField n, Integral n) => RefU -> RefU -> UIntRelations n -> EquivClass.M (Error n) (UIntRelations n)
assertEqual var1 = relate var1 0

relationBetween :: RefU -> RefU -> UIntRelations n -> Maybe Int
relationBetween var1 var2 xs = case EquivClass.relationBetween var1 var2 xs of
  Nothing -> Nothing
  Just rotation -> Just (rotationAmount rotation)

toMap :: (RefU -> Bool) -> UIntRelations n -> Map RefU (Either (Int, RefU) n)
toMap shouldBeKept xs = Map.mapMaybeWithKey convert $ EquivClass.toMap xs
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          EquivClass.IsConstant val -> Just (Right val)
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf parent rotation ->
            if shouldBeKept parent
              then Just $ Left (rotationAmount rotation, parent)
              else Nothing
        else Nothing

size :: UIntRelations n -> Int
size = Map.size . EquivClass.toMap

isValid :: UIntRelations n -> Bool
isValid = EquivClass.isValid

-- -- \| Result of looking up a variable in the BooleanRelations
-- data Lookup n = Root | Value n | ChildOf Int RefU
--   deriving (Eq, Show)

-- lookup :: RefU -> UIntRelations n -> Lookup n
-- lookup var xs = case EquivClass.lookup var xs of
--   EquivClass.IsRoot _ -> Root
--   EquivClass.IsConstant val -> Value val
--   EquivClass.IsChildOf parent rotation -> ChildOf (rotationAmount rotation) parent

-- lookup' :: RefU -> UIntRelations n -> EquivClass.VarStatus RefU n Int
-- lookup' var xs = case EquivClass.lookup var xs of
--   EquivClass.IsRoot children -> EquivClass.IsRoot $ fmap rotationAmount children
--   EquivClass.IsConstant val -> EquivClass.IsConstant val
--   EquivClass.IsChildOf parent rotation -> EquivClass.IsChildOf parent (rotationAmount rotation)
