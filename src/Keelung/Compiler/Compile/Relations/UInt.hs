{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile.Relations.UInt
  ( UIntRelations,
    new,
    assign,
    relate,
    relationBetween,
    toMap,
    size,
    isValid,
    lookup,
    lookup',
    assertEqual,
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
import Keelung.Compiler.Compile.Relations.Relations qualified as Relations
import Keelung.Compiler.Constraint
import Keelung.Interpreter.Arithmetics qualified as Arith
import Keelung.Syntax (HasWidth (widthOf), Width)
import Prelude hiding (lookup)

type UIntRelations n = Relations.Relations RefU n Rotation

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

instance Relations.IsRelation Rotation where
  relationToString (var, Rotation w n) =
    let n' = (-n) `mod` w
     in if n' == 0
          then var
          else var <> " <<< " <> show n'
  relationToString (var, NoRotation) = var

  invertRel (Rotation w n) = Rotation w ((-n) `mod` w)
  invertRel NoRotation = NoRotation

instance (GaloisField n, Integral n) => Relations.ExecRelation n Rotation where
  execRel (Rotation w n) value = Arith.bitWiseRotateL w n value
  execRel NoRotation value = value

rotationAmount :: Rotation -> Int
rotationAmount (Rotation _ n) = n
rotationAmount NoRotation = 0

mapError :: Relations.M (n, n) a -> Relations.M (Error n) a
mapError = Relations.mapError (uncurry ConflictingValuesU)

new :: UIntRelations n
new = Relations.new "UInt"

assign :: (GaloisField n, Integral n) => RefU -> n -> UIntRelations n -> Relations.M (Error n) (UIntRelations n)
assign var val xs = mapError $ Relations.assign var val xs

relate :: (GaloisField n, Integral n) => RefU -> Int -> RefU -> UIntRelations n -> Relations.M (Error n) (UIntRelations n)
relate var1 0 var2 xs = mapError $ Relations.relate var1 NoRotation var2 xs
relate var1 rotation var2 xs = mapError $ Relations.relate var1 (Rotation (widthOf var1) rotation) var2 xs

assertEqual :: (GaloisField n, Integral n) => RefU -> RefU -> UIntRelations n -> Relations.M (Error n) (UIntRelations n)
assertEqual var1 = relate var1 0

relationBetween :: RefU -> RefU -> UIntRelations n -> Maybe Int
relationBetween var1 var2 xs = case Relations.relationBetween var1 var2 xs of
  Nothing -> Nothing
  Just rotation -> Just (rotationAmount rotation)

toMap :: (RefU -> Bool) -> UIntRelations n -> Map RefU (Either (Int, RefU) n)
toMap shouldBeKept xs = Map.mapMaybeWithKey convert $ Relations.toMap xs
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          Relations.IsConstant val -> Just (Right val)
          Relations.IsRoot _ -> Nothing
          Relations.IsChildOf parent rotation ->
            if shouldBeKept parent
              then Just $ Left (rotationAmount rotation, parent)
              else Nothing
        else Nothing

size :: UIntRelations n -> Int
size = Map.size . Relations.toMap

isValid :: UIntRelations n -> Bool
isValid = Relations.isValid

-- \| Result of looking up a variable in the BooleanRelations
data Lookup n = Root | Value n | ChildOf Int RefU
  deriving (Eq, Show)

lookup :: RefU -> UIntRelations n -> Lookup n
lookup var xs = case Relations.lookup var xs of
  Relations.IsRoot _ -> Root
  Relations.IsConstant val -> Value val
  Relations.IsChildOf parent rotation -> ChildOf (rotationAmount rotation) parent

lookup' :: RefU -> UIntRelations n -> Relations.VarStatus RefU n Int
lookup' var xs = case Relations.lookup var xs of
  Relations.IsRoot children -> Relations.IsRoot $ fmap rotationAmount children
  Relations.IsConstant val -> Relations.IsConstant val
  Relations.IsChildOf parent rotation -> Relations.IsChildOf parent (rotationAmount rotation)
