{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile.Relations.Boolean
  ( BooleanRelations,
    new,
    assign,
    relate,
    relationBetween,
    toMap,
    toMap2,
    size,
    isValid,
    lookup,
    lookup',
    Lookup (..),
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Except
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.Relations.Relations qualified as Relations
import Keelung.Compiler.Constraint
import Prelude hiding (lookup)

type BooleanRelations = Relations.Relations RefB Bool Polarity

newtype Polarity = Polarity {unPolarity :: Bool}
  deriving (Eq, Generic)

instance NFData Polarity

instance Show Polarity where
  show (Polarity True) = "P"
  show (Polarity False) = "N"

instance Semigroup Polarity where
  Polarity a <> Polarity b = Polarity (a == b)

instance Monoid Polarity where
  mempty = Polarity True

instance Relations.IsRelation Polarity where
  relationToString (var, Polarity True) = var
  relationToString (var, Polarity False) = "¬" <> var

  invertRel (Polarity x) = Polarity x

instance Relations.ExecRelation Bool Polarity where
  execRel (Polarity True) value = value
  execRel (Polarity False) value = not value

mapError :: Relations.M (Bool, Bool) a -> Relations.M (Error n) a
mapError = Relations.mapError (uncurry ConflictingValuesB)

new :: BooleanRelations
new = Relations.new

assign :: RefB -> Bool -> BooleanRelations -> Relations.M (Error n) BooleanRelations
assign var val xs = mapError $ Relations.assign var val xs

relate :: RefB -> Bool -> RefB -> BooleanRelations -> Relations.M (Error n) BooleanRelations
relate var1 polarity var2 xs = mapError $ Relations.relate var1 (Polarity polarity) var2 xs

relationBetween :: RefB -> RefB -> BooleanRelations -> Maybe Bool
relationBetween var1 var2 xs = unPolarity <$> Relations.relationBetween var1 var2 xs

toMap :: BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
toMap xs = Map.mapMaybe convert $ Relations.toMap xs
  where
    convert (Relations.IsConstant val) = Just (Right val)
    convert (Relations.IsRoot _) = Nothing
    convert (Relations.IsChildOf parent (Polarity polarity)) = Just $ Left (polarity, parent)

toMap2 :: (RefB -> Bool) -> BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
toMap2 shouldBeKept xs = Map.mapMaybeWithKey convert $ Relations.toMap xs
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          Relations.IsConstant val -> Just (Right val)
          Relations.IsRoot _ -> Nothing
          Relations.IsChildOf parent (Polarity polarity) ->
            if shouldBeKept parent
              then Just $ Left (polarity, parent)
              else Nothing
        else Nothing

size :: BooleanRelations -> Int
size = Map.size . Relations.toMap

isValid :: BooleanRelations -> Bool
isValid = Relations.isValid

-- | Result of looking up a variable in the BooleanRelations
data Lookup = Root | Value Bool | ChildOf Bool RefB
  deriving (Eq, Show)

lookup :: RefB -> BooleanRelations -> Lookup
lookup var xs = case Relations.lookup var xs of
  Relations.IsRoot _ -> Root
  Relations.IsConstant val -> Value val
  Relations.IsChildOf parent (Polarity polarity) -> ChildOf polarity parent

lookup' :: RefB -> BooleanRelations -> Relations.VarStatus RefB Bool Bool
lookup' var xs = case Relations.lookup var xs of
  Relations.IsRoot children -> Relations.IsRoot $ fmap unPolarity children
  Relations.IsConstant val -> Relations.IsConstant val
  Relations.IsChildOf parent (Polarity polarity) -> Relations.IsChildOf parent polarity
