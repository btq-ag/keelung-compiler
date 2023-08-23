{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Relations.Boolean
  ( BooleanRelations,
    new,
    assign,
    relate,
    relationBetween,
    toMap,
    size,
    isValid,
    Polarity (..),
  )
where

import Control.DeepSeq (NFData)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Data.Reference
import Prelude hiding (lookup)

type BooleanRelations = EquivClass.EquivClass RefB Bool Polarity

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

instance EquivClass.IsRelation Polarity where
  relationToString (var, Polarity True) = var
  relationToString (var, Polarity False) = "¬" <> var

  invertRel (Polarity x) = Just (Polarity x)

instance EquivClass.ExecRelation Bool Polarity where
  execRel (Polarity True) value = value
  execRel (Polarity False) value = not value

mapError :: EquivClass.M (Bool, Bool) a -> EquivClass.M (Error n) a
mapError = EquivClass.mapError (uncurry ConflictingValuesB)

new :: BooleanRelations
new = EquivClass.new "Boolean"

assign :: RefB -> Bool -> BooleanRelations -> EquivClass.M (Error n) BooleanRelations
assign var val xs = mapError $ EquivClass.assign var val xs

relate :: RefB -> Bool -> RefB -> BooleanRelations -> EquivClass.M (Error n) BooleanRelations
relate var1 polarity var2 xs = mapError $ EquivClass.relate var1 (Polarity polarity) var2 xs

relationBetween :: RefB -> RefB -> BooleanRelations -> Maybe Bool
relationBetween var1 var2 xs = unPolarity <$> EquivClass.relationBetween var1 var2 xs

toMap :: (RefB -> Bool) -> BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
toMap shouldBeKept xs = Map.mapMaybeWithKey convert $ EquivClass.toMap xs
  where
    convert var status = do
      if shouldBeKept var
        then case status of
          EquivClass.IsConstant val -> Just (Right val)
          EquivClass.IsRoot _ -> Nothing
          EquivClass.IsChildOf parent (Polarity polarity) ->
            if shouldBeKept parent
              then Just $ Left (polarity, parent)
              else Nothing
        else Nothing

size :: BooleanRelations -> Int
size = Map.size . EquivClass.toMap

isValid :: BooleanRelations -> Bool
isValid = EquivClass.isValid

-- -- | Result of looking up a variable in the BooleanRelations
-- data Lookup = Root | Value Bool | ChildOf Bool RefB
--   deriving (Eq, Show)

-- lookup :: RefB -> BooleanRelations -> Lookup
-- lookup var xs = case EquivClass.lookup var xs of
--   EquivClass.IsRoot _ -> Root
--   EquivClass.IsConstant val -> Value val
--   EquivClass.IsChildOf parent (Polarity polarity) -> ChildOf polarity parent

-- lookup' :: RefB -> BooleanRelations -> EquivClass.VarStatus RefB Bool Bool
-- lookup' var xs = case EquivClass.lookup var xs of
--   EquivClass.IsRoot children -> EquivClass.IsRoot $ fmap unPolarity children
--   EquivClass.IsConstant val -> EquivClass.IsConstant val
--   EquivClass.IsChildOf parent (Polarity polarity) -> EquivClass.IsChildOf parent polarity
