{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile.Relations.Boolean
  ( BooleanRelations,
    new,
    assign,
    relate,
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

liftError :: Except (Bool, Bool) a -> Except (Error n) a
liftError = withExceptT (uncurry ConflictingValuesB)

new :: BooleanRelations
new = Relations.new

assign :: RefB -> Bool -> BooleanRelations -> Except (Error n) (Maybe BooleanRelations)
assign var val xs = liftError $ Just <$> Relations.assign var val xs

relate :: RefB -> Bool -> RefB -> BooleanRelations -> Except (Error n) (Maybe BooleanRelations)
relate var1 polarity var2 xs = liftError $ Just <$> Relations.relate var1 (Polarity polarity) var2 xs

relationBetween :: RefB -> RefB -> BooleanRelations -> Maybe Bool
relationBetween var1 var2 xs = unPolarity <$> Relations.relationBetween var1 var2 xs

toIntMap :: BooleanRelations -> Map RefB (Either (Bool, RefB) Bool)
toIntMap xs = Map.mapMaybe convert $ Relations.toMap xs
  where
    convert (Relations.IsConstant val) = Just (Right val)
    convert (Relations.IsRoot _) = Nothing
    convert (Relations.IsChildOf parent (Polarity polarity)) = Just $ Left (polarity, parent)

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
