module Keelung.Compiler.Relations.Slice (assignMapping, lookupMapping) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Data.Reference (RefU)
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Syntax (Var, Width)

-- newtype SliceRelations = SliceRelations
--   (IntMap (IntMap Slice))
--   (IntMap (IntMap Slice))
--   (IntMap (IntMap Slice))
--   (IntMap (IntMap Slice)) -- Mappings of bit-width to variable to Slice
--   deriving (Eq)

-- assign :: RefU -> (Int, Int) -> U -> SliceRelations -> SliceRelations
-- assign ref interval val (SliceRelations xs) =
--   let bitWidth = widthOf ref
--    in SliceRelations $ case IntMap.lookup bitWidth xs of
--         Nothing -> IntMap.insert bitWidth (IntMap.singleton ref _) xs
--         Just vs -> case IntMap.lookup bitWidth xs of

newtype Mapping = Mapping (IntMap (IntMap Slice))
  deriving (Eq)

-- | Assign a value to a slice of a variable
assignMapping :: (Var -> RefU) -> Width -> Var -> (Int, Int) -> U -> Mapping -> Mapping
assignMapping ctor width var interval val (Mapping xs) = Mapping (IntMap.alter assignVarMap width xs)
  where
    mapSlice :: Slice -> Slice
    mapSlice = Slice.mapInterval (const (Slice.Constant val)) interval

    assignVarMap :: Maybe (IntMap Slice) -> Maybe (IntMap Slice)
    assignVarMap Nothing = Just (IntMap.singleton var (mapSlice (Slice.fromRefU (ctor var))))
    assignVarMap (Just varMap) = Just (IntMap.alter assignSlice var varMap)

    assignSlice :: Maybe Slice -> Maybe Slice
    assignSlice Nothing = Just (mapSlice (Slice.fromRefU (ctor var)))
    assignSlice (Just slices) = Just (mapSlice slices)

-- | Lookup a slice of a variable
lookupMapping :: (Var -> RefU) -> Width -> Var -> (Int, Int) -> Mapping -> Slice
lookupMapping ctor width var interval (Mapping xs) = case IntMap.lookup width xs of
  Nothing -> Slice.fromRefU (ctor var)
  Just varMap -> case IntMap.lookup var varMap of
    Nothing -> Slice.fromRefU (ctor var)
    Just slices -> Slice.slice interval slices