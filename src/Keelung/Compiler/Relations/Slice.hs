module Keelung.Compiler.Relations.Slice (assignMapping) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Data.Reference (RefU)
import Keelung.Data.Slice (Slices)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Syntax (Var, Width)

-- newtype SliceRelations = SliceRelations
--   (IntMap (IntMap Slices))
--   (IntMap (IntMap Slices))
--   (IntMap (IntMap Slices))
--   (IntMap (IntMap Slices)) -- Mappings of bit-width to variable to Slices
--   deriving (Eq)

-- assign :: RefU -> (Int, Int) -> U -> SliceRelations -> SliceRelations
-- assign ref interval val (SliceRelations xs) =
--   let bitWidth = widthOf ref
--    in SliceRelations $ case IntMap.lookup bitWidth xs of
--         Nothing -> IntMap.insert bitWidth (IntMap.singleton ref _) xs
--         Just vs -> case IntMap.lookup bitWidth xs of

newtype Mapping = Mapping (IntMap (IntMap Slices))
  deriving (Eq)

-- | Assign a value to a slice of a variable
assignMapping :: (Var -> RefU) -> Width -> Var -> (Int, Int) -> U -> Mapping -> Mapping
assignMapping ctor width var interval val (Mapping xs) = Mapping (IntMap.alter assignVarMap width xs)
  where
    mapSlices :: Slices -> Slices
    mapSlices = Slice.mapInterval (const (Slice.Constant val)) interval

    assignVarMap :: Maybe (IntMap Slices) -> Maybe (IntMap Slices)
    assignVarMap Nothing = Just (IntMap.singleton var (mapSlices (Slice.fromRefU (ctor var))))
    assignVarMap (Just varMap) = Just (IntMap.alter assignSlices var varMap)

    assignSlices :: Maybe Slices -> Maybe Slices
    assignSlices Nothing = Just (mapSlices (Slice.fromRefU (ctor var)))
    assignSlices (Just slices) = Just (mapSlices slices)

-- | Lookup a slice of a variable
lookupMapping :: (Var -> RefU) -> Width -> Var -> (Int, Int) -> Mapping -> Slices
lookupMapping ctor width var interval (Mapping xs) = case IntMap.lookup width xs of
  Nothing -> Slice.fromRefU (ctor var)
  Just varMap -> case IntMap.lookup var varMap of
    Nothing -> Slice.fromRefU (ctor var)
    Just slices -> Slice.slice interval slices