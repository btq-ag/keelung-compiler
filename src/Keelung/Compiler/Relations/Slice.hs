module Keelung.Compiler.Relations.Slice
  ( SliceRelations,
    new,
    assign,
    lookup,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Syntax (Var, Width)
import Prelude hiding (lookup)
import Debug.Trace

--------------------------------------------------------------------------------

data SliceRelations = SliceRelations
  { srRefO :: Mapping,
    srRefI :: Mapping,
    srRefP :: Mapping,
    srRefX :: Mapping
  }
  deriving (Eq, Show)

new :: SliceRelations
new = SliceRelations (Mapping mempty) (Mapping mempty) (Mapping mempty) (Mapping mempty)

assign :: RefU -> (Int, Int) -> U -> SliceRelations -> SliceRelations
assign (RefUO width var) interval val relations = relations {srRefO = assignMapping (RefUDesc (RefUO width) width var) interval val (srRefO relations)}
assign (RefUI width var) interval val relations = relations {srRefI = assignMapping (RefUDesc (RefUI width) width var) interval val (srRefI relations)}
assign (RefUP width var) interval val relations = relations {srRefP = assignMapping (RefUDesc (RefUP width) width var) interval val (srRefP relations)}
assign (RefUX width var) interval val relations = relations {srRefX = assignMapping (RefUDesc (RefUX width) width var) interval val (srRefX relations)}

lookup :: RefU -> (Int, Int) -> SliceRelations -> Slice
lookup (RefUO width var) interval relations = lookupMapping (RefUDesc (RefUO width) width var) interval (srRefO relations)
lookup (RefUI width var) interval relations = lookupMapping (RefUDesc (RefUI width) width var) interval (srRefI relations)
lookup (RefUP width var) interval relations = lookupMapping (RefUDesc (RefUP width) width var) interval (srRefP relations)
lookup (RefUX width var) interval relations = lookupMapping (RefUDesc (RefUX width) width var) interval (srRefX relations)

--------------------------------------------------------------------------------

-- | The description of a RefU, so that we can tear them apart and put them back together
data RefUDesc = RefUDesc
  { _descCtor :: Var -> RefU,
    _descWidth :: Width,
    _descVar :: Var
  }

newtype Mapping = Mapping (IntMap (IntMap Slice))
  deriving (Eq)

instance Show Mapping where
  show (Mapping xs) =
    if IntMap.null xs
      then "Mapping {}"
      else
        "Mapping {\n"
          <> unlines (map (\(width, varMap) -> "  " <> show width <> ": " <> showVarMap varMap) (IntMap.toList xs))
          <> "}"
    where
      showVarMap :: IntMap Slice -> String
      showVarMap varMap =
        if IntMap.null varMap
          then "{}"
          else
            "{\n"
              <> unlines (map (\(var, slice) -> "    " <> show var <> ": " <> show slice) (IntMap.toList varMap))
              <> "  }"

-- | Assign a value to a slice of a variable
assignMapping :: RefUDesc -> (Int, Int) -> U -> Mapping -> Mapping
assignMapping (RefUDesc ctor width var) interval val (Mapping xs) = Mapping (IntMap.alter assignVarMap width xs)
  where
    mapSlice :: Slice -> Slice
    mapSlice = Slice.mapInterval (const (Slice.Constant val)) interval

    assignVarMap :: Maybe (IntMap Slice) -> Maybe (IntMap Slice)
    assignVarMap Nothing = traceShowId $ Just (IntMap.singleton var (mapSlice (Slice.fromRefU (ctor var))))
    assignVarMap (Just varMap) = Just (IntMap.alter assignSlice var varMap)

    assignSlice :: Maybe Slice -> Maybe Slice
    assignSlice Nothing = Just (mapSlice (Slice.fromRefU (ctor var)))
    assignSlice (Just slices) = Just (mapSlice slices)

-- | Lookup a slice of a variable
lookupMapping :: RefUDesc -> (Int, Int) -> Mapping -> Slice
lookupMapping (RefUDesc ctor width var) interval (Mapping xs) = case IntMap.lookup width xs of
  Nothing -> Slice.fromRefU (ctor var)
  Just varMap -> case IntMap.lookup var varMap of
    Nothing -> Slice.fromRefU (ctor var)
    Just slices -> Slice.slice interval slices