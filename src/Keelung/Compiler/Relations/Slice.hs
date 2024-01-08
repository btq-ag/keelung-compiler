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
assign (RefUO width var) interval val relations = relations {srRefO = assignMapping (RefUDesc RefUO' width var, interval) val (srRefO relations)}
assign (RefUI width var) interval val relations = relations {srRefI = assignMapping (RefUDesc RefUI' width var, interval) val (srRefI relations)}
assign (RefUP width var) interval val relations = relations {srRefP = assignMapping (RefUDesc RefUP' width var, interval) val (srRefP relations)}
assign (RefUX width var) interval val relations = relations {srRefX = assignMapping (RefUDesc RefUX' width var, interval) val (srRefX relations)}

lookup :: RefU -> (Int, Int) -> SliceRelations -> Slice
lookup (RefUO width var) interval relations = lookupMapping (RefUDesc RefUO' width var) interval (srRefO relations)
lookup (RefUI width var) interval relations = lookupMapping (RefUDesc RefUI' width var) interval (srRefI relations)
lookup (RefUP width var) interval relations = lookupMapping (RefUDesc RefUP' width var) interval (srRefP relations)
lookup (RefUX width var) interval relations = lookupMapping (RefUDesc RefUX' width var) interval (srRefX relations)

--------------------------------------------------------------------------------

-- | The description of a RefU, so that we can tear them apart and put them back together
data RefUKind = RefUO' | RefUI' | RefUP' | RefUX' deriving (Eq)

data RefUDesc = RefUDesc RefUKind Width Var deriving (Eq)

-- | Compose a RefU with a RefUDesc
toRefU :: RefUDesc -> RefU
toRefU (RefUDesc RefUO' width var) = RefUO width var
toRefU (RefUDesc RefUI' width var) = RefUI width var
toRefU (RefUDesc RefUP' width var) = RefUP width var
toRefU (RefUDesc RefUX' width var) = RefUX width var

-- | For UnionFind root competition, larger RefUs gets to be the root
--    1. compare the kind of RefUs: RefUI = RefUP > RefUO > RefUX
--    2. compare the width of RefUs: larger width > smaller width
--    3. compare the var of RefUs: smaller var > larger var
instance Ord RefUDesc where
  compare (RefUDesc kind1 width1 var1) (RefUDesc kind2 width2 var2) = case (kind1, kind2) of
    (RefUI', RefUI') -> compare width1 width2 <> compare var2 var1
    (RefUI', RefUP') -> compare width1 width2 <> compare var2 var1 <> GT
    (RefUI', _) -> GT
    (RefUP', RefUI') -> compare width1 width2 <> compare var2 var1 <> LT
    (RefUP', RefUP') -> compare width1 width2 <> compare var2 var1
    (RefUP', _) -> GT
    (RefUO', RefUI') -> LT
    (RefUO', RefUP') -> LT
    (RefUO', RefUO') -> compare width1 width2 <> compare var2 var1
    (RefUO', _) -> GT
    (RefUX', RefUI') -> LT
    (RefUX', RefUP') -> LT
    (RefUX', RefUO') -> LT
    (RefUX', RefUX') -> compare width1 width2 <> compare var2 var1

--------------------------------------------------------------------------------

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
assignMapping :: (RefUDesc, (Int, Int)) -> U -> Mapping -> Mapping
assignMapping (ref@(RefUDesc _ width var), interval) val (Mapping xs) = Mapping (IntMap.alter assignVarMap width xs)
  where
    mapSlice :: Slice -> Slice
    mapSlice = Slice.mapInterval (const (Slice.Constant val)) interval

    assignVarMap :: Maybe (IntMap Slice) -> Maybe (IntMap Slice)
    assignVarMap Nothing = Just (IntMap.singleton var (mapSlice (Slice.fromRefU (toRefU ref))))
    assignVarMap (Just varMap) = Just (IntMap.alter assignSlice var varMap)

    assignSlice :: Maybe Slice -> Maybe Slice
    assignSlice Nothing = Just (mapSlice (Slice.fromRefU (toRefU ref)))
    assignSlice (Just slices) = Just (mapSlice slices)

-- relateMapping :: (RefUDesc, (Int, Int)) -> (RefUDesc, (Int, Int)) -> Mapping -> Mapping
-- relateMapping (RefUDesc ctor1 width1 var1, interval1) (RefUDesc ctor2 width2 var2, interval2) (Mapping xs) = Mapping (IntMap.alter relateVarMap width1 xs)
--   where
--     relateVarMap :: Maybe (IntMap Slice) -> Maybe (IntMap Slice)
--     relateVarMap Nothing = Just (IntMap.singleton var1 (Slice.fromRefU (ctor1 var1)))
--     relateVarMap (Just varMap) = Just (IntMap.alter relateSlice var1 varMap)

--     relateSlice :: Maybe Slice -> Maybe Slice
--     relateSlice Nothing = Just (Slice.fromRefU (ctor1 var1))
--     relateSlice (Just slices) = Just (Slice.mapInterval (const (Slice.ChildOf (Limb.new (ctor2 var2) (snd interval2 - fst interval2) (fst interval2) (Left slices)))) interval1 slices)

-- | Lookup a slice of a variable
lookupMapping :: RefUDesc -> (Int, Int) -> Mapping -> Slice
lookupMapping ref@(RefUDesc _ width var) interval (Mapping xs) = case IntMap.lookup width xs of
  Nothing -> Slice.fromRefU (toRefU ref)
  Just varMap -> case IntMap.lookup var varMap of
    Nothing -> Slice.fromRefU (toRefU ref)
    Just slices -> Slice.slice interval slices