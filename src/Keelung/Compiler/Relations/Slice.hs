module Keelung.Compiler.Relations.Slice
  ( SliceRelations,
    new,
    assign,
    lookup,
    toEdits,
    toAlignedSegmentPairs,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Keelung (widthOf)
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.Reference (RefU (..))
import Keelung.Data.SliceLookup (Segment, SliceLookup (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
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

lookup :: RefU -> (Int, Int) -> SliceRelations -> SliceLookup
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

fromRefU :: RefU -> RefUDesc
fromRefU (RefUO width var) = RefUDesc RefUO' width var
fromRefU (RefUI width var) = RefUDesc RefUI' width var
fromRefU (RefUP width var) = RefUDesc RefUP' width var
fromRefU (RefUX width var) = RefUDesc RefUX' width var

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

newtype Mapping = Mapping (IntMap (IntMap SliceLookup))
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
      showVarMap :: IntMap SliceLookup -> String
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
    mapSliceLookup :: SliceLookup -> SliceLookup
    mapSliceLookup = SliceLookup.mapInterval (const (SliceLookup.Constant val)) interval

    assignVarMap :: Maybe (IntMap SliceLookup) -> Maybe (IntMap SliceLookup)
    assignVarMap Nothing = Just (IntMap.singleton var (mapSliceLookup (SliceLookup.fromRefU (toRefU ref))))
    assignVarMap (Just varMap) = Just (IntMap.alter assignSliceLookup var varMap)

    assignSliceLookup :: Maybe SliceLookup -> Maybe SliceLookup
    assignSliceLookup Nothing = Just (mapSliceLookup (SliceLookup.fromRefU (toRefU ref)))
    assignSliceLookup (Just lookups) = Just (mapSliceLookup lookups)

-- | Lookup a slice of a variable
lookupMapping :: RefUDesc -> (Int, Int) -> Mapping -> SliceLookup
lookupMapping ref@(RefUDesc _ width var) interval (Mapping xs) = case IntMap.lookup width xs of
  Nothing -> SliceLookup.fromRefU (toRefU ref)
  Just varMap -> case IntMap.lookup var varMap of
    Nothing -> SliceLookup.fromRefU (toRefU ref)
    Just lookups -> SliceLookup.splice interval lookups

--------------------------------------------------------------------------------

data Edit
  = AssignAs (RefUDesc, (Int, Int)) U
  | RelateTo (RefUDesc, (Int, Int)) (RefUDesc, (Int, Int))
  | DoNothing

-- | Given a pair of aligned segments, generate a list of edits
toEdits :: RefUDesc -> RefUDesc -> ((Int, Segment), (Int, Segment)) -> [Edit]
toEdits ref1 ref2 ((index1, segment1), (index2, segment2)) =
  let ref1RefUDesc = (ref1, (index1, index1 + widthOf segment1))
      ref2RefUDesc = (ref2, (index2, index2 + widthOf segment2))
   in case (segment1, segment2) of
        (SliceLookup.Constant _, SliceLookup.Constant _) -> [DoNothing]
        (SliceLookup.Constant val, SliceLookup.ChildOf _) -> [AssignAs ref2RefUDesc val]
        (SliceLookup.Constant val, SliceLookup.Parent _) -> [AssignAs ref2RefUDesc val]
        (SliceLookup.ChildOf _, SliceLookup.Constant val) -> [AssignAs ref1RefUDesc val]
        (SliceLookup.ChildOf root1, SliceLookup.ChildOf root2) ->
          -- see who's root is the real boss
          let root1RefUDesc = (fromRefU (Limb.lmbRef root1), (Limb.lmbOffset root1, Limb.lmbOffset root1 + widthOf root1))
              root2RefUDesc = (fromRefU (Limb.lmbRef root2), (Limb.lmbOffset root2, Limb.lmbOffset root2 + widthOf root2))
           in if root1RefUDesc > root2RefUDesc
                then
                  [ root2RefUDesc `RelateTo` root1RefUDesc,
                    ref2RefUDesc `RelateTo` root1RefUDesc
                  ]
                else
                  [ root1RefUDesc `RelateTo` root2RefUDesc,
                    ref1RefUDesc `RelateTo` root2RefUDesc
                  ]
        (SliceLookup.ChildOf root1, SliceLookup.Parent _) ->
          let root1RefUDesc = (fromRefU (Limb.lmbRef root1), (Limb.lmbOffset root1, Limb.lmbOffset root1 + widthOf root1))
           in if root1RefUDesc > ref2RefUDesc
                then [ref2RefUDesc `RelateTo` root1RefUDesc]
                else [root1RefUDesc `RelateTo` ref2RefUDesc]
        (SliceLookup.Parent _, SliceLookup.Constant val) -> [AssignAs ref1RefUDesc val]
        (SliceLookup.Parent _, SliceLookup.ChildOf root2) ->
          let root2RefUDesc = (fromRefU (Limb.lmbRef root2), (Limb.lmbOffset root2, Limb.lmbOffset root2 + widthOf root2))
           in if ref1RefUDesc > root2RefUDesc
                then [ref1RefUDesc `RelateTo` root2RefUDesc]
                else [root2RefUDesc `RelateTo` ref1RefUDesc]
        (SliceLookup.Parent _, SliceLookup.Parent _) ->
          if ref1RefUDesc > ref2RefUDesc
            then [ref1RefUDesc `RelateTo` ref2RefUDesc]
            else [ref2RefUDesc `RelateTo` ref1RefUDesc]

-- | Given 2 SliceLookups of the same lengths, generate pairs of aligned segments (indexed with their offsets).
--   Such that the boundaries of the generated segments pairs are the union of the boundaries of the two lookups.
--   Example:
-- slice 1      ├─────B─────┼──A──┤
-- slice 2      ├──A──┼─────C─────┤
--            =>
-- pairs        ├──B──┼──B──┼──A──┤
-- pairs        ├──A──┼──C──┼──C──┤
toAlignedSegmentPairs :: SliceLookup -> SliceLookup -> [((Int, Segment), (Int, Segment))]
toAlignedSegmentPairs lookup1 lookup2 = step (IntMap.toList (lookupSegments lookup1)) (IntMap.toList (lookupSegments lookup2))
  where
    step :: [(Int, Segment)] -> [(Int, Segment)] -> [((Int, Segment), (Int, Segment))]
    step ((index1, segment1) : xs1) ((index2, segment2) : xs2) =
      let width1 = widthOf segment1
          width2 = widthOf segment2
       in case width1 `compare` width2 of
            EQ -> ((index1, segment1), (index2, segment2)) : step xs1 xs2
            LT ->
              -- segment1 is shorter, so we split segment2 into two
              let (segment21, segment22) = SliceLookup.splitSegment width1 segment2
               in ((index1, segment1), (index2, segment21)) : step xs1 ((index2 + width1, segment22) : xs2)
            GT ->
              -- segment2 is shorter, so we split segment1 into two
              let (segment11, segment12) = SliceLookup.splitSegment width2 segment1
               in ((index1, segment11), (index2, segment2)) : step ((index1 + width2, segment12) : xs1) xs2
    step _ _ = []
