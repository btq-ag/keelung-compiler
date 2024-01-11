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
import Keelung.Data.Reference (RefU (..), refUVar)
import Keelung.Data.Slice (Slice (..))
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

assign :: Slice -> U -> SliceRelations -> SliceRelations
assign (Slice (RefUO width var) start end) val relations = relations {srRefO = assignMapping (Slice (RefUO width var) start end) val (srRefO relations)}
assign (Slice (RefUI width var) start end) val relations = relations {srRefI = assignMapping (Slice (RefUI width var) start end) val (srRefI relations)}
assign (Slice (RefUP width var) start end) val relations = relations {srRefP = assignMapping (Slice (RefUP width var) start end) val (srRefP relations)}
assign (Slice (RefUX width var) start end) val relations = relations {srRefX = assignMapping (Slice (RefUX width var) start end) val (srRefX relations)}

lookup :: Slice -> SliceRelations -> SliceLookup
lookup (Slice (RefUO width var) start end) relations = lookupMapping (Slice (RefUO width var) start end) (srRefO relations)
lookup (Slice (RefUI width var) start end) relations = lookupMapping (Slice (RefUI width var) start end) (srRefI relations)
lookup (Slice (RefUP width var) start end) relations = lookupMapping (Slice (RefUP width var) start end) (srRefP relations)
lookup (Slice (RefUX width var) start end) relations = lookupMapping (Slice (RefUX width var) start end) (srRefX relations)

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
assignMapping :: Slice -> U -> Mapping -> Mapping
assignMapping (Slice ref start end) val (Mapping xs) = Mapping (IntMap.alter assignVarMap width xs)
  where
    width :: Width
    width = widthOf ref

    var :: Var
    var = refUVar ref

    mapSliceLookup :: SliceLookup -> SliceLookup
    mapSliceLookup = SliceLookup.mapInterval (const (SliceLookup.Constant val)) (start, end)

    assignVarMap :: Maybe (IntMap SliceLookup) -> Maybe (IntMap SliceLookup)
    assignVarMap Nothing = Just (IntMap.singleton var (mapSliceLookup (SliceLookup.fromRefU ref)))
    assignVarMap (Just varMap) = Just (IntMap.alter assignSliceLookup var varMap)

    assignSliceLookup :: Maybe SliceLookup -> Maybe SliceLookup
    assignSliceLookup Nothing = Just (mapSliceLookup (SliceLookup.fromRefU ref))
    assignSliceLookup (Just lookups) = Just (mapSliceLookup lookups)

-- | Lookup a slice of a variable
lookupMapping :: Slice -> Mapping -> SliceLookup
lookupMapping (Slice ref start end) (Mapping xs) =
  let width = widthOf ref
   in case IntMap.lookup width xs of
        Nothing -> SliceLookup.fromRefU ref
        Just varMap -> case IntMap.lookup (refUVar ref) varMap of
          Nothing -> SliceLookup.fromRefU ref
          Just lookups -> SliceLookup.splice (start, end) lookups

--------------------------------------------------------------------------------

data Edit
  = AssignAs Slice U
  | RelateTo Slice Slice
  | DoNothing

-- applyEdits :: Edit -> SliceRelations -> SliceRelations
-- applyEdits (AssignAs slice val) relations = assign slice val relations
-- applyEdits (RelateTo slice1 slice2) relations = _
-- applyEdits DoNothing relations = relations

-- | Given a pair of aligned segments, generate a list of edits
toEdits :: (Slice, Segment) -> (Slice, Segment) -> [Edit]
toEdits (slice1, segment1) (slice2, segment2) = case (segment1, segment2) of
  (SliceLookup.Constant _, SliceLookup.Constant _) -> [DoNothing]
  (SliceLookup.Constant val, SliceLookup.ChildOf _) -> [AssignAs slice1 val]
  (SliceLookup.Constant val, SliceLookup.Parent _ _) -> [AssignAs slice2 val]
  (SliceLookup.ChildOf _, SliceLookup.Constant val) -> [AssignAs slice1 val]
  (SliceLookup.ChildOf root1, SliceLookup.ChildOf root2) ->
    -- see who's root is the real boss
    if root1 > root2
      then
        [ root2 `RelateTo` root1,
          slice2 `RelateTo` root1
        ]
      else
        [ root1 `RelateTo` root2,
          slice1 `RelateTo` root2
        ]
  (SliceLookup.ChildOf root1, SliceLookup.Parent _ _) ->
    if root1 > slice2
      then [slice2 `RelateTo` root1]
      else [root1 `RelateTo` slice2]
  (SliceLookup.Parent _ _, SliceLookup.Constant val) -> [AssignAs slice1 val]
  (SliceLookup.Parent _ _, SliceLookup.ChildOf root2) ->
    if slice1 > root2
      then [slice1 `RelateTo` root2]
      else [root2 `RelateTo` slice1]
  (SliceLookup.Parent _ _, SliceLookup.Parent _ _) ->
    if slice1 > slice2
      then [slice1 `RelateTo` slice2]
      else [slice2 `RelateTo` slice1]

-- | Given 2 SliceLookups of the same lengths, generate pairs of aligned segments (indexed with their offsets).
--   Such that the boundaries of the generated segments pairs are the union of the boundaries of the two lookups.
--   Example:
-- slice 1      ├─────B─────┼──A──┤
-- slice 2      ├──A──┼─────C─────┤
--            =>
-- pairs        ├──B──┼──B──┼──A──┤
-- pairs        ├──A──┼──C──┼──C──┤
toAlignedSegmentPairs :: SliceLookup -> SliceLookup -> [((Slice, Segment), (Slice, Segment))]
toAlignedSegmentPairs (SliceLookup slice1 segments1) (SliceLookup slice2 segments2) = step (IntMap.toList segments1) (IntMap.toList segments2)
  where
    step :: [(Int, Segment)] -> [(Int, Segment)] -> [((Slice, Segment), (Slice, Segment))]
    step ((index1, segment1) : xs1) ((index2, segment2) : xs2) =
      let width1 = widthOf segment1
          width2 = widthOf segment2
       in case width1 `compare` width2 of
            EQ ->
              ( (Slice (sliceRefU slice1) index1 width1, segment1),
                (Slice (sliceRefU slice2) index2 width2, segment2)
              )
                : step xs1 xs2
            LT ->
              -- segment1 is shorter, so we split segment2 into two
              let (segment21, segment22) = SliceLookup.splitSegment width1 segment2
               in ( (Slice (sliceRefU slice1) index1 width1, segment1),
                    (Slice (sliceRefU slice2) index2 width1, segment21)
                  )
                    : step xs1 ((index2 + width1, segment22) : xs2)
            GT ->
              -- segment2 is shorter, so we split segment1 into two
              let (segment11, segment12) = SliceLookup.splitSegment width2 segment1
               in ( (Slice (sliceRefU slice1) index1 width2, segment11),
                    (Slice (sliceRefU slice2) index2 width2, segment2)
                  )
                    : step ((index1 + width2, segment12) : xs1) xs2
    step _ _ = []