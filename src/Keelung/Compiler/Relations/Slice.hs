module Keelung.Compiler.Relations.Slice
  ( SliceRelations,
    new,
    assign,
    lookup,
    toAlignedSegmentPairs,
    modifySliceLookup,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
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
assign slice value relations = foldr applyEdit relations (assignmentToEdits slice value relations)

lookup :: Slice -> SliceRelations -> SliceLookup
lookup slice relations = lookupMapping slice (getMapping slice relations)

getMapping :: Slice -> SliceRelations -> Mapping
getMapping (Slice (RefUO _ _) _ _) relations = srRefO relations
getMapping (Slice (RefUI _ _) _ _) relations = srRefI relations
getMapping (Slice (RefUP _ _) _ _) relations = srRefP relations
getMapping (Slice (RefUX _ _) _ _) relations = srRefX relations

modifyMapping :: Slice -> (Mapping -> Mapping) -> SliceRelations -> SliceRelations
modifyMapping (Slice (RefUO _ _) _ _) f relations = relations {srRefO = f (srRefO relations)}
modifyMapping (Slice (RefUI _ _) _ _) f relations = relations {srRefI = f (srRefI relations)}
modifyMapping (Slice (RefUP _ _) _ _) f relations = relations {srRefP = f (srRefP relations)}
modifyMapping (Slice (RefUX _ _) _ _) f relations = relations {srRefX = f (srRefX relations)}

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

-- -- | Relate a child Slice with a parent Slice
-- relateMapping :: Slice -> Slice -> Mapping -> Mapping
-- relateMapping child root = alterSliceLookup alterRoot root . alterSliceLookup alterChild child
--   where 
--     alterChild :: Maybe SliceLookup -> Maybe SliceLookup
--     alterChild Nothing = Just (SliceLookup child (IntMap.singleton (sliceStart child) (SliceLookup.ChildOf root)))
--     alterChild (Just lookups) = _

--     alterRoot :: Maybe SliceLookup -> Maybe SliceLookup
--     alterRoot = _


modifySliceLookup :: (Maybe SliceLookup -> Maybe SliceLookup) -> Slice -> Mapping -> Mapping
modifySliceLookup f slice (Mapping xs) = Mapping (IntMap.alter alterVarMap width xs)
  where
    width :: Width
    width = widthOf (sliceRefU slice)

    var :: Var
    var = refUVar (sliceRefU slice)

    alterVarMap :: Maybe (IntMap SliceLookup) -> Maybe (IntMap SliceLookup)
    alterVarMap Nothing = f Nothing >>= \lookups -> pure (IntMap.singleton var lookups)
    alterVarMap (Just varMap) = Just $ IntMap.alter f var varMap

--------------------------------------------------------------------------------

assignmentToEdits :: Slice -> U -> SliceRelations -> [Edit]
assignmentToEdits slice value relations = map (`AssignValue` value) (getFamily slice relations)

data Edit
  = AssignValue Slice U -- assign the slice itself the value
  | AssignRootValue Slice U -- assign the slice itself (root) and all its children the value, needs further lookup

-- \| RelateTo Slice Slice -- relate the slice itself to the other slice
-- \| RelateRootTo Slice Slice -- relate the slice itself (root) and all its children to the other slice, needs further lookup

applyEdits :: [Edit] -> SliceRelations -> SliceRelations
applyEdits edits relations = foldr applyEdit relations edits

applyEdit :: Edit -> SliceRelations -> SliceRelations
applyEdit (AssignValue slice val) relations = modifyMapping slice (assignMapping slice val) relations
applyEdit (AssignRootValue root val) relations = applyEdits (map (`AssignValue` val) (getFamily root relations)) relations

-- | Given the slice, return all members of the equivalence class (including the slice itself)
getFamily :: Slice -> SliceRelations -> [Slice]
getFamily slice relations =
  let SliceLookup _ segments = lookup slice relations
   in IntMap.elems segments >>= go
  where
    go :: Segment -> [Slice]
    go (SliceLookup.Constant _) = []
    go (SliceLookup.ChildOf root) = getFamily root relations
    go (SliceLookup.Parent _ children) = slice : Map.elems children

-- -- | Given a pair of aligned segments, generate a list of edits
-- toEdits :: (Slice, Segment) -> (Slice, Segment) -> [Edit]
-- toEdits (slice1, segment1) (slice2, segment2) = case (segment1, segment2) of
--   (SliceLookup.Constant _, SliceLookup.Constant _) -> []
--   (SliceLookup.Constant val1, SliceLookup.ChildOf root2) -> [AssignRootValue root2 val1]
--   (SliceLookup.Constant val1, SliceLookup.Parent _ children2) -> AssignValue slice2 val1 : map (`AssignValue` val1) (Map.elems children2)
--   (SliceLookup.ChildOf root1, SliceLookup.Constant val2) -> [AssignRootValue root1 val2]
--   (SliceLookup.ChildOf root1, SliceLookup.ChildOf root2) ->
--     -- see who's root is the real boss
--     if root1 > root2
--       then -- root1 is the boss

--         [ root2 `RelateRootTo` root1,
--           slice2 `RelateTo` root1
--         ]
--       else -- root2 is the boss

--         [ root1 `RelateRootTo` root2,
--           slice1 `RelateTo` root2
--         ]
--   (SliceLookup.ChildOf root1, SliceLookup.Parent _ children2) ->
--     if root1 > slice2
--       then RelateTo slice2 root1 : map (`RelateTo` root1) (Map.elems children2)
--       else [RelateRootTo root1 slice2]
--   (SliceLookup.Parent _ children1, SliceLookup.Constant val2) -> AssignValue slice1 val2 : map (`AssignValue` val2) (Map.elems children1)
--   (SliceLookup.Parent _ children1, SliceLookup.ChildOf root2) ->
--     if slice1 > root2
--       then [root2 `RelateRootTo` slice1] -- slice1 is the boss
--       else RelateTo slice1 root2 : map (`RelateTo` root2) (Map.elems children1) -- root2 is the boss
--   (SliceLookup.Parent _ children1, SliceLookup.Parent _ children2) ->
--     if slice1 > slice2
--       then RelateTo slice2 slice1 : map (`RelateTo` slice1) (Map.elems children2) -- slice1 is the boss
--       else RelateTo slice1 slice2 : map (`RelateTo` slice2) (Map.elems children1) -- slice2 is the boss

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