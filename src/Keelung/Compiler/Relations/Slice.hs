{-# HLINT ignore "Use list comprehension" #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant if" #-}

module Keelung.Compiler.Relations.Slice
  ( SliceRelations,
    new,
    assign,
    relate,
    lookup,
    toAlignedSegmentPairs,
    -- Testing
    isValid,
    Failure (..),
    collectFailure,
  )
where

import Control.Monad.State
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Keelung (widthOf)
import Keelung.Data.Reference (RefU (..), refUVar)
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
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

modifyMapping' :: Slice -> (Mapping -> Mapping) -> SliceRelations -> SliceRelations
modifyMapping' (Slice (RefUO _ _) _ _) f relations = relations {srRefO = f (srRefO relations)}
modifyMapping' (Slice (RefUI _ _) _ _) f relations = relations {srRefI = f (srRefI relations)}
modifyMapping' (Slice (RefUP _ _) _ _) f relations = relations {srRefP = f (srRefP relations)}
modifyMapping' (Slice (RefUX _ _) _ _) f relations = relations {srRefX = f (srRefX relations)}

-- | Fold over all Segments in a SliceRelations
fold :: (a -> Slice -> Segment -> a) -> a -> SliceRelations -> a
fold f acc relations =
  let SliceRelations refO refI refP refX = relations
   in foldl foldMapping acc [refO, refI, refP, refX]
  where
    foldMapping a (Mapping xs) = foldl foldVarMap a xs
    foldVarMap = foldl foldSliceLookup
    foldSliceLookup a (SliceLookup slice segments) = foldl (\b (index, segment) -> f b (Slice (sliceRefU slice) index (index + widthOf segment)) segment) a (IntMap.toList segments)

-- | FOR TESTING: A SliceRelations is valid if:
--    1. all existing SliceLookups cover the entire width of the variable
--    2. all children of a Parent Segment has the parent as its root
isValid :: SliceRelations -> Bool
isValid = null . collectFailure

--------------------------------------------------------------------------------

data Failure
  = InvalidSliceLookupNotCoveringAll SliceLookup
  | InvalidSliceLookup SliceLookup.Failure
  | InvalidKinship Kinship
  deriving (Eq, Show)

collectFailure :: SliceRelations -> [Failure]
collectFailure relations = fromKinshipConstruction <> fromInvalidSliceLookup
  where
    SliceRelations refO refI refP refX = relations

    fromInvalidSliceLookup = mconcat (map isValidMapping [refO, refI, refP, refX])

    isValidMapping :: Mapping -> [Failure]
    isValidMapping (Mapping xs) = mconcat $ map (mconcat . map isValidSliceLookup . IntMap.elems) (IntMap.elems xs)

    isValidSliceLookup :: SliceLookup -> [Failure]
    isValidSliceLookup x =
      if isCoveringAll x
        then map InvalidSliceLookup (SliceLookup.collectFailure False x)
        else [InvalidSliceLookupNotCoveringAll x]

    isCoveringAll :: SliceLookup -> Bool
    isCoveringAll (SliceLookup slice _) = sliceStart slice == 0 && sliceEnd slice == widthOf (sliceRefU slice)

    fromKinshipConstruction :: [Failure]
    fromKinshipConstruction = case nullKinship (destroyKinshipWithParent relations (constructKinshipWithChildOf relations)) of
      Nothing -> []
      Just x -> [InvalidKinship x]

--------------------------------------------------------------------------------

-- | Given 2 Slices, modify the SliceRelations so that they are related
relate :: Slice -> Slice -> SliceRelations -> SliceRelations
relate slice1 slice2 relations =
  let -- modify the slices if they are overlapping
      (slice1', slice2') =
        if Slice.overlaps slice1 slice2
          then modifyOverlappingSlices slice1 slice2
          else (slice1, slice2)
      pairs = toAlignedSegmentPairs (lookup slice1' relations) (lookup slice2' relations)
   in execState (mapM_ relateSegment pairs) relations
  where
    -- When 2 Slices belong to the same variable and they are overlapping
    -- We return only the Slices that are affected by the overlap
    --    Example:
    --      slice1     ├───────────╠═════════════════╣─────┤
    --      slice2     ├─────╠═════════════════╣───────────┤
    --              =>
    --                                   ┌──w──┬──w──┐
    --      result     ├─────╠═══════════╬═════╬═════╣─────┤
    --                                   ↑     ↑     ↑
    --                                  new    rE    cE
    modifyOverlappingSlices :: Slice -> Slice -> (Slice, Slice)
    modifyOverlappingSlices sliceA sliceB =
      let (root, child) = if sliceA > sliceB then (sliceA, sliceB) else (sliceB, sliceA)
          newEndpoint = sliceEnd root - (sliceEnd child - sliceEnd root)
          rootEnd = sliceEnd root
          childEnd = sliceEnd child
       in ( Slice (sliceRefU sliceA) newEndpoint rootEnd,
            Slice (sliceRefU sliceB) rootEnd childEnd
          )

type M = State SliceRelations

getFamilyM :: Slice -> M [Slice]
getFamilyM = gets . getFamily

relateSegment :: ((Slice, Segment), (Slice, Segment)) -> M ()
relateSegment ((slice1, segment1), (slice2, segment2)) = case (segment1, segment2) of
  (SliceLookup.Constant val1, _) -> do
    family <- getFamilyM slice2
    mapM_ (assignValueSegment val1) family
  (_, SliceLookup.Constant val2) -> do
    family <- getFamilyM slice1
    mapM_ (assignValueSegment val2) family
  (SliceLookup.ChildOf root1, SliceLookup.ChildOf root2) ->
    if root1 > root2
      then do
        family <- getFamilyM slice2
        mapM_ (assignRootSegment root1) family
      else do
        family <- getFamilyM slice1
        mapM_ (assignRootSegment root2) family
  (SliceLookup.ChildOf root1, SliceLookup.Parent {}) ->
    if root1 > slice2
      then do
        family <- getFamilyM slice2
        mapM_ (assignRootSegment root1) family
      else do
        family <- getFamilyM slice1
        mapM_ (assignRootSegment slice2) family
  (SliceLookup.ChildOf root1, SliceLookup.Empty _) -> assignRootSegment root1 slice2
  (SliceLookup.Parent {}, SliceLookup.ChildOf root2) ->
    if slice1 > root2
      then do
        family <- getFamilyM slice2
        mapM_ (assignRootSegment slice1) family
      else do
        family <- getFamilyM slice1
        mapM_ (assignRootSegment root2) family
  (SliceLookup.Parent {}, SliceLookup.Parent {}) ->
    if slice1 > slice2
      then do
        family <- getFamilyM slice2
        mapM_ (assignRootSegment slice1) family
      else do
        family <- getFamilyM slice1
        mapM_ (assignRootSegment slice2) family
  (SliceLookup.Parent {}, SliceLookup.Empty _) -> assignRootSegment slice1 slice2
  (SliceLookup.Empty _, SliceLookup.ChildOf root2) -> assignRootSegment root2 slice1
  (SliceLookup.Empty _, SliceLookup.Parent {}) -> assignRootSegment slice2 slice1
  (SliceLookup.Empty _, SliceLookup.Empty _) ->
    if slice1 > slice2
      then assignRootSegment slice1 slice2
      else assignRootSegment slice2 slice1

assignValueSegment :: U -> Slice -> M ()
assignValueSegment val slice = modify (modifyMapping' slice (assignMapping slice val))

-- | Relate a child Slice with a parent Slice
assignRootSegment :: Slice -> Slice -> M ()
assignRootSegment root child = do
  -- relations <- get
  -- traceM $ "\nroot:         " <> show root
  -- traceM $ "\nroot lookup:  " <> show (lookup root relations)
  -- traceM $ "\nchild:        " <> show child
  -- traceM $ "\nchild lookup: " <> show (lookup child relations)
  modify (modifySegment addRootToChild child)
  modify (modifySegment addChildToRoot root)
  where
    addRootToChild :: Maybe Segment -> Segment
    addRootToChild _ = SliceLookup.ChildOf root

    addChildToRoot :: Maybe Segment -> Segment
    addChildToRoot Nothing = SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) (Set.singleton child))
    addChildToRoot (Just (SliceLookup.Parent width children)) = SliceLookup.Parent width (Map.insertWith (<>) (sliceRefU child) (Set.singleton child) children)
    addChildToRoot (Just (SliceLookup.ChildOf anotherRoot)) =
      if sliceRefU root == sliceRefU anotherRoot
        then -- "root" has self reference to itself, convert it to a Parent node
          SliceLookup.Parent (widthOf root) mempty
        else error "[ panic ] assignRootSegment: child already has a parent"
    addChildToRoot (Just (SliceLookup.Constant _)) = error "[ panic ] assignRootSegment: child already has a value"
    addChildToRoot (Just (SliceLookup.Empty _)) = SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) (Set.singleton child))

modifySegment :: (Maybe Segment -> Segment) -> Slice -> SliceRelations -> SliceRelations
modifySegment f slice xs = case sliceRefU slice of
  RefUO width var -> xs {srRefO = modifyMapping width var (srRefO xs)}
  RefUI width var -> xs {srRefI = modifyMapping width var (srRefI xs)}
  RefUP width var -> xs {srRefP = modifyMapping width var (srRefP xs)}
  RefUX width var -> xs {srRefX = modifyMapping width var (srRefX xs)}
  where
    modifyMapping :: Width -> Var -> Mapping -> Mapping
    modifyMapping width var (Mapping mapping) = Mapping $ IntMap.alter alterVarMap width mapping
      where
        alterVarMap :: Maybe (IntMap SliceLookup) -> Maybe (IntMap SliceLookup)
        alterVarMap Nothing = pure (IntMap.singleton var (SliceLookup.fromSegment slice (f Nothing)))
        alterVarMap (Just varMap) = Just $ IntMap.alter alterSliceLookup var varMap

        alterSliceLookup :: Maybe SliceLookup -> Maybe SliceLookup
        alterSliceLookup Nothing = pure (SliceLookup.fromSegment slice (f Nothing))
        alterSliceLookup (Just lookups) = Just $ SliceLookup.mapIntervalWithSlice (const (f . Just)) slice lookups

--------------------------------------------------------------------------------

newtype Mapping = Mapping (IntMap (IntMap SliceLookup))
  deriving (Eq)

instance Show Mapping where
  show (Mapping xs) =
    if IntMap.null xs
      then "Mapping {}"
      else
        "Mapping {\n"
          <> mconcat (map showVarMap (IntMap.elems xs))
          <> "}"
    where
      showVarMap :: IntMap SliceLookup -> String
      showVarMap varMap =
        if IntMap.null varMap
          then ""
          else unlines (map (\(_, slice) -> "    " <> show slice) (IntMap.toList varMap))

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
   in SliceLookup.splice (start, end) $ case IntMap.lookup width xs of
        Nothing -> SliceLookup.fromRefU ref
        Just varMap -> case IntMap.lookup (refUVar ref) varMap of
          Nothing -> SliceLookup.fromRefU ref
          Just lookups -> lookups

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
applyEdit (AssignValue slice val) relations = modifyMapping' slice (assignMapping slice val) relations
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
    go (SliceLookup.Parent _ children) = slice : Set.toList (Set.unions (Map.elems children))
    go (SliceLookup.Empty _) = [slice]

-- | Given 2 SliceLookups of the same lengths, generate pairs of aligned segments (indexed with their offsets).
--   Such that the boundaries of the generated segments pairs are the union of the boundaries of the two lookups.
--   Example:
--      slice 1      ├─────B─────┼──A──┤
--      slice 2      ├──A──┼─────C─────┤
--                          =>
--      pairs        ├──B──┼──B──┼──A──┤
--      pairs        ├──A──┼──C──┼──C──┤
toAlignedSegmentPairs :: SliceLookup -> SliceLookup -> [((Slice, Segment), (Slice, Segment))]
toAlignedSegmentPairs (SliceLookup slice1 segments1) (SliceLookup slice2 segments2) =
  step (IntMap.toList segments1) (IntMap.toList segments2)
  where
    step :: [(Int, Segment)] -> [(Int, Segment)] -> [((Slice, Segment), (Slice, Segment))]
    step ((index1, segment1) : xs1) ((index2, segment2) : xs2) =
      let width1 = widthOf segment1
          width2 = widthOf segment2
       in case width1 `compare` width2 of
            EQ ->
              ( (Slice (sliceRefU slice1) index1 (index1 + width1), segment1),
                (Slice (sliceRefU slice2) index2 (index2 + width2), segment2)
              )
                : step xs1 xs2
            LT ->
              -- segment1 is shorter, so we split segment2 into two
              let (segment21, segment22) = SliceLookup.unsafeSplitSegment width1 segment2
               in ( (Slice (sliceRefU slice1) index1 (index1 + width1), segment1),
                    (Slice (sliceRefU slice2) index2 (index2 + widthOf segment21), segment21)
                  )
                    : step xs1 ((index2 + width1, segment22) : xs2)
            GT ->
              -- segment2 is shorter, so we split segment1 into two
              let (segment11, segment12) = SliceLookup.unsafeSplitSegment width2 segment1
               in ( (Slice (sliceRefU slice1) index1 (index1 + widthOf segment11), segment11),
                    (Slice (sliceRefU slice2) index2 (index2 + width2), segment2)
                  )
                    : step ((index1 + width2, segment12) : xs1) xs2
    step _ _ = []

--------------------------------------------------------------------------------

-- | Data structure for testing the relationship between parent and children
data Kinship = Kinship
  { kinshipParents :: Map RefU (IntMap [Slice]), -- each RefU has intervals that are parents of children
    kinshipChildren ::
      Map
        RefU -- child
        (IntMap Slice) -- parent
  }
  deriving (Eq)

instance Show Kinship where
  show (Kinship parents children) =
    case nullKinship (Kinship parents children) of
      Nothing -> "Kinship {}"
      Just _ ->
        "Kinship {\n"
          <> showParents
          <> showChildren
          <> "}"
    where
      showParents :: String
      showParents =
        "  parents: {\n"
          <> unlines (map (\(ref, x) -> "    " <> show ref <> ": " <> show (IntMap.toList x)) (filter (not . IntMap.null . snd) (Map.toList parents)))
          <> "  }\n"

      showChildren :: String
      showChildren =
        "  children: {\n"
          <> unlines (map (\(ref, x) -> "    " <> show ref <> ": " <> show (IntMap.toList x)) (filter (not . IntMap.null . snd) (Map.toList children)))
          <> "  }\n"

-- return Nothing if the Kinship is valid, otherwise return the invalid Kinship
nullKinship :: Kinship -> Maybe Kinship
nullKinship (Kinship parents children) =
  if all IntMap.null (filter (not . IntMap.null) (Map.elems parents))
    && all IntMap.null (filter (not . IntMap.null) (Map.elems children))
    then Nothing
    else Just (Kinship parents children)

_alter :: (Maybe Slice -> Maybe Slice) -> Slice -> Map RefU (IntMap Slice) -> Map RefU (IntMap Slice)
_alter f slice = flip Map.alter (sliceRefU slice) $ \case
  Nothing -> f Nothing >>= Just . IntMap.singleton (sliceStart slice)
  Just result1 -> Just (IntMap.alter f (sliceStart slice) result1)

-- | `Slice.split` on list of slices
splitMany :: Int -> [Slice] -> ([Slice], [Slice])
splitMany n = unzip . map (Slice.split n)

-- | Helper function for inserting an interval into existing intervals
insertInterval :: (Int, Int) -> Slice -> IntMap [Slice] -> IntMap [Slice]
insertInterval (l, r) inserted intervals =
  -- see if the left endpoint of the inserted interval is within an existing interval or in empty space
  case IntMap.lookupLE l intervals of
    Nothing -> case IntMap.lookupGE r intervals of
      Nothing -> IntMap.insert l [inserted] intervals
      Just next -> leftEndpointInSpace (l, r) inserted next intervals
    Just (l1, existing) ->
      let r1 = l1 + widthOf (head existing) -- assuming that `existing` is not empty list
       in if r1 > l
            then leftEndpointInInterval (l, r) inserted (l1, existing) intervals
            else case IntMap.lookupGE r intervals of
              Nothing -> IntMap.insert l [inserted] intervals
              Just next -> leftEndpointInSpace (l, r) inserted next intervals

-- | When the left endpoint of the inserted interval is within an existing interval
--    l1 <= l
--                l1              r1
--    existing    ├───────────────┤
--    inserted        ├─
--                    l
leftEndpointInInterval :: (Int, Int) -> Slice -> (Int, [Slice]) -> IntMap [Slice] -> IntMap [Slice]
leftEndpointInInterval (l, r) inserted (l1, existing) =
  let r1 = l1 + widthOf (head existing) -- assuming that `existing` is not empty list
   in --  The right endpoint can be one of these 3 cases:
      case r `compare` r1 of
        LT ->
          --    1. r < r1
          --                l1              r1
          --    existing    ├─A─┼───B───┼─C─┤
          --    inserted        ├───X───┤
          --                    l       r
          --
          let (a, bc) = splitMany (l - l1) existing
              (b, c) = splitMany (r - l) bc
           in IntMap.insert l1 a
                . IntMap.insert l (inserted : b)
                . IntMap.insert r c
        EQ ->
          --    1. r = r1
          --                l1              r1
          --    existing    ├─A─┼─────B─────┤
          --    inserted        ├───────────┤
          --                    l           r
          --
          let (a, b) = splitMany (l - l1) existing
           in IntMap.insert l1 a
                . IntMap.insert l (inserted : b)
        GT ->
          --    1. r > r1
          --                l1              r1
          --    existing    ├─A─┼─────B─────┤
          --    inserted        ├─────X─────┼─Y─┤
          --                    l               r
          let (a, b) = splitMany (l - l1) existing
              (x, y) = Slice.split (r1 - l) inserted
           in insertInterval (r1, r) y
                . IntMap.insert l1 a
                . IntMap.insert l (x : b)

-- | When the left endpoint of the inserted interval is in empty space
--    r1 < l
--                r1              l2
--    existing    ────┤           ├───
--    inserted            ├─
--                        l
leftEndpointInSpace :: (Int, Int) -> Slice -> (Int, [Slice]) -> IntMap [Slice] -> IntMap [Slice]
leftEndpointInSpace (l, r) inserted (l2, existing) =
  --  The right endpoint can be one of these 3 cases:
  case r `compare` l2 of
    LT ->
      --    1. r < l2
      --                                l2
      --    existing    ────┤           ├───
      --    inserted            ├─X─┤
      --                        l   r
      --
      IntMap.insert l [inserted]
    EQ ->
      --    1. r = l2
      --                                l2
      --    existing    ────┤           ├───
      --    inserted            ├───X───┤
      --                        l       r
      --
      IntMap.insert l [inserted]
    GT ->
      --    1. r > l2
      --                                l2
      --    existing    ────┤           ├───
      --    inserted            ├─X─────┼─Y─┤
      --                        l           r
      let (x, y) = Slice.split (l2 - l) inserted
       in leftEndpointInInterval (l2, r) y (l2, existing)
            . IntMap.insert l [x]

-- | Construct a Kinship with all Segment.ChildOf in SliceRelations
constructKinshipWithChildOf :: SliceRelations -> Kinship
constructKinshipWithChildOf = fold addRelation (Kinship Map.empty Map.empty)
  where
    addRelation :: Kinship -> Slice -> Segment -> Kinship
    addRelation kinship slice segment = case segment of
      SliceLookup.Constant _ -> kinship
      SliceLookup.ChildOf root ->
        -- make `slice` a child of `root`
        -- make `root` the parent of `slice`
        Kinship
          { kinshipParents = Map.alter (insertChildToParent slice root) (sliceRefU root) (kinshipParents kinship),
            kinshipChildren = Map.alter (insertParentToChild root slice) (sliceRefU slice) (kinshipChildren kinship)
          }
      SliceLookup.Parent {} -> kinship
      SliceLookup.Empty _ -> kinship

    insertChildToParent :: Slice -> Slice -> Maybe (IntMap [Slice]) -> Maybe (IntMap [Slice])
    insertChildToParent slice target Nothing = Just (IntMap.singleton (sliceStart target) [slice])
    insertChildToParent slice target (Just slices) = Just $ insertInterval (sliceStart target, sliceEnd target) slice slices

    insertParentToChild :: Slice -> Slice -> Maybe (IntMap Slice) -> Maybe (IntMap Slice)
    insertParentToChild slice target Nothing = Just (IntMap.singleton (sliceStart target) slice)
    insertParentToChild slice target (Just slices) =
      -- see if the slot is empty so that we can insert the child
      case IntMap.splitLookup (sliceStart target) slices of
        -- the slot is empty, insert the child
        (before, Nothing, after) ->
          let hasSpaceBefore = case IntMap.lookupMax before of
                Nothing -> True -- there is no child before
                Just (index, childBefore) -> index + widthOf childBefore <= sliceStart target -- there is a child before, see if there is enough space
              hasSpaceAfter = case IntMap.lookupMin after of
                Nothing -> True -- there is no child after
                Just (index, _) -> sliceEnd target <= index -- there is a child after, see if there is enough space
           in if hasSpaceBefore
                then
                  if hasSpaceAfter
                    then Just (IntMap.insert (sliceStart target) slice slices)
                    else error "[ panic ] constructKinshipWithChildOf.insertParentToChild: trying to insert a Slice but there is not enough space after"
                else error "[ panic ] constructKinshipWithChildOf.insertParentToChild: trying to insert a Slice but there is not enough space before"
        -- the slot is not empty, see if the child is already there
        (_, Just existing, _) -> error $ "[ panic ] constructKinshipWithChildOf.insertParentToChild: trying to insert a Slice " <> show slice <> " but found " <> show existing <> " at slot " <> show target

destroyKinshipWithParent :: SliceRelations -> Kinship -> Kinship
destroyKinshipWithParent = flip (fold removeRelation)
  where
    removeRelation :: Kinship -> Slice -> Segment -> Kinship
    removeRelation kinship slice segment = case segment of
      SliceLookup.Constant _ -> kinship
      SliceLookup.ChildOf _ -> kinship
      SliceLookup.Parent _ children ->
        Kinship
          { kinshipParents = Map.alter removeChildFromParent (sliceRefU slice) (kinshipParents kinship),
            kinshipChildren = foldl removeParentFromChild (kinshipChildren kinship) (Set.toList (Set.unions (Map.elems children)))
          }
      SliceLookup.Empty _ -> kinship

    removeChildFromParent :: Maybe (IntMap [Slice]) -> Maybe (IntMap [Slice])
    removeChildFromParent _ = Nothing

    removeParentFromChild :: Map RefU (IntMap Slice) -> Slice -> Map RefU (IntMap Slice)
    removeParentFromChild allChildren child = Map.alter (removeParentFromChild' child) (sliceRefU child) allChildren

    removeParentFromChild' :: Slice -> Maybe (IntMap Slice) -> Maybe (IntMap Slice)
    removeParentFromChild' _ Nothing = Nothing
    removeParentFromChild' child (Just slices) = Just (IntMap.delete (sliceStart child) slices)