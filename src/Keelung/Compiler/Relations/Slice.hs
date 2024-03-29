{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Replace case with fromMaybe" #-}

module Keelung.Compiler.Relations.Slice
  ( SliceRelations,
    new,
    assign,
    relate,
    size,
    lookup,
    toConstraints,
    -- Testing
    isValid,
    Failure (..),
    collectFailure,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.State
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Keelung (FieldType (..), widthOf)
import Keelung.Compiler.Optimize.OccurU (OccurU)
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Util
import Keelung.Data.Constraint
import Keelung.Data.FieldInfo (FieldInfo)
import Keelung.Data.FieldInfo qualified as FieldInfo
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.SliceLookup (Segment, SliceLookup (..))
import Keelung.Data.SliceLookup qualified as SliceLookup
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax (Width)
import Prelude hiding (lookup)

--------------------------------------------------------------------------------

data SliceRelations = SliceRelations
  { srRefO :: Mapping,
    srRefI :: Mapping,
    srRefP :: Mapping,
    srRefX :: Mapping
  }
  deriving (Eq, Generic)

instance NFData SliceRelations

instance Show SliceRelations where
  show (SliceRelations o i p x) =
    "UInt Relations:\n"
      <> showMapping o
      <> showMapping i
      <> showMapping p
      <> showMapping x
    where
      showMapping :: Mapping -> String
      showMapping = indent . mconcat . map showVarMap . IntMap.elems . unMapping

      showVarMap :: IntMap SliceLookup -> String
      showVarMap varMap =
        if IntMap.null varMap
          then ""
          else unlines (map showSliceLookup (IntMap.elems varMap))

      showSliceLookup :: SliceLookup -> String
      showSliceLookup (SliceLookup slice segments) =
        show (sliceRefU slice)
          <> ": "
          <> show (IntMap.elems segments)

new :: SliceRelations
new = SliceRelations (Mapping mempty) (Mapping mempty) (Mapping mempty) (Mapping mempty)

-- | Given a Slice and a value, assign the value to all members of the equivalence class of th Slice
assign :: Slice -> U -> SliceRelations -> SliceRelations
assign slice value relations = flip execState relations $ do
  lookupFamilyWithSliceM slice >>= assignValueToFamily value

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

size :: SliceRelations -> Int
size (SliceRelations refO refI refP refX) = sum (map sizeMapping [refO, refI, refP, refX])
  where
    sizeMapping :: Mapping -> Int
    sizeMapping (Mapping xs) = sum (map sizeVarMap (IntMap.elems xs))

    sizeVarMap :: IntMap SliceLookup -> Int
    sizeVarMap = sum . map (\x -> if SliceLookup.null x then 0 else 1) . IntMap.elems

-- | Given a Slice, return the SliceLookup of the Slice
lookup :: Slice -> SliceRelations -> SliceLookup
lookup (Slice ref start end) relations = lookupMapping (getMapping ref)
  where
    getMapping :: RefU -> Mapping
    getMapping (RefUO _ _) = srRefO relations
    getMapping (RefUI _ _) = srRefI relations
    getMapping (RefUP _ _) = srRefP relations
    getMapping (RefUX _ _) = srRefX relations

    lookupMapping :: Mapping -> SliceLookup
    lookupMapping (Mapping xs) =
      let whenNotFound = SliceLookup (Slice ref start end) (IntMap.singleton start (SliceLookup.Empty (end - start)))
       in case IntMap.lookup (widthOf ref) xs of
            Nothing -> whenNotFound
            Just varMap -> case IntMap.lookup (refUVar ref) varMap of
              Nothing -> whenNotFound
              Just lookups -> SliceLookup.splice (start, end) lookups

-- | Convert relations to specialized constraints
toConstraints :: FieldInfo -> OccurU -> (Slice -> Bool) -> SliceRelations -> Seq (Constraint n)
toConstraints fieldInfo occurrence sliceShouldBeKept = fold step mempty
  where
    fieldWidth :: Width
    fieldWidth = FieldInfo.fieldWidth fieldInfo

    step :: Seq (Constraint n) -> Slice -> Segment -> Seq (Constraint n)
    step acc slice segment = acc <> convert slice segment

    -- see if a Segment should be converted to a Constraint
    convert :: Slice -> Segment -> Seq (Constraint n)
    convert slice segment =
      case segment of
        SliceLookup.Constant val ->
          case sliceRefU slice of
            RefUX width var ->
              -- only export part of slice that is used
              OccurU.maskSlice occurrence width var slice >>= flip buildSliceVal val
            _ ->
              -- pinned reference, all bits needs to be exported
              buildSliceVal slice val
        SliceLookup.ChildOf root ->
          if sliceShouldBeKept slice && sliceShouldBeKept root
            then buildSliceEq slice root
            else mempty
        SliceLookup.Parent _ _ -> mempty
        SliceLookup.Empty _ -> mempty

    -- Slices will be chopped into pieces no longer than `fieldWidth`
    buildSliceEq :: Slice -> Slice -> Seq (Constraint n)
    buildSliceEq x y =
      let widthX = Slice.sliceEnd x - Slice.sliceStart x
          widthY = Slice.sliceEnd y - Slice.sliceStart y
       in if widthX /= widthY
            then error "[ panic ] SliceRelations.toConstraints.buildSliceEq: Slices are of different width"
            else
              Seq.fromList $
                [ CSliceEq
                    (Slice (sliceRefU x) (sliceStart x + i) ((sliceStart x + i + fieldWidth) `min` sliceEnd x))
                    ( Slice (sliceRefU y) (sliceStart y + i) ((sliceStart y + i + fieldWidth) `min` sliceEnd y)
                    )
                  | i <- [0, fieldWidth .. widthOf x - 1]
                ]

    -- Slices will be chopped into pieces no longer than `fieldWidth`
    buildSliceVal :: Slice -> U -> Seq (Constraint n)
    buildSliceVal slice val =
      let -- flip Binary values to positive
          flipped = case FieldInfo.fieldTypeData fieldInfo of
            Binary _ -> if val < 0 then -val else val
            Prime _ -> val
          -- resize the value to the width of the slice
          resized = U.slice flipped (0, widthOf slice)
          -- split the constant into smaller chunks of size `fieldWidth`
          constantChunks = zip [0 ..] (U.chunks fieldWidth resized)
       in Seq.fromList [CSliceVal (Slice (sliceRefU slice) (sliceStart slice + fieldWidth * i) ((sliceStart slice + fieldWidth * (i + 1)) `min` sliceEnd slice)) (toInteger chunk) | (i, chunk) <- constantChunks]

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

type M = State SliceRelations

type SliceSegmentPair = (Slice, Segment)

relateSegment :: (SliceSegmentPair, SliceSegmentPair) -> M ()
relateSegment ((slice1, segment1), (slice2, segment2)) = case (segment1, segment2) of
  (SliceLookup.Constant val1, _) -> lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= assignValueToFamily val1
  (_, SliceLookup.Constant val2) -> lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= assignValueToFamily val2
  (SliceLookup.ChildOf root1, SliceLookup.ChildOf root2) ->
    if root1 > root2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily root1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily root2
  (SliceLookup.ChildOf root1, SliceLookup.Parent {}) ->
    if root1 > slice2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily root1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily slice2
  (SliceLookup.ChildOf root1, SliceLookup.Empty _) -> relateRootToSegment root1 slice2
  (SliceLookup.Parent {}, SliceLookup.ChildOf root2) ->
    if slice1 > root2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily slice1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily root2
  (SliceLookup.Parent {}, SliceLookup.Parent {}) ->
    if slice1 > slice2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily slice1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily slice2
  (SliceLookup.Parent {}, SliceLookup.Empty _) -> relateRootToSegment slice1 slice2
  (SliceLookup.Empty _, SliceLookup.ChildOf root2) -> relateRootToSegment root2 slice1
  (SliceLookup.Empty _, SliceLookup.Parent {}) -> relateRootToSegment slice2 slice1
  (SliceLookup.Empty _, SliceLookup.Empty _) ->
    if slice1 > slice2
      then relateRootToSegment slice1 slice2
      else relateRootToSegment slice2 slice1

assignValueToSegment :: U -> Slice -> M ()
assignValueToSegment val slice@(Slice ref start end) =
  modify $
    modifySliceLookup
      slice
      (mapSliceLookup (SliceLookup.fromRefU ref)) -- insert this SliceLookup if it does not exist
      mapSliceLookup -- else modify the existing SliceLookup
  where
    mapSliceLookup :: SliceLookup -> SliceLookup
    mapSliceLookup = SliceLookup.mapInterval (const (SliceLookup.Constant val)) (start, end)

assignValueToFamily :: U -> FamilyLookup -> M ()
assignValueToFamily _ (FamilyLookup []) = return ()
assignValueToFamily val (FamilyLookup (x : xs)) = do
  let (val1, val2) = U.split val (widthOf (head x))
  mapM_ (assignValueToSegment val1) x
  assignValueToFamily val2 (FamilyLookup xs)

-- | Relate a child Slice with a parent Slice
relateRootToSegment :: Slice -> Slice -> M ()
relateRootToSegment root child = do
  modifySegment addRootToChild child
  modifySegment addChildToRoot root
  where
    addRootToChild :: Maybe Segment -> Segment
    addRootToChild _ = SliceLookup.ChildOf root

    addChildToRoot :: Maybe Segment -> Segment
    addChildToRoot Nothing = SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) (Set.singleton child))
    addChildToRoot (Just (SliceLookup.Parent width children)) = SliceLookup.Parent width (Map.insertWith (<>) (sliceRefU child) (Set.singleton child) children)
    addChildToRoot (Just (SliceLookup.ChildOf _)) = error "[ panic ] relateRootToSegment: the root already has a parent"
    addChildToRoot (Just (SliceLookup.Constant _)) = error "[ panic ] relateRootToSegment: the root already has a value"
    addChildToRoot (Just (SliceLookup.Empty _)) = SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) (Set.singleton child))

    modifySegment :: (Maybe Segment -> Segment) -> Slice -> M ()
    modifySegment f slice =
      modify $
        modifySliceLookup
          slice
          (SliceLookup.fromSegment slice (f Nothing)) -- what to do if the SliceLookup does not exist
          (SliceLookup.mapIntervalWithSlice (const (f . Just)) slice)

relateRootToFamily :: Slice -> FamilyLookup -> M ()
relateRootToFamily _ (FamilyLookup []) = return ()
relateRootToFamily root (FamilyLookup (x : xs)) = do
  let (root1, root2) = Slice.split (widthOf (head x)) root
  mapM_ (relateRootToSegment root1) x
  relateRootToFamily root2 (FamilyLookup xs)

--------------------------------------------------------------------------------

-- | Internal data structure for storing SliceLookups
newtype Mapping = Mapping {unMapping :: IntMap (IntMap SliceLookup)}
  deriving (Eq, Generic)

instance NFData Mapping

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

-- | Given a Slice, modify the SliceLookup referenced by the Slice
--   Insert a new SliceLookup if it does not exist
modifySliceLookup :: Slice -> SliceLookup -> (SliceLookup -> SliceLookup) -> SliceRelations -> SliceRelations
modifySliceLookup (Slice var _ _) e f relations = case var of
  RefUO width _ -> relations {srRefO = Mapping (IntMap.alter alterSliceLookups width (unMapping (srRefO relations)))}
  RefUI width _ -> relations {srRefI = Mapping (IntMap.alter alterSliceLookups width (unMapping (srRefI relations)))}
  RefUP width _ -> relations {srRefP = Mapping (IntMap.alter alterSliceLookups width (unMapping (srRefP relations)))}
  RefUX width _ -> relations {srRefX = Mapping (IntMap.alter alterSliceLookups width (unMapping (srRefX relations)))}
  where
    alterSliceLookups :: Maybe (IntMap SliceLookup) -> Maybe (IntMap SliceLookup)
    alterSliceLookups Nothing = Just (IntMap.singleton (refUVar var) e) -- insert a new SliceLookup if it does not exist
    alterSliceLookups (Just x) = Just (IntMap.alter alterSliceLookup (refUVar var) x)

    alterSliceLookup :: Maybe SliceLookup -> Maybe SliceLookup
    alterSliceLookup Nothing = Just e -- insert a new SliceLookup if it does not exist
    alterSliceLookup (Just x) = Just (f x)

-- | Convert a SliceRelations to a list of SliceSegmentPairs
sliceLookupToPairs :: SliceLookup -> [SliceSegmentPair]
sliceLookupToPairs (SliceLookup slice segments) = map (\(offset, segment) -> (slice {Slice.sliceStart = offset, Slice.sliceEnd = offset + widthOf segment}, segment)) (IntMap.toList segments)

--------------------------------------------------------------------------------

-- | The equivalence class version of SliceLookup
newtype FamilyLookup = FamilyLookup [[Slice]] -- the equivalence class of each segment

-- | Given a Slice and its corresponding Segment, return all member Slices of the equivalence class of that Slice
--   so that we can, for example, assign a value to all members of the equivalence class
--   or relate then to another Slice
familySlicesOfSliceSegmentPair :: SliceRelations -> SliceSegmentPair -> [Slice]
familySlicesOfSliceSegmentPair relations (slice, segment) = case segment of
  SliceLookup.Constant _ -> []
  SliceLookup.ChildOf root ->
    let SliceLookup _ segments = lookup root relations
     in case IntMap.elems segments of
          [] -> error "[ panic ] getFamily: ChildOf root has no segments"
          [SliceLookup.Parent _ children] -> root : Set.toList (Set.unions (Map.elems children))
          [_] -> error "[ panic ] getFamily: Should be Parent"
          _ -> error "[ panic ] getFamily: ChildOf root has more than one segment"
  SliceLookup.Parent _ children -> slice : Set.toList (Set.unions (Map.elems children))
  SliceLookup.Empty _ -> [slice]

lookupFamilyWithSlice :: Slice -> SliceRelations -> FamilyLookup
lookupFamilyWithSlice slice relations =
  let pairs = sliceLookupToPairs $ lookup slice relations
   in FamilyLookup $ map (familySlicesOfSliceSegmentPair relations) pairs

lookupFamilyWithSliceSegmentPair :: SliceSegmentPair -> SliceRelations -> FamilyLookup
lookupFamilyWithSliceSegmentPair pair relations = FamilyLookup [familySlicesOfSliceSegmentPair relations pair]

-- | Monadic version of `lookupFamily` in the `M` monad
lookupFamilyWithSliceM :: Slice -> M FamilyLookup
lookupFamilyWithSliceM = gets . lookupFamilyWithSlice

-- | Monadic version of `lookupFamilyOfSegment` in the `M` monad
lookupFamilyWithSliceSegmentPairM :: SliceSegmentPair -> M FamilyLookup
lookupFamilyWithSliceSegmentPairM = gets . lookupFamilyWithSliceSegmentPair

--------------------------------------------------------------------------------

-- | Given 2 SliceLookups of the same lengths, generate pairs of aligned segments (indexed with their offsets).
--   Such that the boundaries of the generated segments pairs are the union of the boundaries of the two lookups.
--   Example:
--      slice 1      ├─────B─────┼──A──┤
--      slice 2      ├──A──┼─────C─────┤
--                          =>
--      pairs        ├──B──┼──B──┼──A──┤
--      pairs        ├──A──┼──C──┼──C──┤
toAlignedSegmentPairs :: SliceLookup -> SliceLookup -> [(SliceSegmentPair, SliceSegmentPair)]
toAlignedSegmentPairs (SliceLookup slice1 segments1) (SliceLookup slice2 segments2) =
  step (IntMap.toList segments1) (IntMap.toList segments2)
  where
    step :: [(Int, Segment)] -> [(Int, Segment)] -> [(SliceSegmentPair, SliceSegmentPair)]
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