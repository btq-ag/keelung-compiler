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
    refUSegmentsRefUBit,
    toConstraints,
    -- Testing
    isValid,
    Failure (..),
    validate,
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
import Keelung.Data.RefUSegments (PartialRefUSegments (PartialRefUSegments), RefUSegments (..))
import Keelung.Data.RefUSegments qualified as RefUSegments
import Keelung.Data.Reference
import Keelung.Data.Segment (Segment)
import Keelung.Data.Segment qualified as Segment
import Keelung.Data.Slice (Slice (..))
import Keelung.Data.Slice qualified as Slice
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
      <> show o
      <> show i
      <> show p
      <> show x

new :: SliceRelations
new = SliceRelations (Mapping mempty) (Mapping mempty) (Mapping mempty) (Mapping mempty)

-- | Given a Slice and a value, assign the value to all members of the equivalence class of th Slice
assign :: Slice -> U -> SliceRelations -> SliceRelations
assign slice value relations = flip execState relations $ do
  lookupFamilyWithSliceM slice >>= assignValueToFamily value

-- | Given 2 Slices, modify the SliceRelations so that they are related
relate :: Slice -> Slice -> SliceRelations -> SliceRelations
relate slice1 slice2 relations = case handleOverlappingSlices slice1 slice2 of
  Nothing -> relations -- no-op
  Just (slice1', slice2') ->
    let pairs = toAlignedSegmentPairs (lookup slice1' relations) (lookup slice2' relations)
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
    handleOverlappingSlices :: Slice -> Slice -> Maybe (Slice, Slice)
    handleOverlappingSlices sliceA sliceB
      | sliceA == sliceB = Nothing
      | not (sliceA `Slice.overlaps` sliceB) = Just (sliceA, sliceB)
      | otherwise =
          let (root, child) = if sliceA > sliceB then (sliceA, sliceB) else (sliceB, sliceA)
              newEndpoint = sliceEnd root - (sliceEnd child - sliceEnd root)
              rootEnd = sliceEnd root
              childEnd = sliceEnd child
           in Just
                ( Slice (sliceRefU sliceA) newEndpoint rootEnd,
                  Slice (sliceRefU sliceB) rootEnd childEnd
                )

size :: SliceRelations -> Int
size (SliceRelations refO refI refP refX) = sum (map sizeMapping [refO, refI, refP, refX])
  where
    sizeMapping :: Mapping -> Int
    sizeMapping (Mapping xs) = sum (map sizeVarMap (IntMap.elems xs))

    sizeVarMap :: IntMap RefUSegments -> Int
    sizeVarMap = IntMap.size

-- | Given a Slice, return the RefUSegments of the Slice
lookup :: Slice -> SliceRelations -> PartialRefUSegments
lookup (Slice ref start end) relations = getRefUSegments (getMapping ref)
  where
    getMapping :: RefU -> Mapping
    getMapping (RefUO _ _) = srRefO relations
    getMapping (RefUI _ _) = srRefI relations
    getMapping (RefUP _ _) = srRefP relations
    getMapping (RefUX _ _) = srRefX relations

    getRefUSegments :: Mapping -> PartialRefUSegments
    getRefUSegments (Mapping xs) =
      let whenNotFound = PartialRefUSegments (Slice ref start end) (IntMap.singleton start (Segment.Free (end - start)))
       in case IntMap.lookup (widthOf ref) xs of
            Nothing -> whenNotFound
            Just varToSegments -> case IntMap.lookup (refUVar ref) varToSegments of
              Nothing -> whenNotFound
              Just segments -> RefUSegments.splice (start, end) segments

-- | Given a RefUBit, return the Segment of the RefUBit
refUSegmentsRefUBit :: RefU -> Int -> SliceRelations -> Maybe (Either (RefU, Int) Bool)
refUSegmentsRefUBit ref index relations = getRefUSegments (getMapping ref)
  where
    getMapping :: RefU -> Mapping
    getMapping (RefUO _ _) = srRefO relations
    getMapping (RefUI _ _) = srRefI relations
    getMapping (RefUP _ _) = srRefP relations
    getMapping (RefUX _ _) = srRefX relations

    getRefUSegments :: Mapping -> Maybe (Either (RefU, Int) Bool)
    getRefUSegments (Mapping xs) = case IntMap.lookup (widthOf ref) xs of
      Nothing -> Nothing
      Just varToSegments -> case IntMap.lookup (refUVar ref) varToSegments of
        Nothing -> Nothing
        Just segments -> RefUSegments.lookupAt index segments

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
        Segment.Constant val ->
          case sliceRefU slice of
            RefUX width var ->
              -- only export part of slice that is used
              OccurU.maskSlice occurrence width var slice >>= flip buildSliceVal val
            _ ->
              -- pinned reference, all bits needs to be exported
              buildSliceVal slice val
        Segment.ChildOf root ->
          if sliceShouldBeKept slice && sliceShouldBeKept root
            then buildSliceEq slice root
            else mempty
        Segment.ParentOf _ _ -> mempty
        Segment.Free _ -> mempty

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
          resized = U.slice (0, widthOf slice) flipped
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
    foldVarMap = foldl foldRefUSegments
    foldRefUSegments a (RefUSegments ref segments) = foldl (\b (index, segment) -> f b (Slice ref index (index + widthOf segment)) segment) a (IntMap.toList segments)

-- | FOR TESTING: A SliceRelations is valid if:
--    1. all existing RefUSegments cover the entire width of the variable
--    2. all children of a Parent Segment has the parent as its root
isValid :: SliceRelations -> Bool
isValid = null . validate

--------------------------------------------------------------------------------

data Failure
  = InvalidRefUSegments RefUSegments.Error
  | InvalidKinship Kinship
  deriving (Eq, Show)

validate :: SliceRelations -> [Failure]
validate relations = fromKinshipConstruction <> fromInvalidRefUSegments
  where
    SliceRelations refO refI refP refX = relations

    fromInvalidRefUSegments = mconcat (map isValidMapping [refO, refI, refP, refX])

    isValidMapping :: Mapping -> [Failure]
    isValidMapping (Mapping xs) = mconcat $ map (mconcat . map isValidRefUSegments . IntMap.elems) (IntMap.elems xs)

    isValidRefUSegments :: RefUSegments -> [Failure]
    isValidRefUSegments x = map InvalidRefUSegments (RefUSegments.validate x)

    fromKinshipConstruction :: [Failure]
    fromKinshipConstruction = case nullKinship (destroyKinshipWithParent relations (constructKinshipWithChildOf relations)) of
      Nothing -> []
      Just x -> [InvalidKinship x]

--------------------------------------------------------------------------------

type M = State SliceRelations

type SliceSegmentPair = (Slice, Segment)

relateSegment :: (SliceSegmentPair, SliceSegmentPair) -> M ()
relateSegment ((slice1, segment1), (slice2, segment2)) = case (segment1, segment2) of
  (Segment.Constant val1, _) -> lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= assignValueToFamily val1
  (_, Segment.Constant val2) -> lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= assignValueToFamily val2
  (Segment.ChildOf root1, Segment.ChildOf root2) ->
    if root1 > root2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily root1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily root2
  (Segment.ChildOf root1, Segment.ParentOf {}) ->
    if root1 > slice2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily root1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily slice2
  (Segment.ChildOf root1, Segment.Free _) -> relateRootToSegment root1 slice2
  (Segment.ParentOf {}, Segment.ChildOf root2) ->
    if slice1 > root2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily slice1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily root2
  (Segment.ParentOf {}, Segment.ParentOf {}) ->
    if slice1 > slice2
      then lookupFamilyWithSliceSegmentPairM (slice2, segment2) >>= relateRootToFamily slice1
      else lookupFamilyWithSliceSegmentPairM (slice1, segment1) >>= relateRootToFamily slice2
  (Segment.ParentOf {}, Segment.Free _) -> relateRootToSegment slice1 slice2
  (Segment.Free _, Segment.ChildOf root2) -> relateRootToSegment root2 slice1
  (Segment.Free _, Segment.ParentOf {}) -> relateRootToSegment slice2 slice1
  (Segment.Free _, Segment.Free _) ->
    if slice1 > slice2
      then relateRootToSegment slice1 slice2
      else relateRootToSegment slice2 slice1

assignValueToSegment :: U -> Slice -> M ()
assignValueToSegment val (Slice ref start end) =
  modify $
    modifyRefUSegments
      ref
      (mapRefUSegments (RefUSegments.fromRefU ref)) -- insert this RefUSegments if it does not exist
      mapRefUSegments -- else modify the existing RefUSegments
  where
    mapRefUSegments :: RefUSegments -> RefUSegments
    mapRefUSegments = RefUSegments.mapInterval (const (Segment.Constant val)) (start, end)

assignValueToFamily :: U -> FamilyLookup -> M ()
assignValueToFamily _ (FamilyLookup []) = return ()
assignValueToFamily val (FamilyLookup ([] : xs)) = do
  assignValueToFamily val (FamilyLookup xs)
assignValueToFamily val (FamilyLookup ((x : xs) : xss)) = do
  let (val1, val2) = U.split val (widthOf x)
  mapM_ (assignValueToSegment val1) (x : xs)
  assignValueToFamily val2 (FamilyLookup xss)

-- | Relate a child Slice with a parent Slice
relateRootToSegment :: Slice -> Slice -> M ()
relateRootToSegment root child = do
  modifySegment addRootToChild child
  modifySegment addChildToRoot root
  where
    addRootToChild :: Maybe Segment -> Segment
    addRootToChild _ = Segment.ChildOf root

    addChildToRoot :: Maybe Segment -> Segment
    addChildToRoot Nothing = Segment.ParentOf (widthOf root) (Map.singleton (sliceRefU child) (Set.singleton child))
    addChildToRoot (Just (Segment.ParentOf width children)) = Segment.ParentOf width (Map.insertWith (<>) (sliceRefU child) (Set.singleton child) children)
    addChildToRoot (Just (Segment.ChildOf _)) = error "[ panic ] relateRootToSegment: the root already has a parent"
    addChildToRoot (Just (Segment.Constant _)) = error "[ panic ] relateRootToSegment: the root already has a value"
    addChildToRoot (Just (Segment.Free _)) = Segment.ParentOf (widthOf root) (Map.singleton (sliceRefU child) (Set.singleton child))

    modifySegment :: (Maybe Segment -> Segment) -> Slice -> M ()
    modifySegment f (Slice ref start end) =
      modify $
        modifyRefUSegments
          ref
          (RefUSegments.fromSegment (Slice ref start end) (f Nothing)) -- what to do if the RefUSegments does not exist
          (RefUSegments.mapInterval (f . Just) (start, end))

relateRootToFamily :: Slice -> FamilyLookup -> M ()
relateRootToFamily _ (FamilyLookup []) = return ()
relateRootToFamily root (FamilyLookup ([] : xss)) = do
  relateRootToFamily root (FamilyLookup xss)
relateRootToFamily root (FamilyLookup ((x : xs) : xss)) = do
  let (root1, root2) = Slice.split (widthOf x) root
  mapM_ (relateRootToSegment root1) (x : xs)
  relateRootToFamily root2 (FamilyLookup xss)

--------------------------------------------------------------------------------

-- | Internal data structure for storing RefUSegments
newtype Mapping = Mapping {unMapping :: IntMap (IntMap RefUSegments)}
  deriving (Eq, Generic)

instance NFData Mapping

instance Show Mapping where
  show = indent . mconcat . map showVarMap . IntMap.elems . unMapping
    where
      showVarMap :: IntMap RefUSegments -> String
      showVarMap varMap =
        if IntMap.null varMap
          then ""
          else unlines (IntMap.elems varMap >>= RefUSegments.formatRefUSegments)

-- | Given a RefU, modify the RefUSegments referenced by the RefU
--   Insert a new RefUSegments if it does not exist
modifyRefUSegments :: RefU -> RefUSegments -> (RefUSegments -> RefUSegments) -> SliceRelations -> SliceRelations
modifyRefUSegments ref e f relations = case ref of
  RefUO width _ -> relations {srRefO = Mapping (IntMap.alter alterRefUSegmentsMap width (unMapping (srRefO relations)))}
  RefUI width _ -> relations {srRefI = Mapping (IntMap.alter alterRefUSegmentsMap width (unMapping (srRefI relations)))}
  RefUP width _ -> relations {srRefP = Mapping (IntMap.alter alterRefUSegmentsMap width (unMapping (srRefP relations)))}
  RefUX width _ -> relations {srRefX = Mapping (IntMap.alter alterRefUSegmentsMap width (unMapping (srRefX relations)))}
  where
    alterRefUSegmentsMap :: Maybe (IntMap RefUSegments) -> Maybe (IntMap RefUSegments)
    alterRefUSegmentsMap Nothing = Just (IntMap.singleton (refUVar ref) e) -- insert a new RefUSegments if it does not exist
    alterRefUSegmentsMap (Just x) = Just (IntMap.alter alterRefUSegments (refUVar ref) x)

    alterRefUSegments :: Maybe RefUSegments -> Maybe RefUSegments
    alterRefUSegments Nothing = Just e -- insert a new RefUSegments if it does not exist
    alterRefUSegments (Just x) = Just (f x)

-- | Convert a SliceRelations to a list of SliceSegmentPairs
segmentsToPairs :: PartialRefUSegments -> [SliceSegmentPair]
segmentsToPairs (PartialRefUSegments slice segments) = map (\(offset, segment) -> (Slice (Slice.sliceRefU slice) offset (offset + widthOf segment), segment)) (IntMap.toList segments)

--------------------------------------------------------------------------------

-- | The equivalence class version of RefUSegments
newtype FamilyLookup = FamilyLookup [[Slice]] -- the equivalence class of each segment
  deriving (Eq, Show)

-- | Given a Slice and its corresponding Segment, return all member Slices of the equivalence class of that Slice
--   so that we can, for example, assign a value to all members of the equivalence class
--   or relate them to another Slice
familySlicesOfSliceSegmentPair :: SliceRelations -> SliceSegmentPair -> [Slice]
familySlicesOfSliceSegmentPair relations (slice, segment) = case segment of
  Segment.Constant _ -> []
  Segment.ChildOf root ->
    let PartialRefUSegments _ segments = lookup root relations
     in case IntMap.elems segments of
          [] -> error "[ panic ] getFamily: ChildOf root has no segments"
          [Segment.ParentOf _ children] -> root : Set.toList (Set.unions (Map.elems children))
          [_] -> error "[ panic ] getFamily: Should be ParentOf"
          _ -> error "[ panic ] getFamily: ChildOf root has more than one segment"
  Segment.ParentOf _ children -> slice : Set.toList (Set.unions (Map.elems children))
  Segment.Free _ -> [slice]

lookupFamilyWithSlice :: Slice -> SliceRelations -> FamilyLookup
lookupFamilyWithSlice slice relations =
  let pairs = segmentsToPairs $ lookup slice relations
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

-- | Given 2 RefUSegments of the same lengths, generate pairs of aligned segments (indexed with their offsets).
--   Such that the boundaries of the generated segments pairs are the union of the boundaries of the two segments.
--   Example:
--      slice 1      ├─────B─────┼──A──┤
--      slice 2      ├──A──┼─────C─────┤
--                          =>
--      pairs        ├──B──┼──B──┼──A──┤
--      pairs        ├──A──┼──C──┼──C──┤
toAlignedSegmentPairs :: PartialRefUSegments -> PartialRefUSegments -> [(SliceSegmentPair, SliceSegmentPair)]
toAlignedSegmentPairs (PartialRefUSegments (Slice ref1 _ _) segments1) (PartialRefUSegments (Slice ref2 _ _) segments2) =
  step (IntMap.toList segments1) (IntMap.toList segments2)
  where
    step :: [(Int, Segment)] -> [(Int, Segment)] -> [(SliceSegmentPair, SliceSegmentPair)]
    step ((index1, segment1) : xs1) ((index2, segment2) : xs2) =
      let width1 = widthOf segment1
          width2 = widthOf segment2
       in case width1 `compare` width2 of
            EQ ->
              ( (Slice ref1 index1 (index1 + width1), segment1),
                (Slice ref2 index2 (index2 + width2), segment2)
              )
                : step xs1 xs2
            LT ->
              -- segment1 is shorter, so we split segment2 into two
              let (segment21, segment22) = Segment.unsafeSplit width1 segment2
               in ( (Slice ref1 index1 (index1 + width1), segment1),
                    (Slice ref2 index2 (index2 + widthOf segment21), segment21)
                  )
                    : step xs1 ((index2 + width1, segment22) : xs2)
            GT ->
              -- segment2 is shorter, so we split segment1 into two
              let (segment11, segment12) = Segment.unsafeSplit width2 segment1
               in ( (Slice ref1 index1 (index1 + widthOf segment11), segment11),
                    (Slice ref2 index2 (index2 + width2), segment2)
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
      Segment.Constant _ -> kinship
      Segment.ChildOf root ->
        -- make `slice` a child of `root`
        -- make `root` the parent of `slice`
        Kinship
          { kinshipParents = Map.alter (insertChildToParent slice root) (sliceRefU root) (kinshipParents kinship),
            kinshipChildren = Map.alter (insertParentToChild root slice) (sliceRefU slice) (kinshipChildren kinship)
          }
      Segment.ParentOf {} -> kinship
      Segment.Free _ -> kinship

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
      Segment.Constant _ -> kinship
      Segment.ChildOf _ -> kinship
      Segment.ParentOf _ children ->
        Kinship
          { kinshipParents = Map.alter removeChildFromParent (sliceRefU slice) (kinshipParents kinship),
            kinshipChildren = foldl removeParentFromChild (kinshipChildren kinship) (Set.toList (Set.unions (Map.elems children)))
          }
      Segment.Free _ -> kinship

    removeChildFromParent :: Maybe (IntMap [Slice]) -> Maybe (IntMap [Slice])
    removeChildFromParent _ = Nothing

    removeParentFromChild :: Map RefU (IntMap Slice) -> Slice -> Map RefU (IntMap Slice)
    removeParentFromChild allChildren child = Map.alter (removeParentFromChild' child) (sliceRefU child) allChildren

    removeParentFromChild' :: Slice -> Maybe (IntMap Slice) -> Maybe (IntMap Slice)
    removeParentFromChild' _ Nothing = Nothing
    removeParentFromChild' child (Just slices) = Just (IntMap.delete (sliceStart child) slices)