{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use list comprehension" #-}

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
import Data.Maybe qualified as Maybe
import Data.Set (Set)
import Data.Set qualified as Set
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
    foldSliceLookup a (SliceLookup slice segments) = foldl (\b (index, segment) -> f b (Slice (sliceRefU slice) index (widthOf segment)) segment) a (IntMap.toList segments)

-- | FOR TESTING: A SliceRelations is valid if:
--    1. all existing SliceLookups cover the entire width of the variable
--    2. all children of a Parent Segment has the parent as its root
isValid :: SliceRelations -> Bool
isValid relations = all isValidMapping [refO, refI, refP, refX] && hasCorrectKinship
  where
    SliceRelations refO refI refP refX = relations

    isValidMapping :: Mapping -> Bool
    isValidMapping (Mapping xs) = all (all isValidSliceLookup) xs

    isValidSliceLookup :: SliceLookup -> Bool
    isValidSliceLookup x@(SliceLookup slice _) = sliceStart slice == 0 && sliceEnd slice == widthOf (sliceRefU slice) && SliceLookup.isValid x

    hasCorrectKinship :: Bool
    hasCorrectKinship = Maybe.isNothing $ invalidKinship (kinshipFromSliceRelations relations)

--------------------------------------------------------------------------------

data Failure
  = InvalidSliceLookupNotCoveringAll SliceLookup
  | InvalidSliceLookup SliceLookup.Failure
  | InvalidKinship Kinship
  deriving (Eq, Show)

collectFailure :: SliceRelations -> [Failure]
collectFailure relations = isInvalidKinship <> invalidMapping
  where
    SliceRelations refO refI refP refX = relations

    invalidMapping = mconcat (map isValidMapping [refO, refI, refP, refX])

    isValidMapping :: Mapping -> [Failure]
    isValidMapping (Mapping xs) = mconcat $ map (mconcat . map isValidSliceLookup . IntMap.elems) (IntMap.elems xs)

    isValidSliceLookup :: SliceLookup -> [Failure]
    isValidSliceLookup x =
      if isCoveringAll x
        then map InvalidSliceLookup (SliceLookup.collectFailure False x)
        else [InvalidSliceLookupNotCoveringAll x]

    isCoveringAll :: SliceLookup -> Bool
    isCoveringAll (SliceLookup slice _) = sliceStart slice == 0 && sliceEnd slice == widthOf (sliceRefU slice)

    isInvalidKinship :: [Failure]
    isInvalidKinship = case invalidKinship (kinshipFromSliceRelations relations) of
      Nothing -> []
      Just x -> [InvalidKinship x]

--------------------------------------------------------------------------------

relate :: Slice -> Slice -> SliceRelations -> SliceRelations
relate child root relations =
  let childLookup = lookup child relations
      rootLookup = lookup root relations
      pairs = toAlignedSegmentPairs childLookup rootLookup
   in execState (mapM_ relateSegment pairs) relations

type M = State SliceRelations

getFamilyM :: Slice -> M [Slice]
getFamilyM = gets . getFamily

-- getRoot :: Slice -> M Slice
-- getRoot slice = do
--   relations <- get
--   pure (head family)

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
  modify (modifySegment addRootToChild child)
  modify (modifySegment addChildToRoot root)
  where
    -- modify root

    addRootToChild :: Maybe Segment -> Segment
    addRootToChild _ = SliceLookup.ChildOf root

    addChildToRoot :: Maybe Segment -> Segment
    addChildToRoot Nothing = SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) child) mempty
    addChildToRoot (Just (SliceLookup.Parent width children self)) = 
      if sliceRefU root == sliceRefU child -- see if the child is the root itself
        then SliceLookup.Parent width (Map.insert (sliceRefU child) child children) (IntMap.insert (sliceStart child) child self)
        else SliceLookup.Parent width (Map.insert (sliceRefU child) child children) self
    addChildToRoot (Just (SliceLookup.ChildOf anotherRoot)) =
      if sliceRefU root == sliceRefU anotherRoot
        then -- "root" has self reference to itself
             -- convert it to a Parent node
           SliceLookup.Parent (widthOf root) mempty (IntMap.singleton (sliceStart child) child)
        else error "[ panic ] assignRootSegment: child already has a parent"
    addChildToRoot (Just (SliceLookup.Constant _)) = error "[ panic ] assignRootSegment: child already has a value"
    addChildToRoot (Just (SliceLookup.Empty _)) = SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) child) mempty

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

-- (SliceLookup.Constant val1, SliceLookup.ChildOf root2) -> assignMapping slice2 val1 (relateMapping slice2 root2 relations)
-- (SliceLookup.Constant val1, SliceLookup.Parent _ children2) -> assignMapping slice2 val1 (foldr (\child -> relateMapping child slice2) relations (Map.elems children2))
-- (SliceLookup.ChildOf root1, SliceLookup.Constant val2) -> assignMapping slice1 val2 (relateMapping slice1 root1 relations)
-- (SliceLookup.ChildOf root1, SliceLookup.ChildOf root2) ->
--   -- see who's root is the real boss
--   if root1 > root2
--     then -- root1 is the boss

--       relateMapping root2 root1 relations
--     else -- root2 is the boss

--       relateMapping root1 root2 relations
-- (SliceLookup.ChildOf root1, SliceLookup.Parent _ children2) ->
--   if root1 > slice2
--     then foldr (\child -> relateMapping child root1) relations (Map.elems children2)
--     else relateMapping root1 slice2 relations
-- (SliceLookup.Parent _ children1, SliceLookup.Constant val2) -> foldr (\child -> assignMapping child val2) relations (Map.elems children1)
-- (SliceLookup.Parent _ children1, SliceLookup.ChildOf root2) ->
--   if slice1 > root2
--     then relateMapping slice1 root2 relations -- slice1 is the boss
--     else foldr (\child -> relateMapping child root2) relations (Map.elems children1) -- root2 is the boss
-- (SliceLookup.Parent _ children1, SliceLookup.Parent _ children2) ->
--   if slice1 > slice2
--     then foldr (\child -> relateMapping child slice1) relations (Map.elems children2) -- slice1 is the boss
--     else foldr (\child -> relateMapping child slice2) relations (Map.elems children1) -- slice2 is the boss

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

-- | Assign a value to a slice of a variable
-- modifySliceLookup :: (Maybe SliceLookup -> Maybe SliceLookup) -> Slice -> Mapping -> Mapping

-- assignMapping :: Slice -> U -> Mapping -> Mapping
-- assignMapping slice val = modifySliceLookup assignSliceLookup slice
--   where
--     assignSliceLookup :: Maybe SliceLookup -> Maybe SliceLookup
--     assignSliceLookup Nothing = Just (SliceLookup.fromSegment slice (SliceLookup.Constant val))
--     assignSliceLookup (Just lookups) = Just (SliceLookup.mapInterval assignSegment (sliceStart slice, sliceEnd slice) lookups)

--     assignSegment :: Segment -> Segment
--     assignSegment (SliceLookup.Constant _) = error "assignSegment: assigning on existing Constant"
--     assignSegment (SliceLookup.ChildOf root) = _
--     assignSegment (SliceLookup.Parent _ children) = _
--     assignSegment (SliceLookup.Empty _) = error "assignSegment: assigning on existing Empty"

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

-- -- | Relate a child Slice with a parent Slice
-- relateMapping :: Slice -> Slice -> Mapping -> Mapping
-- relateMapping child root = modifySliceLookupMapping modifyRoot root . modifySliceLookupMapping modifyChild child
--   where
--     -- modify existing child SliceLookup
--     modifyChild :: Maybe SliceLookup -> Maybe SliceLookup
--     modifyChild Nothing = Just (SliceLookup.fromSegment child (SliceLookup.ChildOf root)) -- creates a new SliceLookup from "ChildOf root"
--     modifyChild (Just lookups) = Just (SliceLookup.mapInterval (const (SliceLookup.ChildOf root)) (sliceStart child, sliceEnd child) lookups)

--     -- modify existing root SliceLookup
--     modifyRoot :: Maybe SliceLookup -> Maybe SliceLookup
--     modifyRoot Nothing = Just (SliceLookup.fromSegment root (SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) child))) -- creates a new SliceLookup
--     modifyRoot (Just lookups) = Just (SliceLookup.mapInterval (const (SliceLookup.Parent (widthOf root) (Map.singleton (sliceRefU child) child))) (sliceStart root, sliceEnd root) lookups)

-- modifySliceLookupMapping :: (Maybe SliceLookup -> Maybe SliceLookup) -> Slice -> Mapping -> Mapping
-- modifySliceLookupMapping f slice (Mapping xs) = Mapping (IntMap.alter alterVarMap width xs)
--   where
--     width :: Width
--     width = widthOf (sliceRefU slice)

--     var :: Var
--     var = refUVar (sliceRefU slice)

--     alterVarMap :: Maybe (IntMap SliceLookup) -> Maybe (IntMap SliceLookup)
--     alterVarMap Nothing = f Nothing >>= \lookups -> pure (IntMap.singleton 0 (SliceLookup.pad lookups))
--     alterVarMap (Just varMap) = Just $ IntMap.alter f var varMap

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
    go (SliceLookup.Parent _ children _) = slice : Map.elems children
    go (SliceLookup.Empty _) = [slice]

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
              ( (Slice (sliceRefU slice1) index1 (index1 + width1), segment1),
                (Slice (sliceRefU slice2) index2 (index2 + width2), segment2)
              )
                : step xs1 xs2
            LT ->
              -- segment1 is shorter, so we split segment2 into two
              let (segment21, segment22) = SliceLookup.splitSegment width1 segment2
               in ( (Slice (sliceRefU slice1) index1 (index1 + width1), segment1),
                    (Slice (sliceRefU slice2) index2 (index2 + widthOf segment21), segment21)
                  )
                    : step xs1 ((index2 + width1, segment22) : xs2)
            GT ->
              -- segment2 is shorter, so we split segment1 into two
              let (segment11, segment12) = SliceLookup.splitSegment width2 segment1
               in ( (Slice (sliceRefU slice1) index1 (index1 + widthOf segment11), segment11),
                    (Slice (sliceRefU slice2) index2 (index2 + width2), segment2)
                  )
                    : step ((index1 + width2, segment12) : xs1) xs2
    step _ _ = []

--------------------------------------------------------------------------------

-- | Data structure for testing the relationship between parent and children
data Kinship = Kinship
  { kinshipParents :: Map Slice (Set Slice), -- each parent has a set of children
    kinshipChildren ::
      Map -- each child has a parent
        Slice -- child
        Slice -- parent
  }
  deriving (Eq)

instance Show Kinship where
  show (Kinship parents children) =
    if Map.null parents && Map.null children
      then "Kinship {}"
      else
        "Kinship {\n"
          <> showParents
          <> showChildren
          <> "}"
    where
      showParents :: String
      showParents =
        "  parents: {\n"
          <> unlines (map (\(parent, x) -> "    " <> show parent <> ": " <> show (Set.toList x)) (Map.toList parents))
          <> "  }\n"

      showChildren :: String
      showChildren =
        "  children: {\n"
          <> unlines (map (\(child, parent) -> "    " <> show child <> ": " <> show parent) (Map.toList children))
          <> "  }\n"

-- | A Kinship is valid if after removing all children, it is empty
invalidKinship :: Kinship -> Maybe Kinship
invalidKinship = nullKinship . removeAllChildren
  where
    -- pick a child and remove its existence from the Kinship
    removeChild :: Kinship -> Kinship
    removeChild (Kinship parents children) = case Map.lookupMax children of
      Nothing -> Kinship parents children
      Just (child, parent) -> Kinship (Map.adjust (Set.delete child) parent parents) (Map.delete child children)

    -- the fixed point of 'removeChild'
    removeAllChildren :: Kinship -> Kinship
    removeAllChildren xs =
      let xs' = removeChild xs
       in if xs' == xs
            then xs
            else removeAllChildren xs'

    -- return Nothing if the Kinship is valid, otherwise return the invalid Kinship
    nullKinship :: Kinship -> Maybe Kinship
    nullKinship (Kinship parents children) =
      if all Set.null (Map.elems parents) && Map.null children
        then Nothing
        else Just (Kinship parents children)

-- | Add a relationship between a child and a parent to the Kinship
kinshipFromSliceRelations :: SliceRelations -> Kinship
kinshipFromSliceRelations = fold addRelation (Kinship Map.empty Map.empty)
  where
    addRelation :: Kinship -> Slice -> Segment -> Kinship
    addRelation kinship slice segment = case segment of
      SliceLookup.Constant _ -> kinship
      SliceLookup.ChildOf root ->
        Kinship
          { kinshipParents = Map.insertWith Set.union root (Set.singleton slice) (kinshipParents kinship),
            kinshipChildren = Map.insert slice root (kinshipChildren kinship)
          }
      SliceLookup.Parent _ children _ ->
        Kinship
          { kinshipParents = Map.insertWith Set.union slice (Set.fromList $ Map.elems children) (kinshipParents kinship),
            kinshipChildren = Map.union (kinshipChildren kinship) $ Map.fromList $ map (,slice) (Map.elems children)
          }
      SliceLookup.Empty _ -> kinship