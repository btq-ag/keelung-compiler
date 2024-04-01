module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung (widthOf)
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Relations (Relations)
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Slice (SliceRelations)
import Keelung.Compiler.Relations.Slice qualified as SliceRelations
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.SliceLookup (SliceLookup (..))
import Keelung.Data.U (U)
import qualified Keelung.Data.Segment as Segment

-- | Order of optimization, if any of the former optimization pass changed the constraint system,
-- the later optimization pass will be run again at that level
--
--  Passes are run in the following order:
--    1. AddF
--    2. AddL
--    3. MulF
--    4. MulL
--    5. DivMods
--    6. ModInvs
--    7. EqZeros
run :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (ConstraintModule n)
run cm = do
  cm' <- runStateMachine cm ShouldRunAddL
  return $ goThroughModInvs cm'

-- | Next optimization pass to run
data Action
  = Accept
  | ShouldRunAddL
  | ShouldRunMulL
  | ShouldRunDivMod
  | ShouldRunCLDivMod
  deriving (Eq, Show)

-- | Decide what to do next based on the result of the previous optimization pass
transition :: WhatChanged -> Action -> Action
transition _ Accept = Accept
transition NothingChanged ShouldRunAddL = ShouldRunMulL
transition NothingChanged ShouldRunMulL = ShouldRunDivMod
transition NothingChanged ShouldRunDivMod = ShouldRunCLDivMod
transition NothingChanged ShouldRunCLDivMod = Accept
transition RelationChanged _ = ShouldRunAddL -- restart from optimizeAddF
transition AdditiveFieldConstraintChanged _ = ShouldRunAddL -- restart from optimizeAddL
transition AdditiveLimbConstraintChanged _ = ShouldRunMulL -- restart from optimizeMulL
transition MultiplicativeConstraintChanged _ = ShouldRunMulL -- restart from optimizeMulL
transition MultiplicativeLimbConstraintChanged _ = ShouldRunMulL -- restart from optimizeMulL

-- | Run the state machine until it reaches the 'Accept' state
runStateMachine :: (GaloisField n, Integral n) => ConstraintModule n -> Action -> Either (Compile.Error n) (ConstraintModule n)
runStateMachine cm action = do
  -- decide which optimization pass to run and see if it changed anything
  (changed, cm') <- case action of
    Accept -> return (NothingChanged, cm)
    ShouldRunAddL -> optimizeAddL cm
    ShouldRunMulL -> optimizeMulL cm
    ShouldRunDivMod -> optimizeDivMod cm
    ShouldRunCLDivMod -> optimizeCLDivMod cm
  -- derive the next action based on the result of the previous optimization pass
  let action' = transition changed action
  -- keep running the state machine until it reaches the 'Accept' state
  if action' == Accept
    then return cm'
    else runStateMachine cm' action'

------------------------------------------------------------------------------

-- optimizeAddF :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
-- optimizeAddF cm = runOptiM cm $ runRoundM $ do
--   result <- foldMaybeM reduceAddF [] (cmAddF cm)
--   modify' $ \cm' -> cm' {cmAddF = result}

optimizeAddL :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeAddL cm = runOptiM cm $ runRoundM $ do
  result <- foldMaybeM reduceAddL mempty (cmAddL cm)
  modify' $ \cm' -> cm' {cmAddL = result}

optimizeMulL :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeMulL cm = runOptiM cm $ runRoundM $ do
  cmMulL' <- foldMaybeM reduceMulL mempty (cmMulL cm)
  modify' $ \cm' -> cm' {cmMulL = cmMulL'}

optimizeDivMod :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeDivMod cm = runOptiM cm $ runRoundM $ do
  result <- foldMaybeM reduceDivMod mempty (cmDivMods cm)
  modify' $ \cm' -> cm' {cmDivMods = result}

optimizeCLDivMod :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeCLDivMod cm = runOptiM cm $ runRoundM $ do
  result <- foldMaybeM reduceDivMod mempty (cmCLDivMods cm)
  modify' $ \cm' -> cm' {cmCLDivMods = result}

goThroughModInvs :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughModInvs cm =
  let substModInv (a, b, c, d) = (a, b, c, d)
   in cm {cmModInvs = fmap substModInv (cmModInvs cm)}

foldMaybeM :: (Monad m) => (a -> m (Maybe a)) -> Seq a -> Seq a -> m (Seq a)
foldMaybeM f = foldM $ \acc x -> do
  result <- f x
  case result of
    Nothing -> return acc
    Just x' -> return (x' Seq.<| acc)

------------------------------------------------------------------------------

-- | Trying to reduce an additive field constraint, returns Nothing if it cannot be reduced
reduceAddL :: (GaloisField n, Integral n) => PolyL n -> RoundM n (Maybe (PolyL n))
reduceAddL polynomial = do
  relations <- gets cmRelations
  case substPolyL relations polynomial of
    Nothing -> do
      reduced <- learnFromAddL polynomial -- learn from the polynomial
      if reduced
        then return Nothing -- polynomial has been reduced to nothing
        else return (Just polynomial) -- nothing changed
    Just (Left constant, changes) -> do
      when (constant /= 0) $ error "[ panic ] Additive reduced to some constant other than 0"
      -- the polynomial has been reduced to nothing
      markChanged AdditiveLimbConstraintChanged
      -- remove all variables in the polynomial from the occurrence list
      applyChanges changes
      return Nothing
    Just (Right substitutedPolynomial, changes) -> do
      -- the polynomial has been reduced to something
      markChanged AdditiveLimbConstraintChanged
      -- remove variables that has been reduced in the polynomial from the occurrence list
      applyChanges changes
      -- learn from the substituted Polynomial
      reduced <- learnFromAddL substitutedPolynomial
      if reduced
        then return Nothing -- polynomial has been reduced to nothing
        else -- keep substituting the substituted polynomial
          reduceAddL substitutedPolynomial

------------------------------------------------------------------------------

type MulL n = (PolyL n, PolyL n, Either n (PolyL n))

reduceMulL :: (GaloisField n, Integral n) => MulL n -> RoundM n (Maybe (MulL n))
reduceMulL (polyA, polyB, polyC) = do
  polyAResult <- substitutePolyL MultiplicativeLimbConstraintChanged polyA
  polyBResult <- substitutePolyL MultiplicativeLimbConstraintChanged polyB
  polyCResult <- case polyC of
    Left constantC -> return (Left constantC)
    Right polyC' -> substitutePolyL MultiplicativeLimbConstraintChanged polyC'
  reduceMulL_ polyAResult polyBResult polyCResult

-- | Substitutes Refs & Limbs in a polynomial and returns the reduced polynomial if it is reduced
substitutePolyL :: (GaloisField n, Integral n) => WhatChanged -> PolyL n -> RoundM n (Either n (PolyL n))
substitutePolyL typeOfChange polynomial = do
  relations <- gets cmRelations
  case substPolyL relations polynomial of
    Nothing -> return (Right polynomial) -- nothing changed
    Just (Left constant, changes) -> do
      -- the polynomial has been reduced to nothing
      markChanged typeOfChange
      -- remove all referenced RefUs in the Limbs of the polynomial from the occurrence list
      applyChanges changes
      return (Left constant)
    Just (Right reducePolynomial, changes) -> do
      -- the polynomial has been reduced to something
      markChanged typeOfChange
      -- remove all referenced RefUs in the Limbs of the polynomial from the occurrence list and add the new ones
      applyChanges changes
      return (Right reducePolynomial)

-- | Trying to reduce a multiplicative limb constaint, returns the reduced constraint if it is reduced
reduceMulL_ :: (GaloisField n, Integral n) => Either n (PolyL n) -> Either n (PolyL n) -> Either n (PolyL n) -> RoundM n (Maybe (MulL n))
reduceMulL_ polyA polyB polyC = case (polyA, polyB, polyC) of
  (Left _a, Left _b, Left _c) -> return Nothing
  (Left a, Left b, Right c) -> reduceMulLCCP a b c >> return Nothing
  (Left a, Right b, Left c) -> reduceMulLCPC a b c >> return Nothing
  (Left a, Right b, Right c) -> reduceMulLCPP a b c >> return Nothing
  (Right a, Left b, Left c) -> reduceMulLCPC b a c >> return Nothing
  (Right a, Left b, Right c) -> reduceMulLCPP b a c >> return Nothing
  (Right a, Right b, Left c) -> return (Just (a, b, Left c))
  (Right a, Right b, Right c) -> return (Just (a, b, Right c))

-- | Trying to reduce a multiplicative limb constaint of (Constant / Constant / Polynomial)
--    a * b = cm
--      =>
--    cm - a * b = 0
reduceMulLCCP :: (GaloisField n, Integral n) => n -> n -> PolyL n -> RoundM n ()
reduceMulLCCP a b cm = addAddL $ PolyL.addConstant (-a * b) cm

-- | Trying to reduce a multiplicative limb constaint of (Constant / Polynomial / Constant)
--    a * bs = c
--      =>
--    c - a * bs = 0
reduceMulLCPC :: (GaloisField n, Integral n) => n -> PolyL n -> n -> RoundM n ()
reduceMulLCPC a bs c = case PolyL.multiplyBy (-a) bs of
  Left constant ->
    if constant == c
      then modify' $ removeOccurrence bs
      else throwError $ Compile.ConflictingValuesF constant c
  Right xs -> addAddL $ PolyL.addConstant c xs

-- | Trying to reduce a multiplicative limb constaint of (Constant / Polynomial / Polynomial)
--    a * bs = cm
--      =>
--    cm - a * bs = 0
reduceMulLCPP :: (GaloisField n, Integral n) => n -> PolyL n -> PolyL n -> RoundM n ()
reduceMulLCPP a polyB polyC = case PolyL.multiplyBy (-a) polyB of
  Left constant ->
    if constant == 0
      then do
        -- a * bs = 0
        -- cm = 0
        modify' $ removeOccurrence polyB
        addAddL polyC
      else do
        -- a * bs = constant = cm
        -- => cm - constant = 0
        modify' $ removeOccurrence polyB
        addAddL (PolyL.addConstant (-constant) polyC)
  Right polyBa -> case PolyL.merge polyC polyBa of
    Left _ -> return ()
    Right poly -> addAddL poly

------------------------------------------------------------------------------

type DivMod = (Either RefU U, Either RefU U, Either RefU U, Either RefU U)

-- | Subsitute variables in polynomials of DivMod with their corresponding values or roots
reduceDivMod :: (GaloisField n, Integral n) => DivMod -> RoundM n (Maybe DivMod)
reduceDivMod (a, b, q, r) = do
  relationsS <- gets (Relations.relationsS . cmRelations)
  return $
    Just
      ( go relationsS a,
        go relationsS b,
        go relationsS q,
        go relationsS r
      )
  where
    go :: SliceRelations -> Either RefU U -> Either RefU U
    go _ (Right val) = Right val
    go relations (Left var) =
      let SliceLookup _ segments = SliceRelations.lookup (Slice.fromRefU var) relations
       in case IntMap.elems segments of
            [Segment.ChildOf root] -> Left (Slice.sliceRefU root)
            [Segment.Constant value] -> Right value
            [Segment.Parent _ _] -> Left var
            [Segment.Free _] -> Left var
            _ -> Left var

------------------------------------------------------------------------------

data WhatChanged
  = NothingChanged
  | RelationChanged
  | AdditiveFieldConstraintChanged
  | AdditiveLimbConstraintChanged
  | MultiplicativeConstraintChanged
  | MultiplicativeLimbConstraintChanged
  deriving (Eq, Show)

instance Semigroup WhatChanged where
  NothingChanged <> x = x
  x <> NothingChanged = x
  RelationChanged <> _ = RelationChanged
  _ <> RelationChanged = RelationChanged
  AdditiveFieldConstraintChanged <> _ = AdditiveFieldConstraintChanged
  _ <> AdditiveFieldConstraintChanged = AdditiveFieldConstraintChanged
  AdditiveLimbConstraintChanged <> _ = AdditiveLimbConstraintChanged
  _ <> AdditiveLimbConstraintChanged = AdditiveLimbConstraintChanged
  MultiplicativeConstraintChanged <> _ = MultiplicativeConstraintChanged
  _ <> MultiplicativeConstraintChanged = MultiplicativeConstraintChanged
  MultiplicativeLimbConstraintChanged <> _ = MultiplicativeLimbConstraintChanged

instance Monoid WhatChanged where
  mempty = NothingChanged

------------------------------------------------------------------------------

type OptiM n = StateT (ConstraintModule n) (Except (Compile.Error n))

type RoundM n = WriterT WhatChanged (OptiM n)

runOptiM :: ConstraintModule n -> OptiM n a -> Either (Compile.Error n) (a, ConstraintModule n)
runOptiM cm m = runExcept (runStateT m cm)

runRoundM :: RoundM n a -> OptiM n WhatChanged
runRoundM = execWriterT

markChanged :: WhatChanged -> RoundM n ()
markChanged = tell

-- | Go through additive constraints and classify them into relation constraints when possible.
--   Returns 'True' if the constraint has been reduced.
learnFromAddL :: (GaloisField n, Integral n) => PolyL n -> RoundM n Bool
learnFromAddL poly = case PolyL.view poly of
  PolyL.RefMonomial intercept (var, slope) -> do
    --    intercept + slope * var = 0
    --  =>
    --    var = - intercept / slope
    assign var (-intercept / slope)
    return True
  PolyL.RefBinomial intercept (var1, slope1) (var2, slope2) -> do
    --    intercept + slope1 * var1 + slope2 * var2 = 0
    --  =>
    --    slope1 * var1 = - slope2 * var2 - intercept
    --  =>
    --    var1 = - slope2 * var2 / slope1 - intercept / slope1
    relateF var1 (-slope2 / slope1, var2, -intercept / slope1)
  PolyL.RefPolynomial _ _ -> return False
  PolyL.SliceMonomial constant (slice1, multiplier1) -> do
    --  constant + slice1 * multiplier1  = 0
    --    =>
    --  slice1 = - constant / multiplier1
    assignS slice1 (toInteger (-constant / multiplier1))
    return True
  PolyL.SliceBinomial constant (slice1, multiplier1) (slice2, multiplier2) -> do
    if constant == 0 && multiplier1 == -multiplier2
      then do
        --  slice1 * multiplier1 = slice2 * multiplier2
        relateS slice1 slice2
      else return False
  PolyL.SlicePolynomial {} -> return False
  PolyL.MixedPolynomial {} -> return False

assign :: (GaloisField n, Integral n) => Ref -> n -> RoundM n ()
assign (B var) value = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ Relations.assignB var (value == 1) (cmRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmRelations = relations}
assign (F var) value = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ Relations.assignR (F var) value (cmRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmRelations = relations}

assignS :: (GaloisField n, Integral n) => Slice -> Integer -> RoundM n ()
assignS slice value = do
  cm <- get
  result <-
    lift $
      lift $
        EquivClass.runM $
          Relations.assignS slice value (cmRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton slice) $ cm {cmRelations = relations}

-- | Relates two variables. Returns 'True' if a new relation has been established.
relateF :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> RoundM n Bool
relateF var1 (slope, var2, intercept) = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ Relations.relateR var1 slope var2 intercept (cmRelations cm)
  case result of
    Nothing -> return False
    Just relations -> do
      markChanged RelationChanged
      modify' $ \cm' -> removeOccurrences (Set.fromList [var1, var2]) $ cm' {cmRelations = relations}
      return True

-- | Relates two Slices. Returns 'True' if a new relation has been established.
relateS :: (GaloisField n, Integral n) => Slice -> Slice -> RoundM n Bool
relateS slice1 slice2 = do
  cm <- get
  result <-
    lift $
      lift $
        EquivClass.runM $
          Relations.relateS slice1 slice2 (cmRelations cm)
  case result of
    Nothing -> return False
    Just relations -> do
      markChanged RelationChanged
      modify' $ \cm' -> removeOccurrences (Set.fromList [slice1, slice2]) $ cm' {cmRelations = relations}
      return True

--------------------------------------------------------------------------------

-- | Add learned additive constraints to the pool
addAddL :: (GaloisField n, Integral n) => PolyL n -> RoundM n ()
addAddL poly = case PolyL.view poly of
  PolyL.RefMonomial constant (var1, coeff1) -> do
    --    constant + coeff1 * var1 = 0
    --      =>
    --    var1 = - constant / coeff1
    assign var1 (-constant / coeff1)
  PolyL.RefBinomial constant (var1, coeff1) (var2, coeff2) -> do
    --    constant + coeff1 * var1 + coeff2 * var2 = 0
    --      =>
    --    coeff1 * var1 = - coeff2 * var2 - constant
    --      =>
    --    var1 = - coeff2 * var2 / coeff1 - constant / coeff1
    void $ relateF var1 (-coeff2 / coeff1, var2, -constant / coeff1)
  PolyL.RefPolynomial _ _ -> do
    markChanged AdditiveFieldConstraintChanged
    modify' $ \cm' -> cm' {cmAddL = poly Seq.<| cmAddL cm'}
  PolyL.SliceMonomial constant (slice1, multiplier1) -> do
    --  constant + slice1 * multiplier1  = 0
    --    =>
    --  slice1 = - constant / multiplier1
    assignS slice1 (toInteger (-constant / multiplier1))
  PolyL.SliceBinomial constant (slice1, multiplier1) (slice2, multiplier2) -> do
    if constant == 0 && multiplier1 == -multiplier2
      then do
        --  slice1 * multiplier1 = slice2 * multiplier2
        void $ relateS slice1 slice2
      else do
        markChanged AdditiveLimbConstraintChanged
        modify' $ \cm' -> cm' {cmAddL = poly Seq.<| cmAddL cm'}
  PolyL.SlicePolynomial {} -> do
    markChanged AdditiveLimbConstraintChanged
    modify' $ \cm' -> cm' {cmAddL = poly Seq.<| cmAddL cm'}
  PolyL.MixedPolynomial {} -> do
    markChanged AdditiveFieldConstraintChanged
    modify' $ \cm' -> cm' {cmAddL = poly Seq.<| cmAddL cm'}

--------------------------------------------------------------------------------

-- | Keep track of what has been changed in the substitution
data Changes = Changes
  { addedSlices :: Set Slice,
    removedSlices :: Set Slice,
    addedRefs :: Set Ref,
    removedRefs :: Set Ref
  }
  deriving (Eq, Show)

applyChanges :: (GaloisField n, Integral n) => Changes -> RoundM n ()
applyChanges changes = modify' $ removeOccurrences (removedSlices changes) . addOccurrences (addedSlices changes) . removeOccurrences (removedRefs changes) . addOccurrences (addedRefs changes)

-- | Mark a Slice as added
addSlice :: Slice -> Maybe Changes -> Maybe Changes
addSlice slice (Just changes) = Just (changes {addedSlices = Set.insert slice (addedSlices changes)})
addSlice slice Nothing = Just (Changes (Set.singleton slice) mempty mempty mempty)

-- | Mark a Slice as removed
removeSlice :: Slice -> Maybe Changes -> Maybe Changes
removeSlice slice (Just changes) = Just (changes {removedSlices = Set.insert slice (removedSlices changes)})
removeSlice slice Nothing = Just (Changes mempty (Set.singleton slice) mempty mempty)

-- | Mark a Ref as added
addRef :: Ref -> Maybe Changes -> Maybe Changes
addRef ref (Just changes) = Just (changes {addedRefs = Set.insert ref (addedRefs changes)})
addRef ref Nothing = Just (Changes mempty mempty (Set.singleton ref) mempty)

-- | Mark a Ref as removed
removeRef :: Ref -> Maybe Changes -> Maybe Changes
removeRef ref (Just changes) = Just (changes {removedRefs = Set.insert ref (removedRefs changes)})
removeRef ref Nothing = Just (Changes mempty mempty mempty (Set.singleton ref))

--------------------------------------------------------------------------------

-- | Substitutes Limbs in a PolyL.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyL :: (GaloisField n, Integral n) => Relations n -> PolyL n -> Maybe (Either n (PolyL n), Changes)
substPolyL relations poly = do
  let constant = PolyL.polyConstant poly
      initState = (Left constant, Nothing)
      afterSubstSlice =
        foldl
          (substSlice (Relations.relationsS relations))
          initState
          (PolyL.toSlices poly)
      afterSubstRef = Map.foldlWithKey' (substRef relations) afterSubstSlice (PolyL.polyRefs poly)
  case afterSubstRef of
    (_, Nothing) -> Nothing -- nothing changed
    (result, Just changes) -> Just (result, changes)

substSlice ::
  (Integral n, GaloisField n) =>
  SliceRelations ->
  (Either n (PolyL n), Maybe Changes) ->
  (Slice, n) ->
  (Either n (PolyL n), Maybe Changes)
substSlice relations initState (sliceWhole, multiplier) =
  let SliceLookup _ segments = SliceRelations.lookup sliceWhole relations
      tagWithSlice = map (\(index, segment) -> (Slice.Slice (Slice.sliceRefU sliceWhole) index (index + widthOf segment), segment))
      removeNullSegment = filter (not . Segment.null . snd)
      segmentsWithSlices = tagWithSlice $ removeNullSegment (IntMap.toList segments)
   in foldl step initState segmentsWithSlices
  where
    step (accPoly, changes) (slice, segment) =
      let offset = Slice.sliceStart slice - Slice.sliceStart sliceWhole
          coefficient = multiplier * 2 ^ offset
       in case segment of
            Segment.Constant constant -> case accPoly of
              Left c -> (Left (fromIntegral constant * coefficient + c), removeSlice slice changes)
              Right xs -> (Right $ PolyL.addConstant (fromIntegral constant * fromIntegral coefficient) xs, removeSlice slice changes)
            Segment.ChildOf root -> case accPoly of
              -- replace `slice` with `root`
              Left c -> (PolyL.new c [] [(root, coefficient)], (addSlice root . removeSlice slice) changes)
              Right accPoly' -> (PolyL.insertSlices [(root, coefficient)] accPoly', (addSlice root . removeSlice slice) changes)
            Segment.Parent _ _ -> case accPoly of
              Left c -> (PolyL.new c [] [(slice, coefficient)], changes)
              Right xs -> (PolyL.insertSlices [(slice, coefficient)] xs, changes)
            Segment.Free _ -> case accPoly of
              Left c -> (PolyL.new c [] [(slice, coefficient)], changes)
              Right xs -> (PolyL.insertSlices [(slice, coefficient)] xs, changes)

-- | Substitutes a Ref in a PolyL.
substRef ::
  (Integral n, GaloisField n) =>
  Relations n ->
  (Either n (PolyL n), Maybe Changes) ->
  Ref ->
  n ->
  (Either n (PolyL n), Maybe Changes)
substRef relations (accPoly, changes) ref coeff = case Relations.lookup ref relations of
  Relations.Root -> case accPoly of -- ref already a root, no need to substitute
    Left c -> (PolyL.fromRefs c [(ref, coeff)], changes)
    Right xs -> (PolyL.insertRefs 0 [(ref, coeff)] xs, changes)
  Relations.Value intercept ->
    -- ref = intercept
    case accPoly of
      Left c -> (Left (intercept * coeff + c), removeRef ref changes)
      Right xs -> (Right $ PolyL.addConstant (intercept * coeff) xs, removeRef ref changes)
  Relations.ChildOf slope root intercept ->
    if root == ref
      then
        if slope == 1 && intercept == 0
          then -- ref = root, nothing changed
          case accPoly of
            Left c -> (PolyL.fromRefs c [(ref, coeff)], changes)
            Right xs -> (PolyL.insertRefs 0 [(ref, coeff)] xs, changes)
          else error "[ panic ] Invalid relation in RefRelations: ref = slope * root + intercept, but slope /= 1 || intercept /= 0"
      else case accPoly of
        -- coeff * ref = coeff * slope * root + coeff * intercept
        Left c -> (PolyL.fromRefs (intercept * coeff + c) [(root, slope * coeff)], addRef root $ removeRef ref changes)
        Right accPoly' -> (PolyL.insertRefs (intercept * coeff) [(root, slope * coeff)] accPoly', addRef root $ removeRef ref changes)