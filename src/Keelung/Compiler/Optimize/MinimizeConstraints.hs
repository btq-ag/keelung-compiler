module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Field (Relations)
import Keelung.Compiler.Relations.Field qualified as Relations
import Keelung.Compiler.Relations.UInt qualified as UInt
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.PolyL
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference

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
run cm = goThroughEqZeros . goThroughModInvs . goThroughDivMods . snd <$> optimizeAddF cm

-- | TODO: reexamine the state transitions
optimizeAddF :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeAddF cm = do
  (changed, cm') <- runOptiM cm goThroughAddF
  case changed of
    NothingChanged -> optimizeAddL cm -- proceed to AddL?
    RelationChanged -> optimizeAddF cm' -- restart from AddF
    AdditiveFieldConstraintChanged -> optimizeAddL cm' -- proceed to AddL?
    AdditiveLimbConstraintChanged -> optimizeMulF cm' -- proceed to MulF?
    MultiplicativeConstraintChanged -> optimizeMulF cm' -- proceed to MulL?
    MultiplicativeLimbConstraintChanged -> optimizeMulL cm' -- back to MulL

-- | TODO: reexamine the state transitions
optimizeAddL :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeAddL cm = do
  (changed, cm') <- runOptiM cm goThroughAddL
  case changed of
    NothingChanged -> optimizeMulF cm -- proceed to MulF?
    RelationChanged -> optimizeAddF cm' -- restart from AddF
    AdditiveFieldConstraintChanged -> optimizeAddL cm' -- proceed to AddL?
    AdditiveLimbConstraintChanged -> optimizeMulF cm' -- proceed to MulF?
    MultiplicativeConstraintChanged -> optimizeMulL cm' -- proceed to MulL?
    MultiplicativeLimbConstraintChanged -> optimizeMulL cm' -- back to MulL

optimizeMulF :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeMulF cm = do
  (changed, cm') <- runOptiM cm goThroughMulF
  case changed of
    NothingChanged -> optimizeMulL cm' -- proceed to MulL?
    RelationChanged -> optimizeAddF cm' -- restart from AddF
    AdditiveFieldConstraintChanged -> optimizeAddL cm' -- proceed to AddL?
    AdditiveLimbConstraintChanged -> optimizeMulF cm' -- proceed to MulF?
    MultiplicativeConstraintChanged -> optimizeMulL cm' -- proceed to MulL?
    MultiplicativeLimbConstraintChanged -> optimizeMulL cm' -- back to MulL

optimizeMulL :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeMulL cm = do
  (changed, cm') <- runOptiM cm goThroughMulL
  case changed of
    NothingChanged -> return (changed, cm')
    RelationChanged -> optimizeAddF cm' -- restart from AddF
    AdditiveFieldConstraintChanged -> optimizeAddL cm' -- proceed to AddL?
    AdditiveLimbConstraintChanged -> optimizeMulF cm' -- proceed to MulF?
    MultiplicativeConstraintChanged -> optimizeMulL cm' -- proceed to MulL?
    MultiplicativeLimbConstraintChanged -> optimizeMulL cm' -- back to MulL

goThroughAddF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughAddF = do
  cm <- get
  runRoundM $ do
    result <- foldMaybeM reduceAddF [] (cmAddF cm)
    modify' $ \cm' -> cm' {cmAddF = result}

goThroughAddL :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughAddL = do
  cm <- get
  runRoundM $ do
    result <- foldMaybeM reduceAddL [] (cmAddL cm)
    modify' $ \cm' -> cm' {cmAddL = result}

goThroughEqZeros :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughEqZeros cm =
  let relations = cmRelations cm
   in cm {cmEqZeros = mapMaybe (reduceEqZeros relations) (cmEqZeros cm)}
  where
    reduceEqZeros :: (GaloisField n, Integral n) => Relations n -> (PolyG n, RefF) -> Maybe (PolyG n, RefF)
    reduceEqZeros relations (polynomial, m) = case substPolyG relations polynomial of
      Nothing -> Just (polynomial, m) -- nothing changed
      Just (Left _constant, _, _) -> Nothing
      Just (Right reducePolynomial, _, _) -> Just (reducePolynomial, m)

goThroughDivMods :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughDivMods cm =
  let substDivMod (a, b, q, r) = (a, b, q, r)
   in cm {cmDivMods = map substDivMod (cmDivMods cm)}

goThroughModInvs :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughModInvs cm =
  let substModInv (a, b, c, d) = (a, b, c, d)
   in cm {cmModInvs = map substModInv (cmModInvs cm)}

goThroughMulF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughMulF = do
  cm <- get
  runRoundM $ do
    cmMulF' <- foldMaybeM reduceMulF [] (cmMulF cm)
    modify' $ \cm'' -> cm'' {cmMulF = cmMulF'}

goThroughMulL :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughMulL = do
  cm <- get
  runRoundM $ do
    cmMulL' <- foldMaybeM reduceMulL [] (cmMulL cm)
    modify' $ \cm'' -> cm'' {cmMulL = cmMulL'}

foldMaybeM :: Monad m => (a -> m (Maybe a)) -> [a] -> [a] -> m [a]
foldMaybeM f = foldM $ \acc x -> do
  result <- f x
  case result of
    Nothing -> return acc
    Just x' -> return (x' : acc)

reduceAddF :: (GaloisField n, Integral n) => PolyG n -> RoundM n (Maybe (PolyG n))
reduceAddF polynomial = do
  changed <- learnFromAddF polynomial
  if changed
    then return Nothing
    else do
      relations <- gets cmRelations
      case substPolyG relations polynomial of
        Nothing -> return (Just polynomial) -- nothing changed
        Just (Left constant, removedRefs, _) -> do
          when (constant /= 0) $
            error "[ panic ] Additive reduced to some constant other than 0"
          -- the polynomial has been reduced to nothing
          markChanged AdditiveFieldConstraintChanged
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs
          return Nothing
        Just (Right reducePolynomial, removedRefs, addedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged AdditiveFieldConstraintChanged
          -- remove variables that has been reduced in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs . addOccurrences addedRefs
          -- keep reducing the reduced polynomial
          reduceAddF reducePolynomial

reduceAddL :: (GaloisField n, Integral n) => PolyL n -> RoundM n (Maybe (PolyL n))
reduceAddL polynomial = do
  changed <- learnFromAddL polynomial
  if changed
    then return Nothing
    else do
      relations <- gets cmRelations
      case substPolyL relations polynomial of
        Nothing -> return (Just polynomial) -- nothing changed
        Just (Left constant, removedRefs, _) -> do
          when (constant /= 0) $
            error "[ panic ] Additive reduced to some constant other than 0"
          -- the polynomial has been reduced to nothing
          markChanged AdditiveLimbConstraintChanged
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs
          return Nothing
        Just (Right reducePolynomial, removedRefs, addedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged AdditiveLimbConstraintChanged
          -- remove variables that has been reduced in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs . addOccurrences addedRefs
          -- keep reducing the reduced polynomial
          reduceAddL reducePolynomial

type MulF n = (PolyG n, PolyG n, Either n (PolyG n))

reduceMulF :: (GaloisField n, Integral n) => MulF n -> RoundM n (Maybe (MulF n))
reduceMulF (polyA, polyB, polyC) = do
  polyAResult <- substitutePolyF MultiplicativeConstraintChanged polyA
  polyBResult <- substitutePolyF MultiplicativeConstraintChanged polyB
  polyCResult <- case polyC of
    Left constantC -> return (Left constantC)
    Right polyC' -> substitutePolyF MultiplicativeConstraintChanged polyC'
  reduceMulF_ polyAResult polyBResult polyCResult
  where
    substitutePolyF :: (GaloisField n, Integral n) => WhatChanged -> PolyG n -> RoundM n (Either n (PolyG n))
    substitutePolyF typeOfChange polynomial = do
      relations <- gets cmRelations
      case substPolyG relations polynomial of
        Nothing -> return (Right polynomial) -- nothing changed
        Just (Left constant, removedRefs, _) -> do
          -- the polynomial has been reduced to nothing
          markChanged typeOfChange
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs
          return (Left constant)
        Just (Right reducePolynomial, removedRefs, addedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged typeOfChange
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs . addOccurrences addedRefs
          return (Right reducePolynomial)

-- | Trying to reduce a multiplicative constaint, returns the reduced constraint if it is reduced
reduceMulF_ :: (GaloisField n, Integral n) => Either n (PolyG n) -> Either n (PolyG n) -> Either n (PolyG n) -> RoundM n (Maybe (MulF n))
reduceMulF_ polyA polyB polyC = case (polyA, polyB, polyC) of
  (Left _a, Left _b, Left _c) -> return Nothing
  (Left a, Left b, Right c) -> reduceMulFCCP a b c >> return Nothing
  (Left a, Right b, Left c) -> reduceMulFCPC a b c >> return Nothing
  (Left a, Right b, Right c) -> reduceMulFCPP a b c >> return Nothing
  (Right a, Left b, Left c) -> reduceMulFCPC b a c >> return Nothing
  (Right a, Left b, Right c) -> reduceMulFCPP b a c >> return Nothing
  (Right a, Right b, Left c) -> return (Just (a, b, Left c))
  (Right a, Right b, Right c) -> return (Just (a, b, Right c))

-- | Trying to reduce a multiplicative constaint of (Constant / Constant / Polynomial)
--    a * b = cm
--      =>
--    cm - a * b = 0
reduceMulFCCP :: (GaloisField n, Integral n) => n -> n -> PolyG n -> RoundM n ()
reduceMulFCCP a b cm = do
  addAddF $ PolyG.addConstant (-a * b) cm

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Constant)
--    a * bs = c
--      =>
--    c - a * bs = 0
reduceMulFCPC :: (GaloisField n, Integral n) => n -> PolyG n -> n -> RoundM n ()
reduceMulFCPC a bs c = do
  case PolyG.multiplyBy (-a) bs of
    Left constant ->
      if constant == c
        then modify' $ removeOccurrences (PolyG.vars bs)
        else throwError $ Compile.ConflictingValuesF constant c
    Right xs -> addAddF $ PolyG.addConstant c xs

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Polynomial)
--    a * bs = cm
--      =>
--    cm - a * bs = 0
reduceMulFCPP :: (GaloisField n, Integral n) => n -> PolyG n -> PolyG n -> RoundM n ()
reduceMulFCPP a polyB polyC = do
  case PolyG.multiplyBy (-a) polyB of
    Left constant ->
      if constant == 0
        then do
          -- a * bs = 0
          -- cm = 0
          modify' $ removeOccurrences (PolyG.vars polyB)
          addAddF polyC
        else do
          -- a * bs = constant = cm
          -- => cm - constant = 0
          modify' $ removeOccurrences (PolyG.vars polyB)
          addAddF (PolyG.addConstant (-constant) polyC)
    Right polyBa -> do
      case PolyG.merge polyC polyBa of
        Left constant ->
          if constant == 0
            then modify' $ removeOccurrences (PolyG.vars polyC) . removeOccurrences (PolyG.vars polyBa)
            else throwError $ Compile.ConflictingValuesF constant 0
        Right addF -> do
          addAddF addF

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
  where
    substitutePolyL :: (GaloisField n, Integral n) => WhatChanged -> PolyL n -> RoundM n (Either n (PolyL n))
    substitutePolyL typeOfChange polynomial = do
      relations <- gets cmRelations
      case substPolyL relations polynomial of
        Nothing -> return (Right polynomial) -- nothing changed
        Just (Left constant, removedRefs, _) -> do
          -- the polynomial has been reduced to nothing
          markChanged typeOfChange
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs
          return (Left constant)
        Just (Right reducePolynomial, removedRefs, addedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged typeOfChange
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs . addOccurrences addedRefs
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
reduceMulLCCP a b cm = do
  addAddL $ PolyL.addConstant (-a * b) cm

-- | Trying to reduce a multiplicative limb constaint of (Constant / Polynomial / Constant)
--    a * bs = c
--      =>
--    c - a * bs = 0
reduceMulLCPC :: (GaloisField n, Integral n) => n -> PolyL n -> n -> RoundM n ()
reduceMulLCPC a bs c = do
  case PolyL.multiplyBy (-a) bs of
    Left constant ->
      if constant == c
        then modify' $ removeOccurrences (PolyL.vars bs)
        else throwError $ Compile.ConflictingValuesU (toInteger constant) (toInteger c)
    Right xs -> addAddL $ PolyL.addConstant c xs

-- | Trying to reduce a multiplicative limb constaint of (Constant / Polynomial / Polynomial)
--    a * bs = cm
--      =>
--    cm - a * bs = 0
reduceMulLCPP :: (GaloisField n, Integral n) => n -> PolyL n -> PolyL n -> RoundM n ()
reduceMulLCPP a polyB polyC = do
  case PolyL.multiplyBy (-a) polyB of
    Left constant ->
      if constant == 0
        then do
          -- a * bs = 0
          -- cm = 0
          modify' $ removeOccurrences (PolyL.vars polyB)
          addAddL polyC
        else do
          -- a * bs = constant = cm
          -- => cm - constant = 0
          modify' $ removeOccurrences (PolyL.vars polyB)
          addAddL (PolyL.addConstant (-constant) polyC)
    Right polyBa -> addAddL (PolyL.merge polyC polyBa)

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
learnFromAddF :: (GaloisField n, Integral n) => PolyG n -> RoundM n Bool
learnFromAddF poly = case PolyG.view poly of
  PolyG.Monomial intercept (var, slope) -> do
    --    intercept + slope * var = 0
    --  =>
    --    var = - intercept / slope
    assign var (-intercept / slope)
    return True
  PolyG.Binomial intercept (var1, slope1) (var2, slope2) -> do
    --    intercept + slope1 * var1 + slope2 * var2 = 0
    --  =>
    --    slope1 * var1 = - slope2 * var2 - intercept
    --  =>
    --    var1 = - slope2 * var2 / slope1 - intercept / slope1
    relateF var1 (-slope2 / slope1, var2, -intercept / slope1)
  PolyG.Polynomial _ _ -> return False

-- | Go through additive constraints and classify them into relation constraints when possible.
--   Returns 'True' if the constraint has been reduced.
learnFromAddL :: (GaloisField n, Integral n) => PolyL n -> RoundM n Bool
learnFromAddL poly = case PolyL.view poly of
  (_, Seq.Empty) -> error "[ panic ] Empty PolyL"
  (constant, (var1, multiplier1) Seq.:<| Seq.Empty) -> do
    --  constant + var1 * multiplier1  = 0
    --    =>
    --  var1 = - constant / multiplier1
    assignL var1 (toInteger (-constant / multiplier1))
    return True
  (constant, (var1, multiplier1) Seq.:<| (var2, multiplier2) Seq.:<| Seq.Empty) ->
    if constant == 0 && multiplier1 == -multiplier2
      then do
        --  var1 * multiplier1 = var2 * multiplier2
        relateL var1 var2
      else return False
  _ -> return False

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
  result <- lift $ lift $ EquivClass.runM $ Relations.assignF (F var) value (cmRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmRelations = relations}

assignL :: (GaloisField n, Integral n) => RefL -> Integer -> RoundM n ()
assignL var value = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ Relations.assignL var value (cmRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmRelations = relations}

-- | Relates two variables. Returns 'True' if a new relation has been established.
relateF :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> RoundM n Bool
relateF var1 (slope, var2, intercept) = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ Relations.relateRefs var1 slope var2 intercept (cmRelations cm)
  case result of
    Nothing -> return False
    Just relations -> do
      markChanged RelationChanged
      modify' $ \cm' -> removeOccurrences (Set.fromList [var1, var2]) $ cm' {cmRelations = relations}
      return True

-- | Relates two RefLs. Returns 'True' if a new relation has been established.
relateL :: (GaloisField n, Integral n) => RefL -> RefL -> RoundM n Bool
relateL var1 var2 = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ Relations.relateL var1 var2 (cmRelations cm)
  case result of
    Nothing -> return False
    Just relations -> do
      markChanged RelationChanged
      modify' $ \cm' -> removeOccurrences (Set.fromList [var1, var2]) $ cm' {cmRelations = relations}
      return True

--------------------------------------------------------------------------------

-- | Add learned additive constraints to the pool
addAddF :: (GaloisField n, Integral n) => PolyG n -> RoundM n ()
addAddF poly = case PolyG.view poly of
  PolyG.Monomial constant (var1, coeff1) -> do
    --    constant + coeff1 * var1 = 0
    --      =>
    --    var1 = - constant / coeff1
    assign var1 (-constant / coeff1)
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> do
    --    constant + coeff1 * var1 + coeff2 * var2 = 0
    --      =>
    --    coeff1 * var1 = - coeff2 * var2 - constant
    --      =>
    --    var1 = - coeff2 * var2 / coeff1 - constant / coeff1
    void $ relateF var1 (-coeff2 / coeff1, var2, -constant / coeff1)
  PolyG.Polynomial _ _ -> do
    markChanged AdditiveFieldConstraintChanged
    modify' $ \cm' -> cm' {cmAddF = poly : cmAddF cm'}

-- | Add learned additive limb constraints to the pool
addAddL :: (GaloisField n, Integral n) => PolyL n -> RoundM n ()
addAddL poly = case PolyL.view poly of
  (_, Seq.Empty) -> error "[ panic ] Empty PolyL"
  (constant, (var1, multiplier1) Seq.:<| Seq.Empty) -> do
    --  constant + var1 * multiplier1  = 0
    --    =>
    --  var1 = - constant / multiplier1
    assignL var1 (toInteger (-constant / multiplier1))
  (constant, (var1, multiplier1) Seq.:<| (var2, multiplier2) Seq.:<| Seq.Empty) ->
    --  var1 * multiplier1 = var2 * multiplier2
    when (constant == 0 && multiplier1 == -multiplier2) $
      void $
        relateL var1 var2
  _ -> return ()

--------------------------------------------------------------------------------

-- | Substitutes variables in a polynomial.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyG :: (GaloisField n, Integral n) => Relations n -> PolyG n -> Maybe (Either n (PolyG n), Set Ref, Set Ref)
substPolyG relations poly = do
  let (c, xs) = PolyG.viewAsMap poly
  case Map.foldlWithKey' (substPolyG_ relations) (False, Left c, mempty, mempty) xs of
    (False, _, _, _) -> Nothing -- nothing changed
    (True, Left constant, removedRefs, addedRefs) -> Just (Left constant, removedRefs, addedRefs) -- the polynomial has been reduced to a constant
    (True, Right poly', removedRefs, addedRefs) -> Just (Right poly', removedRefs, addedRefs `Set.difference` PolyG.vars poly)

substPolyG_ ::
  (Integral n, GaloisField n) =>
  Relations n ->
  (Bool, Either n (PolyG n), Set Ref, Set Ref) ->
  Ref ->
  n ->
  (Bool, Either n (PolyG n), Set Ref, Set Ref)
substPolyG_ relations (changed, accPoly, removedRefs, addedRefs) ref coeff = case Relations.lookup ref relations of
  Relations.Root -> case accPoly of
    Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
    Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
  Relations.Value intercept ->
    -- ref = intercept
    let removedRefs' = Set.insert ref removedRefs -- add ref to removedRefs
     in case accPoly of
          Left c -> (True, Left (intercept * coeff + c), removedRefs', addedRefs)
          Right xs -> (True, Right $ PolyG.addConstant (intercept * coeff) xs, removedRefs', addedRefs)
  Relations.ChildOf slope root intercept ->
    if root == ref
      then
        if slope == 1 && intercept == 0
          then -- ref = root, nothing changed
          case accPoly of
            Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
            Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
          else error "[ panic ] Invalid relation in FieldRelations: ref = slope * root + intercept, but slope /= 1 || intercept /= 0"
      else
        let removedRefs' = Set.insert ref removedRefs
            addedRefs' = Set.insert root addedRefs
         in case accPoly of
              -- ref = slope * root + intercept
              Left c -> (True, PolyG.singleton (intercept * coeff + c) (root, slope * coeff), removedRefs', addedRefs')
              Right accPoly' -> (True, PolyG.insert (intercept * coeff) (root, slope * coeff) accPoly', removedRefs', addedRefs')

--------------------------------------------------------------------------------

-- | Substitutes RefLs in a PolyL.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyL :: (GaloisField n, Integral n) => Relations n -> PolyL n -> Maybe (Either n (PolyL n), Set RefL, Set RefL)
substPolyL relations poly = do
  let (c, xs) = PolyL.view poly
  case foldl (substPolyL_ (Relations.exportUIntRelations relations)) (False, Left c, mempty, mempty) xs of
    (False, _, _, _) -> Nothing -- nothing changed
    (True, Left constant, removedRefs, addedRefs) -> Just (Left constant, removedRefs, addedRefs) -- the polynomial has been reduced to a constant
    (True, Right poly', removedRefs, addedRefs) -> Just (Right poly', removedRefs, addedRefs `Set.difference` PolyL.vars' poly)

substPolyL_ ::
  (Integral n, GaloisField n) =>
  UInt.UIntRelations ->
  (Bool, Either n (PolyL n), Set RefL, Set RefL) ->
  (RefL, n) ->
  (Bool, Either n (PolyL n), Set RefL, Set RefL)
substPolyL_ relations (changed, accPoly, removedRefs, addedRefs) (ref, multiplier) = case EquivClass.lookup ref relations of
  EquivClass.IsConstant constant ->
    let removedRefs' = Set.insert ref removedRefs -- add ref to removedRefs
     in case accPoly of
          Left c -> (True, Left (fromInteger constant * multiplier + c), removedRefs', addedRefs)
          Right xs -> (True, Right $ PolyL.addConstant (fromInteger constant * multiplier) xs, removedRefs', addedRefs)
  EquivClass.IsRoot _ -> case accPoly of
    Left c -> (changed, PolyL.singleton c (ref, multiplier), removedRefs, addedRefs)
    Right xs -> (changed, Right (PolyL.insert 0 (ref, multiplier) xs), removedRefs, addedRefs)
  EquivClass.IsChildOf root () ->
    if root == ref
      then case accPoly of
        Left c -> (changed, PolyL.singleton c (ref, multiplier), removedRefs, addedRefs)
        Right xs -> (changed, Right (PolyL.insert 0 (ref, multiplier) xs), removedRefs, addedRefs)
      else
        let removedRefs' = Set.insert ref removedRefs
            addedRefs' = Set.insert root addedRefs
         in case accPoly of
              -- replace `ref` with `root`
              Left c -> (True, PolyL.singleton c (root, multiplier), removedRefs', addedRefs')
              Right accPoly' -> (True, Right (PolyL.insert 0 (root, multiplier) accPoly'), removedRefs', addedRefs')