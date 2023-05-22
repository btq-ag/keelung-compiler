module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Relations.Boolean (BooleanRelations)
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Field (AllRelations)
import Keelung.Compiler.Relations.Field qualified as AllRelations
import Keelung.Compiler.Relations.UInt (UIntRelations)
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

-- | Order of optimization, if any of the former optimization pass changed the constraint system,
-- the later optimization pass will be run again at that level
run :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (ConstraintModule n)
run cm = goThroughEqZeros . goThroughModInvs . goThroughDivMods . snd <$> optimizeAddF cm

optimizeAddF :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeAddF cm = do
  (changed, cm') <- runOptiM cm goThroughAddF
  case changed of
    NothingChanged -> optimizeMulF cm
    RelationChanged -> optimizeAddF cm'
    AdditiveConstraintChanged -> optimizeMulF cm'
    MultiplicativeConstraintChanged -> optimizeMulF cm'

optimizeMulF :: (GaloisField n, Integral n) => ConstraintModule n -> Either (Compile.Error n) (WhatChanged, ConstraintModule n)
optimizeMulF cm = do
  (changed, cm') <- runOptiM cm goThroughMulF
  case changed of
    NothingChanged -> return (changed, cm')
    RelationChanged -> optimizeAddF cm'
    AdditiveConstraintChanged -> optimizeMulF cm'
    MultiplicativeConstraintChanged -> optimizeMulF cm'

goThroughAddF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughAddF = do
  cm <- get
  runRoundM $ do
    result <- foldMaybeM reduceAddF [] (cmAddF cm)
    modify' $ \cm' -> cm' {cmAddF = result}

goThroughEqZeros :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughEqZeros cm =
  let relations = cmFieldRelations cm
   in cm {cmEqZeros = mapMaybe (reduceEqZeros relations) (cmEqZeros cm)}
  where
    reduceEqZeros :: (GaloisField n, Integral n) => AllRelations n -> (PolyG Ref n, RefF) -> Maybe (PolyG Ref n, RefF)
    reduceEqZeros relations (polynomial, m) = case substPolyG relations polynomial of
      Nothing -> Just (polynomial, m) -- nothing changed
      Just (Left _constant, _, _) -> Nothing
      Just (Right reducePolynomial, _, _) -> Just (reducePolynomial, m)

goThroughDivMods :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughDivMods cm =
  let relations = cmFieldRelations cm
      substDivMod (a, b, q, r) = (substVar relations a, substVar relations b, substVar relations q, substVar relations r)
   in cm {cmDivMods = map substDivMod (cmDivMods cm)}
  where
    substVar _ (Right val) = Right val
    substVar relations (Left ref) = case AllRelations.lookup (U ref) relations of
      AllRelations.Root -> Left ref
      AllRelations.Value val -> Right val
      AllRelations.ChildOf 1 (U root) 0 -> Left root
      AllRelations.ChildOf {} -> Left ref

goThroughModInvs :: (GaloisField n, Integral n) => ConstraintModule n -> ConstraintModule n
goThroughModInvs cm =
  let relations = cmFieldRelations cm
      substModInv (a, b, c) = (substVar relations a, substVar relations b, c)
   in cm {cmModInvs = map substModInv (cmModInvs cm)}
  where
    substVar _ (Right val) = Right val
    substVar relations (Left ref) = case AllRelations.lookup (U ref) relations of
      AllRelations.Root -> Left ref
      AllRelations.Value val -> Right val
      AllRelations.ChildOf 1 (U root) 0 -> Left root
      AllRelations.ChildOf {} -> Left ref

goThroughMulF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughMulF = do
  cm <- get
  runRoundM $ do
    cmMulF' <- foldMaybeM reduceMulF [] (cmMulF cm)
    modify' $ \cm'' -> cm'' {cmMulF = cmMulF'}

foldMaybeM :: Monad m => (a -> m (Maybe a)) -> [a] -> [a] -> m [a]
foldMaybeM f = foldM $ \acc x -> do
  result <- f x
  case result of
    Nothing -> return acc
    Just x' -> return (x' : acc)

reduceAddF :: (GaloisField n, Integral n) => PolyG Ref n -> RoundM n (Maybe (PolyG Ref n))
reduceAddF polynomial = do
  changed <- learnFromAddF polynomial
  if changed
    then return Nothing
    else do
      allRelations <- gets cmFieldRelations
      case substPolyG allRelations polynomial of
        Nothing -> return (Just polynomial) -- nothing changed
        Just (Left constant, removedRefs, _) -> do
          when (constant /= 0) $
            error "[ panic ] Additive reduced to some constant other than 0"
          -- the polynomial has been reduced to nothing
          markChanged AdditiveConstraintChanged
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs
          return Nothing
        Just (Right reducePolynomial, removedRefs, addedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged AdditiveConstraintChanged
          -- remove variables that has been reduced in the polynomial from the occurrence list
          modify' $ removeOccurrences removedRefs . addOccurrences addedRefs
          -- keep reducing the reduced polynomial
          reduceAddF reducePolynomial

type MulF n = (PolyG Ref n, PolyG Ref n, Either n (PolyG Ref n))

reduceMulF :: (GaloisField n, Integral n) => MulF n -> RoundM n (Maybe (MulF n))
reduceMulF (polyA, polyB, polyC) = do
  polyAResult <- substitutePolyF MultiplicativeConstraintChanged polyA
  polyBResult <- substitutePolyF MultiplicativeConstraintChanged polyB
  polyCResult <- case polyC of
    Left constantC -> return (Left constantC)
    Right polyC' -> substitutePolyF MultiplicativeConstraintChanged polyC'
  reduceMulF_ polyAResult polyBResult polyCResult

substitutePolyF :: (GaloisField n, Integral n) => WhatChanged -> PolyG Ref n -> RoundM n (Either n (PolyG Ref n))
substitutePolyF typeOfChange polynomial = do
  allRelations <- gets cmFieldRelations
  case substPolyG allRelations polynomial of
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
reduceMulF_ :: (GaloisField n, Integral n) => Either n (PolyG Ref n) -> Either n (PolyG Ref n) -> Either n (PolyG Ref n) -> RoundM n (Maybe (MulF n))
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
reduceMulFCCP :: (GaloisField n, Integral n) => n -> n -> PolyG Ref n -> RoundM n ()
reduceMulFCCP a b cm = do
  addAddF $ PolyG.addConstant (-a * b) cm

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Constant)
--    a * bs = c
--      =>
--    c - a * bs = 0
reduceMulFCPC :: (GaloisField n, Integral n) => n -> PolyG Ref n -> n -> RoundM n ()
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
reduceMulFCPP :: (GaloisField n, Integral n) => n -> PolyG Ref n -> PolyG Ref n -> RoundM n ()
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

data WhatChanged
  = NothingChanged
  | RelationChanged
  | AdditiveConstraintChanged
  | MultiplicativeConstraintChanged
  deriving (Eq, Show)

instance Semigroup WhatChanged where
  NothingChanged <> x = x
  x <> NothingChanged = x
  RelationChanged <> _ = RelationChanged
  _ <> RelationChanged = RelationChanged
  AdditiveConstraintChanged <> _ = AdditiveConstraintChanged
  _ <> AdditiveConstraintChanged = AdditiveConstraintChanged
  MultiplicativeConstraintChanged <> _ = MultiplicativeConstraintChanged

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
learnFromAddF :: (GaloisField n, Integral n) => PolyG Ref n -> RoundM n Bool
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

assign :: (GaloisField n, Integral n) => Ref -> n -> RoundM n ()
assign (B var) value = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ AllRelations.assignB var (value == 1) (cmFieldRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmFieldRelations = relations}
assign (U var) value = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ AllRelations.assignU var value (cmFieldRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmFieldRelations = relations}
assign (F var) value = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ AllRelations.assignF (F var) value (cmFieldRelations cm)
  case result of
    Nothing -> return ()
    Just relations -> do
      markChanged RelationChanged
      put $ removeOccurrences (Set.singleton var) $ cm {cmFieldRelations = relations}

-- | Relates two variables. Returns 'True' if a new relation has been established.
relateF :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> RoundM n Bool
relateF var1 (slope, var2, intercept) = do
  cm <- get
  result <- lift $ lift $ EquivClass.runM $ AllRelations.relateRefs var1 slope var2 intercept (cmFieldRelations cm)
  case result of
    Nothing -> return False
    Just relations -> do
      markChanged RelationChanged
      modify' $ \cm' -> removeOccurrences (Set.fromList [var1, var2]) $ cm' {cmFieldRelations = relations}
      return True

addAddF :: (GaloisField n, Integral n) => PolyG Ref n -> RoundM n ()
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
    markChanged AdditiveConstraintChanged
    modify' $ \cm' -> cm' {cmAddF = poly : cmAddF cm'}

--------------------------------------------------------------------------------

-- | Substitutes variables in a polynomial.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyG :: (GaloisField n, Integral n) => AllRelations n -> PolyG Ref n -> Maybe (Either n (PolyG Ref n), Set Ref, Set Ref)
substPolyG relations poly = do
  let boolRels = AllRelations.exportBooleanRelations relations
  let uintRels = AllRelations.exportUIntRelations relations
  let (c, xs) = PolyG.viewAsMap poly
  case Map.foldlWithKey' (substPolyG_ relations boolRels uintRels) (False, Left c, mempty, mempty) xs of
    (False, _, _, _) -> Nothing -- nothing changed
    (True, Left constant, removedRefs, addedRefs) -> Just (Left constant, removedRefs, addedRefs) -- the polynomial has been reduced to a constant
    (True, Right poly', removedRefs, addedRefs) -> Just (Right poly', removedRefs, addedRefs `Set.difference` PolyG.vars poly)

substPolyG_ ::
  (Integral n, GaloisField n) =>
  AllRelations n ->
  BooleanRelations ->
  UIntRelations n ->
  (Bool, Either n (PolyG Ref n), Set Ref, Set Ref) ->
  Ref ->
  n ->
  (Bool, Either n (PolyG Ref n), Set Ref, Set Ref)
substPolyG_ relations _boolRels _uintRels (changed, accPoly, removedRefs, addedRefs) ref coeff = case AllRelations.lookup ref relations of
  AllRelations.Root -> case accPoly of
    Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
    Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
  AllRelations.Value intercept ->
    -- ref = intercept
    let removedRefs' = Set.insert ref removedRefs -- add ref to removedRefs
     in case accPoly of
          Left c -> (True, Left (intercept * coeff + c), removedRefs', addedRefs)
          Right xs -> (True, Right $ PolyG.addConstant (intercept * coeff) xs, removedRefs', addedRefs)
  AllRelations.ChildOf slope root intercept ->
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