module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Compile.Relations.BooleanRelations (BooleanRelations)
import Keelung.Compiler.Compile.Relations.BooleanRelations qualified as BooleanRelations
import Keelung.Compiler.Compile.Relations.FieldRelations (FieldRelations)
import Keelung.Compiler.Compile.Relations.FieldRelations qualified as FieldRelations
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

run :: (GaloisField n, Integral n) => ConstraintSystem n -> Either (Compile.Error n) (ConstraintSystem n)
run cs = snd <$> optimizeAddF cs

-- optimizeAddF :: (GaloisField n, Integral n) => ConstraintSystem n -> (WhatChanged, ConstraintSystem n)
-- optimizeAddF cs =
--   let (changed, cs') = runOptiM cs goThroughAddF
--    in case changed of
--         NothingChanged -> (NothingChanged, cs)
--         RelationChanged -> optimizeAddF cs'
--         AdditiveConstraintChanged -> optimizeAddF cs'
--         MultiplicativeConstraintChanged -> optimizeAddF cs'

optimizeAddF :: (GaloisField n, Integral n) => ConstraintSystem n -> Either (Compile.Error n) (WhatChanged, ConstraintSystem n)
optimizeAddF cs = do
  (changed, cs') <- runOptiM cs goThroughAddF
  case changed of
    NothingChanged -> optimizeMulF cs
    RelationChanged -> optimizeAddF cs'
    AdditiveConstraintChanged -> optimizeMulF cs'
    MultiplicativeConstraintChanged -> optimizeMulF cs'

-- optimizeNEqF :: (GaloisField n, Integral n) => ConstraintSystem n -> (WhatChanged, ConstraintSystem n)
-- optimizeNEqF cs =
--   let (changed, cs') = runOptiM cs goThroughNEqF
--    in case changed of
--         NothingChanged -> optimizeMulF cs
--         RelationChanged -> optimizeAddF cs'
--         AdditiveConstraintChanged -> optimizeMulF cs'
--         MultiplicativeConstraintChanged -> optimizeMulF cs'

optimizeMulF :: (GaloisField n, Integral n) => ConstraintSystem n -> Either (Compile.Error n) (WhatChanged, ConstraintSystem n)
optimizeMulF cs = do
  (changed, cs') <- runOptiM cs goThroughMulF
  case changed of
    NothingChanged -> return (changed, cs')
    RelationChanged -> optimizeAddF cs'
    AdditiveConstraintChanged -> optimizeMulF cs'
    MultiplicativeConstraintChanged -> optimizeMulF cs'

goThroughAddF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughAddF = do
  cs <- get
  runRoundM $ do
    csAddF' <- foldMaybeM reduceAddF [] (csAddF cs)
    modify' $ \cs'' -> cs'' {csAddF = csAddF'}

goThroughMulF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughMulF = do
  cs <- get
  runRoundM $ do
    csMulF' <- foldMaybeM reduceMulF [] (csMulF cs)
    modify' $ \cs'' -> cs'' {csMulF = csMulF'}

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
      unionFind <- gets csFieldRelations
      let boolRels = FieldRelations.exportBooleanRelations unionFind
      case substPolyG unionFind boolRels polynomial of
        Nothing -> return (Just polynomial) -- nothing changed
        Just (Left _constant, removedRefs, _) -> do
          -- when (constant /= 0) $
          --   error "[ panic ] Additive reduced to some constant other than 0"
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
  unionFind <- gets csFieldRelations
  let boolRels = FieldRelations.exportBooleanRelations unionFind
  case substPolyG unionFind boolRels polynomial of
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
--    a * b = cs
--      =>
--    cs - a * b = 0
reduceMulFCCP :: (GaloisField n, Integral n) => n -> n -> PolyG Ref n -> RoundM n ()
reduceMulFCCP a b cs = do
  addAddF $ PolyG.addConstant (-a * b) cs

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Constant)
--    a * bs = c
--      =>
--    c - a * bs = 0
reduceMulFCPC :: (GaloisField n, Integral n) => n -> PolyG Ref n -> n -> RoundM n ()
reduceMulFCPC a bs c = do
  case PolyG.multiplyBy (-a) bs of
    Left _constant -> modify' $ removeOccurrences (PolyG.vars bs)
    Right xs -> addAddF $ PolyG.addConstant c xs

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Polynomial)
--    a * bs = cs
--      =>
--    cs - a * bs = 0
reduceMulFCPP :: (GaloisField n, Integral n) => n -> PolyG Ref n -> PolyG Ref n -> RoundM n ()
reduceMulFCPP a polyB polyC = do
  case PolyG.multiplyBy (-a) polyB of
    Left _constant -> do
      modify' $ removeOccurrences (PolyG.vars polyB)
      addAddF polyC
    Right polyBa -> do
      case PolyG.merge polyC polyBa of
        Left _constant -> modify' $ removeOccurrences (PolyG.vars polyC) . removeOccurrences (PolyG.vars polyBa)
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

type OptiM n = StateT (ConstraintSystem n) (Except (Compile.Error n))

type RoundM n = WriterT WhatChanged (OptiM n)

runOptiM :: ConstraintSystem n -> OptiM n a -> Either (Compile.Error n) (a, ConstraintSystem n)
runOptiM cs m = runExcept (runStateT m cs)

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
  markChanged RelationChanged
  cs <- get
  result <- lift $ lift $ FieldRelations.bindBoolean var (value == 1) (csFieldRelations cs)
  put $ removeOccurrences (Set.singleton var) $ cs {csFieldRelations = result}
assign var value = do
  markChanged RelationChanged
  cs <- get
  result <- lift $ lift $ FieldRelations.bindField var value (csFieldRelations cs)
  put $ removeOccurrences (Set.singleton var) $ cs {csFieldRelations = result}

-- | Relates two variables. Returns 'True' if a new relation has been established.
relateF :: (GaloisField n, Integral n) => Ref -> (n, Ref, n) -> RoundM n Bool
relateF var1 (slope, var2, intercept) = do
  cs <- get
  result <- lift $ lift $ FieldRelations.relateRef var1 (slope, var2, intercept) (csFieldRelations cs)
  case result of
    Nothing -> return False
    Just unionFind' -> do
      markChanged RelationChanged
      modify' $ \cs' -> removeOccurrences (Set.fromList [var1, var2]) $ cs' {csFieldRelations = unionFind'}
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
    modify' $ \cs' -> cs' {csAddF = poly : csAddF cs'}

--------------------------------------------------------------------------------

-- | Substitutes variables in a polynomial.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyG :: (GaloisField n, Integral n) => FieldRelations n -> BooleanRelations -> PolyG Ref n -> Maybe (Either n (PolyG Ref n), Set Ref, Set Ref)
substPolyG ctx boolRels poly = do
  let (c, xs) = PolyG.viewAsMap poly
  case Map.foldlWithKey' (substPolyG_ ctx boolRels) (False, Left c, mempty, mempty) xs of
    (False, _, _, _) -> Nothing -- nothing changed
    (True, Left constant, removedRefs, addedRefs) -> Just (Left constant, removedRefs, addedRefs) -- the polynomial has been reduced to a constant
    (True, Right poly', removedRefs, addedRefs) -> Just (Right poly', removedRefs, addedRefs `Set.difference` PolyG.vars poly)

substPolyG_ :: (Integral n, GaloisField n) => FieldRelations n -> BooleanRelations -> (Bool, Either n (PolyG Ref n), Set Ref, Set Ref) -> Ref -> n -> (Bool, Either n (PolyG Ref n), Set Ref, Set Ref)
substPolyG_ ctx boolRels (changed, accPoly, removedRefs, addedRefs) ref coeff = case FieldRelations.parentOf ctx ref of
  FieldRelations.Root -> case ref of
    B refB ->
      case BooleanRelations.lookup refB boolRels of
        BooleanRelations.Root ->
          case accPoly of
            Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
            Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
        BooleanRelations.Value True ->
          let removedRefs' = Set.insert ref removedRefs -- add ref to removedRefs
           in case accPoly of
                Left c -> (True, Left (c + coeff), removedRefs', addedRefs)
                Right xs -> (True, Right $ PolyG.addConstant coeff xs, removedRefs', addedRefs)
        BooleanRelations.Value False ->
          let removedRefs' = Set.insert ref removedRefs -- add ref to removedRefs
           in case accPoly of
                Left c -> (changed, Left c, removedRefs', addedRefs)
                Right xs -> (changed, Right xs, removedRefs', addedRefs)
        BooleanRelations.ChildOf True root ->
          let removedRefs' = Set.insert ref removedRefs
              addedRefs' = Set.insert (B root) addedRefs
           in case accPoly of
                -- ref = root
                Left c -> (True, PolyG.singleton c (B root, coeff), removedRefs', addedRefs')
                Right accPoly' -> (True, PolyG.insert 0 (B root, coeff) accPoly', removedRefs', addedRefs')
        BooleanRelations.ChildOf False root ->
          let removedRefs' = Set.insert ref removedRefs
              addedRefs' = Set.insert (B root) addedRefs
           in case accPoly of
                -- ref = 1 - root
                Left c -> (True, PolyG.singleton (c + coeff) (B root, -coeff), removedRefs', addedRefs')
                Right accPoly' -> (True, PolyG.insert coeff (B root, -coeff) accPoly', removedRefs', addedRefs')
    _ ->
      -- ref is already a root
      case accPoly of
        Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
        Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
  FieldRelations.Constant intercept ->
    -- ref = intercept
    let removedRefs' = Set.insert ref removedRefs -- add ref to removedRefs
     in case accPoly of
          Left c -> (True, Left (intercept * coeff + c), removedRefs', addedRefs)
          Right accPoly' -> (True, Right $ PolyG.addConstant (intercept * coeff) accPoly', removedRefs', addedRefs)
  FieldRelations.ChildOf slope root intercept ->
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