module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run cs = run_ (RelationChanged, cs)

run_ :: (GaloisField n, Integral n) => (WhatChanged, ConstraintSystem n) -> ConstraintSystem n
run_ (NothingChanged, cs) = cs
run_ (RelationChanged, cs) = run_ $ runOptiM cs goThroughAddF
run_ (AdditiveConstraintChanged, cs) = run_ $ runOptiM cs goThroughMulF
run_ (MultiplicativeConstraintChanged, cs) = run_ $ runOptiM cs goThroughMulF

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

reduceAddF :: (GaloisField n, Integral n) => PolyG RefF n -> RoundM n (Maybe (PolyG RefF n))
reduceAddF poly = do
  changed <- learnFromAddF poly
  if changed
    then return Nothing
    else do
      unionFind <- gets csVarEqF
      case substPolyG unionFind poly of
        Nothing -> return (Just poly) -- nothing changed
        Just (Left _constant, substitutedRefs) -> do
          -- when (constant /= 0) $
          --   error "[ panic ] Additive reduced to some constant other than 0"
          -- the polynomial has been reduced to nothing
          markChanged AdditiveConstraintChanged
          -- remove all variables in the polynomial from the occurrence list
          modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
          return Nothing
        Just (Right poly', substitutedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged AdditiveConstraintChanged
          -- remove variables that has been reduced in the polynomial from the occurrence list
          modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
          -- keep reducing the reduced polynomial
          reduceAddF poly'

type MulF n = (PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))

reduceMulF :: (GaloisField n, Integral n) => (PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n)) -> RoundM n (Maybe (MulF n))
reduceMulF (polyA, polyB, polyC) = do
  polyAResult <- substitutePoly MultiplicativeConstraintChanged polyA
  polyBResult <- substitutePoly MultiplicativeConstraintChanged polyB
  polyCResult <- case polyC of
    Left constantC -> return (Left constantC)
    Right polyC' -> substitutePoly MultiplicativeConstraintChanged polyC'
  reduceMulF_ polyAResult polyBResult polyCResult
  -- result <- reduceMulF_ polyAResult polyBResult polyCResult
  -- case result of
  --   Nothing -> return Nothing
  --   Just (polyA', polyB', polyC') -> do
  --     markChanged MultiplicativeConstraintChanged
  --     reduceMulF (polyA', polyB', polyC')

substitutePoly :: (GaloisField n, Integral n) => WhatChanged -> PolyG RefF n -> RoundM n (Either n (PolyG RefF n))
substitutePoly typeOfChange polynomial = do
  unionFind <- gets csVarEqF
  case substPolyG unionFind polynomial of
    Nothing -> return (Right polynomial) -- nothing changed
    Just (Left constant, substitutedRefs) -> do
      -- the polynomial has been reduced to nothing
      markChanged typeOfChange
      -- remove all variables in the polynomial from the occurrence list
      modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
      return (Left constant)
    Just (Right reducePolynomial, substitutedRefs) -> do
      -- the polynomial has been reduced to something
      markChanged typeOfChange
      -- remove all variables in the polynomial from the occurrence list
      modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
      return (Right reducePolynomial)

-- | Trying to reduce a multiplicative constaint, returns the reduced constraint if it is reduced
reduceMulF_ :: (GaloisField n, Integral n) => Either n (PolyG RefF n) -> Either n (PolyG RefF n) -> Either n (PolyG RefF n) -> RoundM n (Maybe (MulF n))
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
reduceMulFCCP :: (GaloisField n, Integral n) => n -> n -> PolyG RefF n -> RoundM n ()
reduceMulFCCP a b cs = do
  addAddF $ PolyG.addConstant (-a * b) cs

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Constant)
--    a * bs = c
--      =>
--    c - a * bs = 0
reduceMulFCPC :: (GaloisField n, Integral n) => n -> PolyG RefF n -> n -> RoundM n ()
reduceMulFCPC a bs c = do
  case PolyG.multiplyBy (-a) bs of
    Left _constant -> modify' $ \cs -> cs {csOccurrenceF = removeOccurrencesWithPolyG bs (csOccurrenceF cs)}
    Right xs -> addAddF $ PolyG.addConstant c xs

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Polynomial)
--    a * bs = cs
--      =>
--    cs - a * bs = 0
reduceMulFCPP :: (GaloisField n, Integral n) => n -> PolyG RefF n -> PolyG RefF n -> RoundM n ()
reduceMulFCPP a polyB polyC = do
  case PolyG.multiplyBy (-a) polyB of
    Left _constant -> do
      modify' $ \cs -> cs {csOccurrenceF = removeOccurrencesWithPolyG polyB (csOccurrenceF cs)}
      addAddF polyC
    Right polyBa -> do
      case PolyG.merge polyC polyBa of
        Left _constant -> modify' $ \cs -> cs {csOccurrenceF = removeOccurrencesWithPolyG polyC (removeOccurrencesWithPolyG polyBa (csOccurrenceF cs))}
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

type OptiM n = State (ConstraintSystem n)

type RoundM n = WriterT WhatChanged (OptiM n)

runOptiM :: ConstraintSystem n -> OptiM n a -> (a, ConstraintSystem n)
runOptiM cs m = runState m cs

runRoundM :: RoundM n a -> OptiM n WhatChanged
runRoundM = execWriterT

markChanged :: WhatChanged -> RoundM n ()
markChanged = tell

-- | Go through additive constraints and classify them into relation constraints when possible.
--   Returns 'True' if the constraint has been reduced.
learnFromAddF :: (GaloisField n, Integral n) => PolyG RefF n -> RoundM n Bool
learnFromAddF poly = case PolyG.view poly of
  PolyG.Monomial intercept (var, slope) -> do
    --    intercept + slope * var = 0
    --  =>
    --    var = - intercept / slope
    bindToValue var (-intercept / slope)
    return True
  PolyG.Binomial intercept (var1, slope1) (var2, slope2) -> do
    --    intercept + slope1 * var1 + slope2 * var2 = 0
    --  =>
    --    slope1 * var1 = - slope2 * var2 - intercept
    --  =>
    --    var1 = - slope2 * var2 / slope1 - intercept / slope1
    relate var1 (-slope2 / slope1, var2, -intercept / slope1)
  PolyG.Polynomial _ _ -> return False

bindToValue :: GaloisField n => RefF -> n -> RoundM n ()
bindToValue var value = do
  markChanged RelationChanged
  modify' $ \cs ->
    cs
      { csVarEqF = UnionFind.bindToValue var value (csVarEqF cs),
        csOccurrenceF = removeOccurrences [var] (csOccurrenceF cs)
      }

-- | Relates two variables. Returns 'True' if a new relation has been established.
relate :: GaloisField n => RefF -> (n, RefF, n) -> RoundM n Bool
relate var1 (slope, var2, intercept) = do
  cs <- get
  case UnionFind.relate var1 (slope, var2, intercept) (csVarEqF cs) of
    Nothing -> return False
    Just unionFind' -> do
      markChanged RelationChanged
      modify' $ \cs' -> cs' {csVarEqF = unionFind', csOccurrenceF = removeOccurrences [var1, var2] (csOccurrenceF cs)}
      return True

addAddF :: (GaloisField n, Integral n) => PolyG RefF n -> RoundM n ()
addAddF poly = case PolyG.view poly of
  PolyG.Monomial constant (var1, coeff1) -> do
    --    constant + coeff1 * var1 = 0
    --      =>
    --    var1 = - constant / coeff1
    bindToValue var1 (-constant / coeff1)
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> do
    --    constant + coeff1 * var1 + coeff2 * var2 = 0
    --      =>
    --    coeff1 * var1 = - coeff2 * var2 - constant
    --      =>
    --    var1 = - coeff2 * var2 / coeff1 - constant / coeff1
    void $ relate var1 (-coeff2 / coeff1, var2, -constant / coeff1)
  PolyG.Polynomial _ _ -> do
    markChanged AdditiveConstraintChanged
    modify' $ \cs' -> cs' {csAddF = poly : csAddF cs'}