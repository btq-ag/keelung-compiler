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
run_ (AdditiveConstraintChanged, cs) = run_ $ runOptiM cs goThroughAddF
run_ (MultiplicativeConstraintChanged, cs) = run_ $ runOptiM cs goThroughAddF

goThroughAddF :: (GaloisField n, Integral n) => OptiM n WhatChanged
goThroughAddF = do
  cs <- get
  runRoundM $ do
    csAddF' <- foldMaybeM goThroughAddFM [] (csAddF cs)
    modify' $ \cs'' -> cs'' {csAddF = csAddF'}

foldMaybeM :: Monad m => (a -> m (Maybe a)) -> [a] -> [a] -> m [a]
foldMaybeM f = foldM $ \acc x -> do
  result <- f x
  case result of
    Nothing -> return acc
    Just x' -> return (x' : acc)

goThroughAddFM :: (GaloisField n, Integral n) => PolyG RefF n -> RoundM n (Maybe (PolyG RefF n))
goThroughAddFM poly = do
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
          modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
          return (Just poly')

-- data OccurrenceChange = OccurrenceChange
--   { ocAdded :: [RefF]
--   , ocRemoved :: [RefF]
--   }

type MulF n = (PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))

-- | Trying to reduce a multiplicative constaint of (Constant / Constant / Polynomial)
reduceMulFCCP :: (GaloisField n, Integral n) => n -> n -> PolyG RefF n -> RoundM n (Maybe (MulF n))
reduceMulFCCP a b cs = case PolyG.view cs of
  PolyG.Monomial constant (var1, coeff1) -> do
    -- a * b = constant + var1 * coeff1
    --    =>
    -- (a * b - constant) / coeff1 = var1
    bindToValue var1 ((a * b - constant) / coeff1)
    return Nothing
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> do
    -- a * b = constant + var1 * coeff1 + var2 * coeff2
    --    =>
    -- (a * b - constant - var2 * coeff2) / coeff1 = var1
    --    =>
    -- var1 = (a * b - constant) / coeff1 - (coeff2 * var2) / coeff1
    _relationEstablished <- relate var1 (coeff2 / coeff1, var2, (a * b - constant) / coeff1)
    return Nothing
  PolyG.Polynomial _ _ -> do
    -- a * b = constant + xs
    --    =>
    -- xs + constant - a * b = 0
    addAddF (PolyG.addConstant (-a * b) cs)
    return Nothing

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Constant)
reduceMulFCPC :: (GaloisField n, Integral n) => n -> PolyG RefF n -> n -> RoundM n (Maybe (MulF n))
reduceMulFCPC a bs c = case PolyG.view bs of
  PolyG.Monomial constant (var1, coeff1) -> do
    -- a * (constant + coeff1 * var1) = c
    --    =>
    -- a * coeff1 * var1 = c - a * constant
    --    =>
    -- var1 = (c - a * constant) / (a * coeff1)
    bindToValue var1 ((c - a * constant) / (a * coeff1))
    return Nothing
  PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> do
    -- a * (constant + coeff1 * var1 + coeff2 * var2) = c
    --    =>
    -- constant + coeff1 * var1 + coeff2 * var2 = c / a
    --    =>
    -- var1 = (c / a - constant - coeff2 * var2) / coeff1
    _relationEstablished <- relate var1 (coeff2 / coeff1, var2, (c / a - constant) / coeff1)
    return Nothing
  PolyG.Polynomial _ _ -> do
    -- a * (constant + xs) = c
    --    =>
    -- a * constant - c + a * xs = 0
    addAddF (PolyG.addConstant (-c) $ PolyG.multiplyBy a bs)
    return Nothing

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Polynomial)
-- reduceMulFCPP :: (GaloisField n, Integral n) => n -> PolyG RefF n -> PolyG RefF n -> RoundM n (Maybe (MulF n))
-- reduceMulFCPP a bs cs = case (PolyG.view bs, PolyG.view cs) of
--   (PolyG.Monomial constant1 (var1, coeff1), PolyG.Monomial constant2 (var2, coeff2)) -> do
--     -- a * (constant1 + coeff1 * var1) = constant2 + coeff2 * var2
--     --    =>
--     -- a * constant1 + a * coeff1 * var1 = constant2 + coeff2 * var2
--     --    =>
--     -- var1 = (constant2 + coeff2 * var2 - a * constant1) / a * coeff1
--     --    =>
--     -- var1 = (constant2 - a * constant1) / a * coeff1 + (coeff2 * var2) / a * coeff1
--     _ <- relate var1 (coeff2 / (a * coeff1), var2, (constant2 - a * constant1) / (a * coeff1))
--     return Nothing
--   (PolyG.Monomial constant1 (var1, coeff1), PolyG.Binomial constant2 (var2, coeff2) (var3, coeff3)) -> do
--     -- a * (constant1 + coeff1 * var1) = constant2 + coeff2 * var2 + coeff3 * var3
--     --    =>
--     -- a * constant1 + a * coeff1 * var1 = constant2 + coeff2 * var2 + coeff3 * var3
--     --    =>
--     -- (a * constant1 - constant2) + a * coeff1 * var1 + coeff2 * var2 + coeff3 * var3 = 0
--     case PolyG.build (a * constant1 - constant2) [(var1, a * coeff1), (var2, coeff2), (var3, coeff3)] of
--       Left _constant -> return Nothing
--       Right addF -> do
--         addAddF addF
--         return Nothing
--   (PolyG.Monomial constant1 (var1, coeff1), _) -> do
--     -- a * constant1 + a * coeff1 * var1 = cs 


--   _ -> return Nothing

-- PolyG.Binomial constant (var1, coeff1) (var2, coeff2) -> do
--   -- a * (constant + coeff1 * var1 + coeff2 * var2) = c + xs
--   --    =>
--   -- constant + coeff1 * var1 + coeff2 * var2 = c / a + xs
--   --    =>
--   -- var1 = (c / a + xs - constant - coeff2 * var2) / coeff1
--   _relationEstablished <- relate var1 (coeff2 / coeff1, var2, (c / a + xs - constant) / coeff1)
--   return Nothing
-- PolyG.Polynomial _ _ -> do
--   -- a * (constant + xs) = c + ys
--   --    =>
--   -- a * constant - c + a * xs = ys
--   cs <- get
--   markChanged AdditiveConstraintChanged
--   let newAddF = PolyG.addConstant (-c) $ PolyG.multiplyBy a b
--   modify' $ \cs'' -> cs'' {csAddF = newAddF : csAddF cs}
--   return Nothing

reduceMulF :: (GaloisField n, Integral n) => Either n (PolyG RefF n) -> Either n (PolyG RefF n) -> Either n (PolyG RefF n) -> RoundM n (Maybe (MulF n))
reduceMulF (Left _a) (Left _b) (Left _c) = return Nothing
reduceMulF (Left a) (Left b) (Right c) = reduceMulFCCP a b c
reduceMulF (Left 0) (Right _) (Left _) = return Nothing
reduceMulF (Left a) (Right b) (Left c) = reduceMulFCPC a b c
reduceMulF (Left a) (Right b) (Right c) = return Nothing -- reduceMulFCPP a b c
reduceMulF (Right _a) (Left _b) (Left _c) = return Nothing
reduceMulF (Right _a) (Left _b) (Right _c) = return Nothing
reduceMulF (Right _a) (Right _b) (Left _c) = return Nothing
reduceMulF (Right _a) (Right _b) (Right _c) = return Nothing

-- bindToValue
-- modify' $ \cs ->
--   cs
--     { csVarEqF = UnionFind.bindToValue var (-intercept / slope) (csVarEqF cs),
--       csOccurrenceF = removeOccurrences [var] (csOccurrenceF cs)
--     }
-- return Nothing

-- do
-- changed <- learnFromAddF poly
-- if changed
--   then return acc
--   else do
--     unionFind <- gets csVarEqF
--     case substPolyG unionFind poly of
--       Nothing -> return (poly : acc)
--       Just (poly', substitutedRefs) -> do
--         markChanged AdditiveConstraintChanged
--         modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs $ removeOccurrencesWithPolyG poly' (csOccurrenceF cs)}
--         return (poly' : acc)

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
addAddF poly = do
  markChanged AdditiveConstraintChanged
  modify' $ \cs' -> cs' {csAddF = poly : csAddF cs'}