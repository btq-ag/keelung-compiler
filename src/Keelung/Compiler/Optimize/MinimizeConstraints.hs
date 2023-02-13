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
    csAddF' <- foldM goThroughAddFM [] (csAddF cs)
    modify' $ \cs'' -> cs'' {csAddF = csAddF'}
  where
    goThroughAddFM :: (GaloisField n, Integral n) => [PolyG RefF n] -> PolyG RefF n -> RoundM n [PolyG RefF n]
    goThroughAddFM acc poly = do
      changed <- learnFromAddF poly
      if changed
        then return acc
        else do
          unionFind <- gets csVarEqF
          case substPolyG unionFind poly of
            Nothing -> return (poly : acc) -- nothing changed
            Just (Nothing, substitutedRefs) -> do
              -- the polynomial has been reduced to nothing
              markChanged AdditiveConstraintChanged
              -- remove all variables in the polynomial from the occurrence list
              modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
              return acc
            Just (Just poly', substitutedRefs) -> do
              -- the polynomial has been reduced to something
              markChanged AdditiveConstraintChanged
              modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs (csOccurrenceF cs)}
              return (poly' : acc)

-- type MulF n = (PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))

-- goThroughMulF :: (GaloisField n, Integral n) => [MulF n] -> MulF n -> RoundM n [MulF n]
-- goThroughMulF acc (a, b, Left c) = do
--   unionFind <- gets csVarEqF
--   case substPolyG unionFind a of
--     Nothing -> return ((a, b, Left c) : acc)
--     Just (a', substitutedRefs) -> do
--       markChanged MultiplicativeConstraintChanged
--       modify' $ \cs -> cs {csOccurrenceF = removeOccurrences substitutedRefs $ removeOccurrencesWithPolyG a' (csOccurrenceF cs)}
--       return ((a', b, Left c) : acc)
-- goThroughMulF acc (a, b, Right c) = _

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
  (_, []) -> error "[ panic ] Empty polynomial"
  (intercept, [(var, slope)]) -> do
    --    intercept + slope * var = 0
    --  =>
    --    var = - intercept / slope
    markChanged RelationChanged

    modify' $ \cs ->
      cs
        { csVarEqF = UnionFind.bindToValue var (-intercept / slope) (csVarEqF cs),
          csOccurrenceF = removeOccurrences [var] (csOccurrenceF cs)
        }
    return True
  (intercept, [(var1, slope1), (var2, slope2)]) -> do
    --    intercept + slope1 * var1 + slope2 * var2 = 0
    --  =>
    --    slope1 * var1 = - slope2 * var2 - intercept
    --  =>
    --    var1 = - slope2 * var2 / slope1 - intercept / slope1
    cs <- get
    case UnionFind.relate var1 (-slope2 / slope1, var2, -intercept / slope1) (csVarEqF cs) of
      Nothing -> return False
      Just unionFind' -> do
        markChanged RelationChanged
        modify' $ \cs' -> cs' {csVarEqF = unionFind', csOccurrenceF = removeOccurrences [var1, var2] (csOccurrenceF cs)}
        return True
  (_, _) -> return False

-- learnFromMulF1 :: (GaloisField n, Integral n) => PolyG RefF n -> PolyG RefF n -> n -> RoundM n Bool
-- learnFromMulF1 poly1 poly2 constant = case PolyG.view a of
--   (_, []) -> error "[ panic ] Empty polynomial"
--   (intercept, [(var, slope)]) -> do
--     --    intercept + slope * var = 0
--     --  =>
--     --    var = - intercept / slope
--     markChanged RelationChanged

--     modify' $ \cs ->
--       cs
--         { csVarEqF = UnionFind.bindToValue var (-intercept / slope) (csVarEqF cs),
--           csOccurrenceF = removeOccurrences [var] (csOccurrenceF cs)
--         }
--     return True

-- cs <- get
-- case UnionFind.relate a (c, b) (csVarEqF cs) of
--   Nothing -> return False
--   Just unionFind' -> do
--     markChanged RelationChanged
--     modify' $ \cs' -> cs' {csVarEqF = unionFind'}
--     return True