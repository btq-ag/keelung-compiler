module Keelung.Compiler.Optimize.MinimizeConstraints (run) where

-- import Control.Monad.State

import Control.Monad.State
import Control.Monad.Writer
import Data.Field.Galois (GaloisField)
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import qualified Data.Map.Strict as Map
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind (UnionFind)

run :: (GaloisField n, Integral n) => ConstraintSystem n -> ConstraintSystem n
run = snd . optimizeAddF

-- optimizeAddF :: (GaloisField n, Integral n) => ConstraintSystem n -> (WhatChanged, ConstraintSystem n)
-- optimizeAddF cs =
--   let (changed, cs') = runOptiM cs goThroughAddF
--    in case changed of
--         NothingChanged -> (NothingChanged, cs)
--         RelationChanged -> optimizeAddF cs'
--         AdditiveConstraintChanged -> optimizeAddF cs'
--         MultiplicativeConstraintChanged -> optimizeAddF cs'

optimizeAddF :: (GaloisField n, Integral n) => ConstraintSystem n -> (WhatChanged, ConstraintSystem n)
optimizeAddF cs =
  let (changed, cs') = runOptiM cs goThroughAddF
   in case changed of
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

optimizeMulF :: (GaloisField n, Integral n) => ConstraintSystem n -> (WhatChanged, ConstraintSystem n)
optimizeMulF cs =
  let (changed, cs') = runOptiM cs goThroughMulF
   in case changed of
        NothingChanged -> (changed, cs')
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

-- goThroughNEqF :: (GaloisField n, Integral n) => OptiM n WhatChanged
-- goThroughNEqF = do
--   cs <- get
--   runRoundM $ do
--     csNEqF' <- foldMaybeM reduceNEqF [] (Map.toList (csNEqF cs))
--     modify' $ \cs'' -> cs'' {csNEqF = Map.fromList csNEqF'}

-- type NEqF = ((RefF, RefF), RefF)

-- -- if (x - y) = 0 then m = 0 else m = recip (x - y)
-- reduceNEqF :: (GaloisField n, Integral n) => NEqF -> RoundM n (Maybe NEqF)
-- reduceNEqF ((x, y), m) = do
--   unionFind <- gets csVarEqF
--   let resultX = UnionFind.parentOf unionFind x
--   let resultY = UnionFind.parentOf unionFind y
--   let resultM = UnionFind.parentOf unionFind m

--   case (resultX, resultY, resultM) of
--     (Just (Nothing, _), Just (Nothing, _), Just (Nothing, _)) -> return Nothing
--     (Just (Nothing, xVal), Just (Nothing, yVal), Just (Just (mSlope, mRoot), mIntercept)) ->
--       if (xVal - yVal) == 0
--         then do
--           -- m = 0 = mSlope * mRoot + mIntercept
--           --    =>
--           -- mRoot = - mIntercept / mSlope
--           bindToValue mRoot (-mIntercept / mSlope)
--           return Nothing
--         else do
--           -- mSlope * mRoot + mIntercept  = recip (xVal - yVal)
--           --    =>
--           -- mRoot = (recip (xVal - yVal) - mIntercept) / mSlope
--           bindToValue mRoot ((recip (xVal - yVal) - mIntercept) / mSlope)
--           return Nothing
--     (Nothing, Nothing, Just (Nothing, mVal)) ->
--       -- m == mVal
--       if mVal == 0
--         then do
--           -- x - y = 0
--           _ <- relate x (1, y, 0)
--           return Nothing
--         else do
--           -- m = 1 / (x - y)
--           --    =>
--           -- x - y = 1 / m
--           --    =>
--           -- x = 1 / m + y
--           _ <- relate x (1, y, recip mVal)
--           return Nothing
--     _ -> return (Just ((x, y), m)) -- cannot do anything

foldMaybeM :: Monad m => (a -> m (Maybe a)) -> [a] -> [a] -> m [a]
foldMaybeM f = foldM $ \acc x -> do
  result <- f x
  case result of
    Nothing -> return acc
    Just x' -> return (x' : acc)

reduceAddF :: (GaloisField n, Integral n) => PolyG RefF n -> RoundM n (Maybe (PolyG RefF n))
reduceAddF polynomial = do
  changed <- learnFromAddF polynomial
  if changed
    then return Nothing
    else do
      unionFind <- gets csVarEqF
      case substPolyG unionFind polynomial of
        Nothing -> return (Just polynomial) -- nothing changed
        Just (Left _constant, removedRefs, _) -> do
          -- when (constant /= 0) $
          --   error "[ panic ] Additive reduced to some constant other than 0"
          -- the polynomial has been reduced to nothing
          markChanged AdditiveConstraintChanged
          -- remove all variables in the polynomial from the occurrence list
          modify' $ removeRefFOccurrences removedRefs
          return Nothing
        Just (Right reducePolynomial, removedRefs, addedRefs) -> do
          -- the polynomial has been reduced to something
          markChanged AdditiveConstraintChanged
          -- remove variables that has been reduced in the polynomial from the occurrence list
          modify' $ removeRefFOccurrences removedRefs . addRefFOccurrences addedRefs
          -- keep reducing the reduced polynomial
          reduceAddF reducePolynomial

type MulF n = (PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n))

reduceMulF :: (GaloisField n, Integral n) => (PolyG RefF n, PolyG RefF n, Either n (PolyG RefF n)) -> RoundM n (Maybe (MulF n))
reduceMulF (polyA, polyB, polyC) = do
  polyAResult <- substitutePoly MultiplicativeConstraintChanged polyA
  polyBResult <- substitutePoly MultiplicativeConstraintChanged polyB
  polyCResult <- case polyC of
    Left constantC -> return (Left constantC)
    Right polyC' -> substitutePoly MultiplicativeConstraintChanged polyC'

  reduceMulF_ polyAResult polyBResult polyCResult

substitutePoly :: (GaloisField n, Integral n) => WhatChanged -> PolyG RefF n -> RoundM n (Either n (PolyG RefF n))
substitutePoly typeOfChange polynomial = do
  unionFind <- gets csVarEqF
  case substPolyG unionFind polynomial of
    Nothing -> return (Right polynomial) -- nothing changed
    Just (Left constant, removedRefs, _) -> do
      -- the polynomial has been reduced to nothing
      markChanged typeOfChange
      -- remove all variables in the polynomial from the occurrence list
      modify' $ removeRefFOccurrences removedRefs
      return (Left constant)
    Just (Right reducePolynomial, removedRefs, addedRefs) -> do
      -- the polynomial has been reduced to something
      markChanged typeOfChange
      -- remove all variables in the polynomial from the occurrence list
      modify' $ removeRefFOccurrences removedRefs . addRefFOccurrences addedRefs
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
    Left _constant -> modify' $ removeRefFOccurrences (PolyG.vars bs)
    Right xs -> addAddF $ PolyG.addConstant c xs

-- | Trying to reduce a multiplicative constaint of (Constant / Polynomial / Polynomial)
--    a * bs = cs
--      =>
--    cs - a * bs = 0
reduceMulFCPP :: (GaloisField n, Integral n) => n -> PolyG RefF n -> PolyG RefF n -> RoundM n ()
reduceMulFCPP a polyB polyC = do
  case PolyG.multiplyBy (-a) polyB of
    Left _constant -> do
      modify' $ removeRefFOccurrences (PolyG.vars polyB)
      addAddF polyC
    Right polyBa -> do
      case PolyG.merge polyC polyBa of
        Left _constant -> modify' $ removeRefFOccurrences (PolyG.vars polyC) . removeRefFOccurrences (PolyG.vars polyBa)
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
    removeRefFOccurrences [var] $
      cs
        { csVarEqF = UnionFind.bindToValue var value (csVarEqF cs)
        }

-- | Relates two variables. Returns 'True' if a new relation has been established.
relate :: GaloisField n => RefF -> (n, RefF, n) -> RoundM n Bool
relate var1 (slope, var2, intercept) = do
  cs <- get
  case UnionFind.relate var1 (slope, var2, intercept) (csVarEqF cs) of
    Nothing -> return False
    Just unionFind' -> do
      markChanged RelationChanged
      modify' $ \cs' -> removeRefFOccurrences [var1, var2] $ cs' {csVarEqF = unionFind'}
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

--------------------------------------------------------------------------------

-- | Substitutes variables in a polynomial.
--   Returns 'Nothing' if nothing changed else returns the substituted polynomial and the list of substituted variables.
substPolyG :: (GaloisField n, Integral n, Ord ref, Show ref) => UnionFind ref n -> PolyG ref n -> Maybe (Either n (PolyG ref n), [ref], [ref])
substPolyG ctx poly = do
  let (c, xs) = PolyG.viewAsMap poly
  case Map.foldlWithKey' (substPolyG_ ctx) (False, Left c, [], []) xs of
    (False, _, _, _) -> Nothing -- nothing changed
    (True, Left constant, removedRefs, addedRefs) -> Just (Left constant, removedRefs, addedRefs) -- the polynomial has been reduced to a constant
    (True, Right poly', removedRefs, addedRefs) -> Just (Right poly', removedRefs, addedRefs)

substPolyG_ :: (Integral n, Ord ref, Show ref, GaloisField n) => UnionFind ref n -> (Bool, Either n (PolyG ref n), [ref], [ref]) -> ref -> n -> (Bool, Either n (PolyG ref n), [ref], [ref])
substPolyG_ ctx (changed, accPoly, removedRefs, addedRefs) ref coeff = case UnionFind.parentOf ctx ref of
  Nothing ->
    -- ref is already a root
    case accPoly of
      Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
      Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
  Just (Nothing, intercept) ->
    -- ref = intercept
    let removedRefs' = ref : removedRefs -- add ref to removedRefs
     in case accPoly of
          Left c -> (True, Left (intercept * coeff + c), removedRefs', addedRefs)
          Right accPoly' -> (True, Right $ PolyG.addConstant (intercept * coeff) accPoly', removedRefs', addedRefs)
  Just (Just (slope, root), intercept) ->
    if root == ref
      then
        if slope == 1 && intercept == 0
          then -- ref = root, nothing changed
          case accPoly of
            Left c -> (changed, PolyG.singleton c (ref, coeff), removedRefs, addedRefs)
            Right xs -> (changed, PolyG.insert 0 (ref, coeff) xs, removedRefs, addedRefs)
          else error "[ panic ] Invalid relation in UnionFind: ref = slope * root + intercept, but slope /= 1 || intercept /= 0"
      else
        let removedRefs' = ref : removedRefs
            addedRefs' = root : addedRefs
         in case accPoly of
              -- ref = slope * root + intercept
              Left c -> (True, PolyG.singleton (intercept * coeff + c) (root, slope * coeff), removedRefs', addedRefs')
              Right accPoly' -> (True, PolyG.insert (intercept * coeff) (root, slope * coeff) accPoly', removedRefs', addedRefs')
