module Keelung.Compiler.Compile.Util where

import Control.Monad.Except
import Control.Monad.State
import Data.Either (partitionEithers)
import Data.Field.Galois (GaloisField)
import Keelung (HasWidth (widthOf))
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.LC
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Field (AllRelations)
import Keelung.Compiler.Relations.Field qualified as AllRelations
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Field (FieldType)
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for compilation
type M n = StateT (ConstraintModule n) (Except (Error n))

runM :: GaloisField n => (FieldType, Integer, Integer) -> Counters -> M n a -> Either (Error n) (ConstraintModule n)
runM fieldInfo counters program =
  runExcept
    ( execStateT
        program
        (ConstraintModule fieldInfo counters OccurF.new (OccurB.new False) OccurU.new mempty AllRelations.new mempty mempty mempty mempty mempty)
    )

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\cs -> cs {cmCounters = f (cmCounters cs)})

freshRefF :: M n RefF
freshRefF = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadField)
  modifyCounter $ addCount (Intermediate, WriteField) 1
  return $ RefFX index

freshRefForU :: Ref -> M n Ref
freshRefForU (F _) = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadField)
  modifyCounter $ addCount (Intermediate, WriteField) 1
  return $ F $ RefFX index
freshRefForU (B _) = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadBool)
  modifyCounter $ addCount (Intermediate, WriteBool) 1
  return $ B $ RefBX index
freshRefForU (U ref) = do
  let width = widthOf ref
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadUInt width)
  modifyCounter $ addCount (Intermediate, WriteUInt width) 1
  return $ U $ RefUX width index

freshRefB :: M n RefB
freshRefB = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadBool)
  modifyCounter $ addCount (Intermediate, WriteBool) 1
  return $ RefBX index

freshRefU :: Width -> M n RefU
freshRefU width = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadUInt width)
  modifyCounter $ addCount (Intermediate, WriteUInt width) 1
  return $ RefUX width index

--------------------------------------------------------------------------------

-- | Compile a linear combination of expressions into a polynomial
toPoly :: (GaloisField n, Integral n) => (Expr n -> M n (Either Ref n)) -> (n, [(Expr n, n)]) -> M n (Either n (PolyG Ref n))
toPoly compile (c, xs) = do
  (constants, terms) <- partitionEithers <$> mapM compileTerm xs
  return $ PolyG.build (c + sum constants) terms
  where
    compileTerm (expr, coeff) = do
      result <- compile expr
      case result of
        Left variable -> return $ Right (variable, coeff)
        Right constant -> return $ Left (constant * coeff)

writeMulWithLC :: (GaloisField n, Integral n) => LC n -> LC n -> LC n -> M n ()
writeMulWithLC as bs cs = case (as, bs, cs) of
  (Constant _, Constant _, Constant _) -> return ()
  (Constant x, Constant y, Polynomial zs) ->
    -- z - x * y = 0
    addC [CAddF $ PolyG.addConstant (-x * y) zs]
  (Constant x, Polynomial ys, Constant z) ->
    -- x * ys = z
    -- x * ys - z = 0
    case PolyG.multiplyBy x ys of
      Left _ -> return ()
      Right poly -> addC [CAddF $ PolyG.addConstant (-z) poly]
  (Constant x, Polynomial ys, Polynomial zs) -> do
    -- x * ys = zs
    -- x * ys - zs = 0
    case PolyG.multiplyBy x ys of
      Left c ->
        -- c - zs = 0
        addC [CAddF $ PolyG.addConstant (-c) zs]
      Right ys' -> case PolyG.merge ys' (PolyG.negate zs) of
        Left _ -> return ()
        Right poly -> addC [CAddF poly]
  (Polynomial xs, Constant y, Constant z) -> writeMulWithLC (Constant y) (Polynomial xs) (Constant z)
  (Polynomial xs, Constant y, Polynomial zs) -> writeMulWithLC (Constant y) (Polynomial xs) (Polynomial zs)
  (Polynomial xs, Polynomial ys, _) -> addC [CMulF xs ys (toEither cs)]

writeAddWithPoly :: (GaloisField n, Integral n) => Either n (PolyG Ref n) -> M n ()
writeAddWithPoly xs = case xs of
  Left _ -> return ()
  Right poly -> addC [CAddF poly]

writeAddWithLC :: (GaloisField n, Integral n) => LC n -> M n ()
writeAddWithLC xs = case xs of
  Constant _ -> return ()
  Polynomial poly -> addC [CAddF poly]

addC :: (GaloisField n, Integral n) => [Constraint n] -> M n ()
addC = mapM_ addOne
  where
    execRelations :: (AllRelations n -> EquivClass.M (Error n) (AllRelations n)) -> M n ()
    execRelations f = do
      cs <- get
      result <- lift $ (EquivClass.runM . f) (cmFieldRelations cs)
      case result of
        Nothing -> return ()
        Just relations -> put cs {cmFieldRelations = relations}

    countBitTestAsOccurU :: (GaloisField n, Integral n) => Ref -> M n ()
    countBitTestAsOccurU (B (RefUBit _ (RefUX width var) _)) =
      modify' ( \cs -> cs { cmOccurrenceU = OccurU.increase width var (cmOccurrenceU cs)})
    countBitTestAsOccurU _ = return ()

    addOne :: (GaloisField n, Integral n) => Constraint n -> M n ()
    addOne (CAddF xs) = modify' (\cs -> addOccurrences (PolyG.vars xs) $ cs {cmAddF = xs : cmAddF cs})
    addOne (CVarBindF x c) = do
      execRelations $ AllRelations.assignF x c
    addOne (CVarBindB x c) = do
      countBitTestAsOccurU (B x)
      execRelations $ AllRelations.assignB x c
    addOne (CVarBindU x c) = do
      execRelations $ AllRelations.assignU x c
    addOne (CVarEq x y) = do
      countBitTestAsOccurU x
      countBitTestAsOccurU y
      execRelations $ AllRelations.relateRefs x 1 y 0
    addOne (CVarEqF x y) = do
      execRelations $ AllRelations.relateRefs (F x) 1 (F y) 0
    addOne (CVarEqB x y) = do
      countBitTestAsOccurU (B x)
      countBitTestAsOccurU (B y)
      execRelations $ AllRelations.relateB x (True, y)
    addOne (CVarNEqB x y) = do
      countBitTestAsOccurU (B x)
      countBitTestAsOccurU (B y)
      execRelations $ AllRelations.relateB x (False, y)
    addOne (CVarEqU x y) = do
      execRelations $ AllRelations.assertEqualU x y
    addOne (CMulF x y (Left c)) = modify' (\cs -> addOccurrences (PolyG.vars x) $ addOccurrences (PolyG.vars y) $ cs {cmMulF = (x, y, Left c) : cmMulF cs})
    addOne (CMulF x y (Right z)) = modify (\cs -> addOccurrences (PolyG.vars x) $ addOccurrences (PolyG.vars y) $ addOccurrences (PolyG.vars z) $ cs {cmMulF = (x, y, Right z) : cmMulF cs})

--------------------------------------------------------------------------------

writeMul :: (GaloisField n, Integral n) => (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> M n ()
writeMul as bs cs = writeMulWithLC (fromEither $ uncurry PolyG.build as) (fromEither $ uncurry PolyG.build bs) (fromEither $ uncurry PolyG.build cs)

writeAdd :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> M n ()
writeAdd c as = writeAddWithPoly (PolyG.build c as)

writeVal :: (GaloisField n, Integral n) => Ref -> n -> M n ()
writeVal (F a) x = writeValF a x
writeVal (B a) x = writeValB a (x /= 0)
writeVal (U a) x = writeValU a x

writeValF :: (GaloisField n, Integral n) => RefF -> n -> M n ()
writeValF a x = addC [CVarBindF (F a) x]

writeValB :: (GaloisField n, Integral n) => RefB -> Bool -> M n ()
writeValB a x = addC [CVarBindB a x]

writeValU :: (GaloisField n, Integral n) => RefU -> n -> M n ()
writeValU a x = addC [CVarBindU a x]

writeEq :: (GaloisField n, Integral n) => Ref -> Ref -> M n ()
writeEq a b = addC [CVarEq a b]

writeEqF :: (GaloisField n, Integral n) => RefF -> RefF -> M n ()
writeEqF a b = addC [CVarEqF a b]

writeEqB :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeEqB a b = addC [CVarEqB a b]

writeNEqB :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeNEqB a b = addC [CVarNEqB a b]

writeEqU :: (GaloisField n, Integral n) => RefU -> RefU -> M n ()
writeEqU a b = addC [CVarEqU a b]

--------------------------------------------------------------------------------

-- | Hints
addEqZeroHint :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> RefF -> M n ()
addEqZeroHint c xs m = case PolyG.build c xs of
  Left 0 -> writeValF m 0
  Left constant -> writeValF m (recip constant)
  Right poly -> modify' $ \cs -> cs {cmEqZeros = (poly, m) : cmEqZeros cs}

addEqZeroHintWithPoly :: (GaloisField n, Integral n) => Either n (PolyG Ref n) -> RefF -> M n ()
addEqZeroHintWithPoly (Left 0) m = writeValF m 0
addEqZeroHintWithPoly (Left constant) m = writeValF m (recip constant)
addEqZeroHintWithPoly (Right poly) m = modify' $ \cs -> cs {cmEqZeros = (poly, m) : cmEqZeros cs}

addDivModHint :: (GaloisField n, Integral n) => RefU -> RefU -> RefU -> RefU -> M n ()
addDivModHint x y q r = modify' $ \cs -> cs {cmDivMods = (Left x, Left y, Left q, Left r) : cmDivMods cs}

addModInvHint :: (GaloisField n, Integral n) => RefU -> RefU -> Integer -> M n ()
addModInvHint x n p = modify' $ \cs -> cs {cmModInvs = (Left x, Left n, p) : cmModInvs cs}

addBinRepHint :: (GaloisField n, Integral n) => [(RefB, Int)] -> M n ()
addBinRepHint segments = modify' $ \cs -> cs {cmBinReps = segments : cmBinReps cs}

addBooleanConstraint :: (GaloisField n, Integral n) => RefB -> M n ()
addBooleanConstraint x = writeMulWithLC (1 @ B x) (1 @ B x) (1 @ B x)

--------------------------------------------------------------------------------

-- | Equalities are compiled with inequalities and inequalities with CNEQ constraints.
--    introduce a new variable m
--    if polynomial = 0 then m = 0 else m = recip polynomial
--    Equality:
--      polynomial * m = 1 - out
--      polynomial * out = 0
--    Inequality:
--      polynomial * m = out
--      polynomial * (1 - out) = 0
eqZero :: (GaloisField n, Integral n) => Bool -> LC n -> M n (Either RefB Bool)
eqZero isEq (Constant constant) = return $ Right $ if isEq then constant == 0 else constant /= 0
eqZero isEq (Polynomial polynomial) = do
  m <- freshRefF
  out <- freshRefB
  if isEq
    then do
      writeMulWithLC
        (Polynomial polynomial)
        (1 @ F m)
        (Constant 1 <> neg (1 @ B out))
      writeMulWithLC
        (Polynomial polynomial)
        (1 @ B out)
        mempty
    else do
      writeMulWithLC
        (Polynomial polynomial)
        (1 @ F m)
        (1 @ B out)
      writeMulWithLC
        (Polynomial polynomial)
        (Constant 1 <> neg (1 @ B out))
        mempty
  --  keep track of the relation between (x - y) and m
  addEqZeroHintWithPoly (Right polynomial) m
  return (Left out)
