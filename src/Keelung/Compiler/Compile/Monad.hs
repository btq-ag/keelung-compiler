module Keelung.Compiler.Compile.Monad where

import Control.Arrow (right)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Sequence qualified as Seq
import Keelung (widthOf)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Optimize.OccurUB qualified as OccurUB
import Keelung.Compiler.Options
import Keelung.Compiler.Relations (Relations)
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Constraint
import Keelung.Data.LC
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyL (PolyL)
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Data.Slice (Slice)
import Keelung.Data.Slice qualified as Slice
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for compilation
type M n = ReaderT (BootstrapCompiler n) (StateT (ConstraintModule n) (Except (Error n)))

-- | Run the monad
runM :: (GaloisField n) => Options -> BootstrapCompiler n -> Counters -> M n a -> Either (Error n) (ConstraintModule n)
runM options compilers counters program =
  runExcept
    ( execStateT
        (runReaderT program compilers)
        (ConstraintModule options (tempSetFlag counters (optUseNewLinker options)) OccurF.new (OccurB.new False) OccurU.new OccurUB.new (Relations.new options) mempty mempty mempty mempty mempty mempty)
    )

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\cs -> cs {cmCounters = f (cmCounters cs)})

freshRefF :: M n RefF
freshRefF = do
  counters <- gets cmCounters
  let index = getCount counters (Intermediate, ReadField)
  modifyCounter $ addCount (Intermediate, WriteField) 1
  return $ RefFX index

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
  useNewLinker <- gets (optUseNewLinker . cmOptions)
  if useNewLinker
    then do
      modifyCounter $ addCount (Intermediate, WriteUInt width) width
      if width == 0
        then return $ RefUX width index -- TODO: examine if allocating a RefU of width 0 is even necessary
        else return $ RefUX width (index `div` width)
    else do
      modifyCounter $ addCount (Intermediate, WriteUInt width) 1
      return $ RefUX width index

--------------------------------------------------------------------------------

-- | We want to break the compilation module into smaller modules,
--   but Haskell forbids mutually recursive modules,
--   and functions in these small modules are mutually dependent on each other.
--   One way to do this is by "tying the knot" with a recursive data type.
data BootstrapCompiler n = BootstrapCompiler
  { boostrapCompileF :: ExprF n -> M n (LC n),
    boostrapCompileB :: ExprB n -> M n (Either RefB Bool),
    boostrapCompileU :: RefU -> ExprU n -> M n ()
  }

-- | For extracting the bootstrapped ExprB compiler
compileExprB :: (GaloisField n, Integral n) => ExprB n -> M n (Either RefB Bool)
compileExprB expr = do
  compiler <- asks boostrapCompileB
  compiler expr

-- | For extracting the bootstrapped ExprF compiler
compileExprF :: (GaloisField n, Integral n) => ExprF n -> M n (LC n)
compileExprF expr = do
  compiler <- asks boostrapCompileF
  compiler expr

-- | For extracting the bootstrapped ExprU compiler
compileExprU :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compileExprU out expr = do
  compiler <- asks boostrapCompileU
  compiler out expr

--------------------------------------------------------------------------------

writeMulWithLC :: (GaloisField n, Integral n) => LC n -> LC n -> LC n -> M n ()
writeMulWithLC as bs cs = case (as, bs, cs) of
  (Constant _, Constant _, Constant _) -> return ()
  (Constant x, Constant y, Polynomial zs) ->
    -- z - x * y = 0
    addC [CAddL $ PolyL.addConstant (-x * y) zs]
  (Constant x, Polynomial ys, Constant z) ->
    -- x * ys = z
    -- x * ys - z = 0
    case PolyL.multiplyBy x ys of
      Left _ -> return ()
      Right poly -> addC [CAddL $ PolyL.addConstant (-z) poly]
  (Constant x, Polynomial ys, Polynomial zs) -> do
    -- x * ys = zs
    -- x * ys - zs = 0
    case PolyL.multiplyBy x ys of
      Left c ->
        -- c - zs = 0
        addC [CAddL $ PolyL.addConstant (-c) zs]
      Right ys' -> case PolyL.merge ys' (PolyL.negate zs) of
        Left _ -> return ()
        Right poly -> addC [CAddL poly]
  (Polynomial xs, Constant y, Constant z) -> writeMulWithLC (Constant y) (Polynomial xs) (Constant z)
  (Polynomial xs, Constant y, Polynomial zs) -> writeMulWithLC (Constant y) (Polynomial xs) (Polynomial zs)
  (Polynomial xs, Polynomial ys, _) -> addC [CMulL xs ys (toPolyL cs)]

writeAddWithPolyL :: (GaloisField n, Integral n) => Either n (PolyL n) -> M n ()
writeAddWithPolyL xs = case xs of
  Left _ -> return ()
  Right poly -> addC [CAddL poly]

writeAddWithLC :: (GaloisField n, Integral n) => LC n -> M n ()
writeAddWithLC xs = case xs of
  Constant _ -> return ()
  Polynomial poly -> addC [CAddL poly]

writeAddWithLCAndLimbs :: (GaloisField n, Integral n) => LC n -> n -> [(Limb, n)] -> M n ()
writeAddWithLCAndLimbs lc constant limbs = case lc of
  Constant _ -> return ()
  Polynomial poly -> addC [CAddL (PolyL.insertLimbs constant limbs poly)]

addC :: (GaloisField n, Integral n) => [Constraint n] -> M n ()
addC = mapM_ addOne
  where
    execRelations :: (Relations n -> EquivClass.M (Error n) (Relations n)) -> M n ()
    execRelations f = do
      cs <- get
      result <- lift $ lift $ (EquivClass.runM . f) (cmRelations cs)
      case result of
        Nothing -> return ()
        Just relations -> put cs {cmRelations = relations}

    countBitTestAsOccurU :: (GaloisField n, Integral n) => Ref -> M n ()
    countBitTestAsOccurU (B (RefUBit (RefUX width var) _)) = do
      useNewLinker <- gets (optUseNewLinker . cmOptions)
      if useNewLinker
        then return ()
        else modify' (\cs -> cs {cmOccurrenceU = OccurU.increase width var (cmOccurrenceU cs)})
    countBitTestAsOccurU _ = return ()

    addOne :: (GaloisField n, Integral n) => Constraint n -> M n ()
    addOne (CAddL xs) = do
      modify' (\cs -> addOccurrencesTuple (PolyL.varsSet xs) $ cs {cmAddL = xs Seq.<| cmAddL cs})
    addOne (CRefFVal x c) = do
      execRelations $ Relations.assignR x c
    addOne (CLimbVal x c) = do
      execRelations $ Relations.assignL x c
    addOne (CRefUVal x c) = do
      execRelations $ Relations.assignU x c
    addOne (CSliceVal x c) = do
      execRelations $ Relations.assignS x c
    addOne (CRefEq x y) = do
      countBitTestAsOccurU x
      countBitTestAsOccurU y
      execRelations $ Relations.relateR x 1 y 0
    addOne (CLimbEq x y) = do
      execRelations $ Relations.relateL x y
    addOne (CRefUEq x y) = do
      execRelations $ Relations.relateU x y
    addOne (CSliceEq x y) = do
      execRelations $ Relations.relateS x y
    addOne (CRefBNEq x y) = do
      countBitTestAsOccurU (B x)
      countBitTestAsOccurU (B y)
      execRelations $ Relations.relateB x (False, y)
    addOne (CMulL x y (Left c)) = modify' (\cs -> addOccurrencesTuple (PolyL.varsSet x) $ addOccurrencesTuple (PolyL.varsSet y) $ cs {cmMulL = (x, y, Left c) Seq.<| cmMulL cs})
    addOne (CMulL x y (Right z)) = modify (\cs -> addOccurrencesTuple (PolyL.varsSet x) $ addOccurrencesTuple (PolyL.varsSet y) $ addOccurrencesTuple (PolyL.varsSet z) $ cs {cmMulL = (x, y, Right z) Seq.<| cmMulL cs})

--------------------------------------------------------------------------------

writeMul :: (GaloisField n, Integral n) => (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> M n ()
writeMul as bs cs = writeMulWithLC (fromPolyL $ uncurry PolyL.fromRefs as) (fromPolyL $ uncurry PolyL.fromRefs bs) (fromPolyL $ uncurry PolyL.fromRefs cs)

writeMulWithLimbs :: (GaloisField n, Integral n) => (n, [(Limb, n)]) -> (n, [(Limb, n)]) -> (n, [(Limb, n)]) -> M n ()
writeMulWithLimbs as bs cs = case (uncurry PolyL.fromLimbs as, uncurry PolyL.fromLimbs bs) of
  (Right as', Right bs') ->
    addC
      [ CMulL as' bs' (uncurry PolyL.fromLimbs cs)
      ]
  _ -> return ()

writeAdd :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> M n ()
writeAdd c as = writeAddWithPolyL (PolyL.fromRefs c as)

writeAddWithLimbs :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> [(Limb, n)] -> M n ()
writeAddWithLimbs constant refs limbs = case PolyL.fromLimbs constant limbs of
  Left _ -> return ()
  Right poly -> case PolyL.insertRefs 0 refs poly of
    Left _ -> return ()
    Right poly' -> addC [CAddL poly']

-- | Assign a field element to a Ref
writeRefVal :: (GaloisField n, Integral n) => Ref -> n -> M n ()
writeRefVal (F a) x = writeRefFVal a x
writeRefVal (B a) x = writeRefBVal a (x /= 0)

-- | Assign a field element to a RefF
writeRefFVal :: (GaloisField n, Integral n) => RefF -> n -> M n ()
writeRefFVal a x = addC [CRefFVal (F a) x]

-- | Assign a Bool to a RefB
writeRefBVal :: (GaloisField n, Integral n) => RefB -> Bool -> M n ()
writeRefBVal a True = addC [CRefFVal (B a) 1]
writeRefBVal a False = addC [CRefFVal (B a) 0]

-- | Assert that two RefBs are equal
writeRefBEq :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeRefBEq a b = addC [CRefEq (B a) (B b)]

writeRefB :: (GaloisField n, Integral n) => RefB -> Either RefB Bool -> M n ()
writeRefB a (Left b) = writeRefBEq a b
writeRefB a (Right b) = writeRefBVal a b

-- | Assert that two Refs are equal
writeRefEq :: (GaloisField n, Integral n) => Ref -> Ref -> M n ()
writeRefEq a b = addC [CRefEq a b]

-- | Assert that two RefFs are equal
writeRefFEq :: (GaloisField n, Integral n) => RefF -> RefF -> M n ()
writeRefFEq a b = addC [CRefEq (F a) (F b)]

-- | Assert that one RefB is the negation of another RefB
writeRefBNEq :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeRefBNEq a b = addC [CRefBNEq a b]

-- | Assign a Integer to a RefU
writeRefUVal :: (GaloisField n, Integral n) => RefU -> U -> M n ()
writeRefUVal a x = do
  useUIntUnionFind <- gets (optUseUIntUnionFind . cmOptions)
  if useUIntUnionFind
    then addC [CSliceVal (Slice.fromRefU a) (toInteger x)]
    else addC [CRefUVal a (toInteger x)]

-- | Assign an Integer to a Limb
writeLimbVal :: (GaloisField n, Integral n) => Limb -> Integer -> M n ()
writeLimbVal a x = do
  useUIntUnionFind <- gets (optUseUIntUnionFind . cmOptions)
  if useUIntUnionFind
    then addC [CSliceVal (Slice.fromLimb a) x]
    else addC [CLimbVal a x]

-- | Assign an Integer to a Slice
writeSliceVal :: (GaloisField n, Integral n) => Slice -> Integer -> M n ()
writeSliceVal a x = addC [CSliceVal a x]

-- | Assert that two RefUs are equal
writeRefUEq :: (GaloisField n, Integral n) => RefU -> RefU -> M n ()
writeRefUEq a b = do
  useUIntUnionFind <- gets (optUseUIntUnionFind . cmOptions)
  if useUIntUnionFind
    then addC [CSliceEq (Slice.fromRefU a) (Slice.fromRefU b)]
    else addC [CRefUEq a b]

-- | Assert that two Limbs are equal
writeLimbEq :: (GaloisField n, Integral n) => Limb -> Limb -> M n ()
writeLimbEq a b = do
  useUIntUnionFind <- gets (optUseUIntUnionFind . cmOptions)
  if useUIntUnionFind
    then addC [CSliceEq (Slice.fromLimb a) (Slice.fromLimb b)]
    else addC [CLimbEq a b]

-- | Assert that two Slices are equal
writeSliceEq :: (GaloisField n, Integral n) => Slice -> Slice -> M n ()
writeSliceEq a b =
  if widthOf a == widthOf b
    then addC [CSliceEq a b]
    else error $ "[ panic ] writeSliceEq: width mismatch, " <> show (widthOf a) <> " /= " <> show (widthOf b)

--------------------------------------------------------------------------------

-- | Hints
addEqZeroHint :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> RefF -> M n ()
addEqZeroHint c xs m = case PolyL.fromRefs c xs of
  Left 0 -> writeRefFVal m 0
  Left constant -> writeRefFVal m (recip constant)
  Right poly -> modify' $ \cs -> cs {cmEqZeros = (poly, m) Seq.<| cmEqZeros cs}

addEqZeroHintWithPoly :: (GaloisField n, Integral n) => Either n (PolyL n) -> RefF -> M n ()
addEqZeroHintWithPoly (Left 0) m = writeRefFVal m 0
addEqZeroHintWithPoly (Left constant) m = writeRefFVal m (recip constant)
addEqZeroHintWithPoly (Right poly) m = modify' $ \cs -> cs {cmEqZeros = (poly, m) Seq.<| cmEqZeros cs}

addDivModHint :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> Either RefU U -> Either RefU U -> M n ()
addDivModHint x y q r = modify' $ \cs -> cs {cmDivMods = (x, y, q, r) Seq.<| cmDivMods cs}

addCLDivModHint :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> Either RefU U -> Either RefU U -> M n ()
addCLDivModHint x y q r = modify' $ \cs -> cs {cmCLDivMods = (x, y, q, r) Seq.<| cmCLDivMods cs}

-- | Width of all values are doubled in this hint
addModInvHint :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> Either RefU U -> U -> M n ()
addModInvHint a output n p = modify' $ \cs -> cs {cmModInvs = (right (U.widen (widthOf p)) a, right (U.widen (widthOf p)) output, right (U.widen (widthOf p)) n, U.widen (widthOf p) p) Seq.<| cmModInvs cs}

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
        (Constant 0)
    else do
      writeMulWithLC
        (Polynomial polynomial)
        (1 @ F m)
        (1 @ B out)
      writeMulWithLC
        (Polynomial polynomial)
        (Constant 1 <> neg (1 @ B out))
        (Constant 0)
  --  keep track of the relation between (x - y) and m
  addEqZeroHintWithPoly (Right polynomial) m
  return (Left out)

--------------------------------------------------------------------------------

-- | Allocates a carry limb with the given signs
allocCarryLimb :: (GaloisField n, Integral n) => Width -> [Bool] -> M n Limb
allocCarryLimb w signs = do
  refU <- freshRefU w
  return $ Limb.new refU w 0 (Right signs)

-- | Allocates an ordinary positie limb
allocLimb :: (GaloisField n, Integral n) => Width -> M n Limb
allocLimb w = do
  refU <- freshRefU w
  return $ Limb.new refU w 0 (Left True)