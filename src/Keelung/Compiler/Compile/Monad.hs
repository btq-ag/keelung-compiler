module Keelung.Compiler.Compile.Monad where

import Control.Arrow (right)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import Keelung (widthOf)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Options
import Keelung.Compiler.Relations (Relations)
import Keelung.Compiler.Relations qualified as Relations
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.LC (LC (..), neg, (@))
import Keelung.Data.LC qualified as LC
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
        ( ConstraintModule
            options
            (tempSetFlag counters True)
            OccurF.new
            (OccurB.new False)
            OccurU.new
            (Relations.new options)
            mempty
            mempty
            mempty
            mempty
            mempty
        )
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
  modifyCounter $ addCount (Intermediate, WriteUInt width) 1
  return $ RefUX width index

execRelations :: (Relations n -> EquivClass.M (Error n) (Relations n)) -> M n ()
execRelations f = do
  cs <- get
  result <- lift $ lift $ (EquivClass.runM . f) (cmRelations cs)
  case result of
    Nothing -> return ()
    Just relations -> put cs {cmRelations = relations}

-- | When a RefUBit is detected, we want to count it as an occurrence
addOccurrenceOnRefUBit :: (GaloisField n, Integral n) => Ref -> M n ()
addOccurrenceOnRefUBit (B (RefUBit (RefUX width var) i)) = modify' (\cs -> cs {cmOccurrenceU = OccurU.increase width var (i, i + 1) (cmOccurrenceU cs)})
addOccurrenceOnRefUBit _ = return ()

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

-- | Given a constant, a list of Refs, and a list of Slices, write a addative constraint of the sum
writeAdd :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> [(Slice, n)] -> M n ()
writeAdd constant refs slices = writeAddWithLC $ LC.new constant refs slices

writeAddWithPolyL :: (GaloisField n, Integral n) => Either n (PolyL n) -> M n ()
writeAddWithPolyL xs = case xs of
  Left 0 -> return ()
  Left n -> error $ "[ panic ] writeAddWithPolyL: expect constant to be 0, got " <> show n
  Right poly -> modify' (\cs -> addOccurrence poly $ cs {cmAddL = poly Seq.<| cmAddL cs})

writeAddWithLC :: (GaloisField n, Integral n) => LC n -> M n ()
writeAddWithLC xs = case xs of
  Constant _ -> return ()
  Polynomial poly -> modify' (\cs -> addOccurrence poly $ cs {cmAddL = poly Seq.<| cmAddL cs})

writeAddWithLimbs :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> [(Limb, n)] -> M n ()
writeAddWithLimbs constant refs limbs = case PolyL.fromLimbs constant limbs of
  Left _ -> return ()
  Right poly -> writeAddWithLC $ Polynomial poly <> LC.new 0 refs []

--------------------------------------------------------------------------------

writeMul :: (GaloisField n, Integral n) => (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> M n ()
writeMul as bs cs = writeMulWithPolyL (uncurry PolyL.fromRefs as) (uncurry PolyL.fromRefs bs) (uncurry PolyL.fromRefs cs)

writeMulWithLC :: (GaloisField n, Integral n) => LC n -> LC n -> LC n -> M n ()
writeMulWithLC as bs cs = writeMulWithPolyL (convert as) (convert bs) (convert cs)
  where
    convert :: LC n -> Either n (PolyL n)
    convert (Constant x) = Left x
    convert (Polynomial xs) = Right xs

writeMulWithPolyL :: (GaloisField n, Integral n) => Either n (PolyL n) -> Either n (PolyL n) -> Either n (PolyL n) -> M n ()
writeMulWithPolyL (Left x) (Left y) (Left z) =
  if x * y == z
    then return ()
    else error "[ panic ] writeMulWithPolyL: constant mismatch"
writeMulWithPolyL (Left x) (Left y) (Right zs) =
  -- zs - x * y = 0
  writeAddWithPolyL $ Right $ PolyL.addConstant (-x * y) zs
writeMulWithPolyL (Left x) (Right ys) (Left z) =
  -- x * ys = z
  -- x * ys - z = 0
  case PolyL.multiplyBy x ys of
    Left _ -> return ()
    Right poly -> writeAddWithPolyL $ Right $ PolyL.addConstant (-z) poly
writeMulWithPolyL (Left x) (Right ys) (Right zs) = do
  -- x * ys = zs
  -- x * ys - zs = 0
  case PolyL.multiplyBy x ys of
    Left c ->
      -- c - zs = 0
      writeAddWithPolyL $ Right $ PolyL.addConstant (-c) zs
    Right ys' -> writeAddWithPolyL $ PolyL.merge ys' (PolyL.negate zs)
writeMulWithPolyL (Right xs) (Left y) (Left z) = writeMulWithPolyL (Left y) (Right xs) (Left z)
writeMulWithPolyL (Right xs) (Left y) (Right zs) = writeMulWithPolyL (Left y) (Right xs) (Right zs)
writeMulWithPolyL (Right xs) (Right ys) (Left z) = modify (\cs -> addOccurrence xs $ addOccurrence ys $ cs {cmMulL = (xs, ys, Constant z) Seq.<| cmMulL cs})
writeMulWithPolyL (Right xs) (Right ys) (Right zs) = modify (\cs -> addOccurrence xs $ addOccurrence ys $ addOccurrence zs $ cs {cmMulL = (xs, ys, Polynomial zs) Seq.<| cmMulL cs})

-- writeMul :: (GaloisField n, Integral n) => (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> M n ()
-- writeMul as bs cs = writeMulWithLC (fromRefs as) (fromRefs bs) (fromRefs cs)
--   where
--     fromRefs (constant, refs) = LC.new constant refs []

-- writeMulWithLC :: (GaloisField n, Integral n) => LC n -> LC n -> LC n -> M n ()
-- writeMulWithLC (Constant x) (Constant y) (Constant z) =
--   if x * y == z
--     then return ()
--     else error "[ panic ] writeMulWithLC: constant mismatch"
-- writeMulWithLC (Constant x) (Constant y) (Polynomial zs) =
--   -- zs - x * y = 0
--   writeAddWithPolyL $ Right $ PolyL.addConstant (-x * y) zs
-- writeMulWithLC (Constant x) (Polynomial ys) (Constant z) =
--   -- x * ys = z
--   -- x * ys - z = 0
--   case PolyL.multiplyBy x ys of
--     Left _ -> return ()
--     Right poly -> writeAddWithPolyL $ Right $ PolyL.addConstant (-z) poly
-- writeMulWithLC (Constant x) (Polynomial ys) (Polynomial zs) = do
--   -- x * ys = zs
--   -- x * ys - zs = 0
--   case PolyL.multiplyBy x ys of
--     Left c ->
--       -- c - zs = 0
--       writeAddWithPolyL $ Right $ PolyL.addConstant (-c) zs
--     Right ys' -> writeAddWithPolyL $ PolyL.merge ys' (PolyL.negate zs)
-- writeMulWithLC (Polynomial xs) (Constant y) (Constant z) = writeMulWithLC (Constant y) (Polynomial xs) (Constant z)
-- writeMulWithLC (Polynomial xs) (Constant y) (Polynomial zs) = writeMulWithLC (Constant y) (Polynomial xs) (Polynomial zs)
-- writeMulWithLC (Polynomial xs) (Polynomial ys) (Constant z) = modify (\cs -> addOccurrence xs $ addOccurrence ys $ cs {cmMulL = (xs, ys, Constant z) Seq.<| cmMulL cs})
-- writeMulWithLC (Polynomial xs) (Polynomial ys) (Polynomial zs) = modify (\cs -> addOccurrence xs $ addOccurrence ys $ addOccurrence zs $ cs {cmMulL = (xs, ys, Polynomial zs) Seq.<| cmMulL cs})

--------------------------------------------------------------------------------

-- | Assign a field element to a Ref
writeRefVal :: (GaloisField n, Integral n) => Ref -> n -> M n ()
writeRefVal (F a) x = writeRefFVal a x
writeRefVal (B a) x = writeRefBVal a (x /= 0)

-- | Assign a field element to a RefF
writeRefFVal :: (GaloisField n, Integral n) => RefF -> n -> M n ()
writeRefFVal x c = execRelations $ Relations.assignR (F x) c

-- | Assign a Bool to a RefB
writeRefBVal :: (GaloisField n, Integral n) => RefB -> Bool -> M n ()
writeRefBVal x True = execRelations $ Relations.assignR (B x) 1
writeRefBVal x False = execRelations $ Relations.assignR (B x) 0

-- | Assert that two RefBs are equal
writeRefBEq :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeRefBEq x y = do
  addOccurrenceOnRefUBit (B x)
  addOccurrenceOnRefUBit (B y)
  execRelations $ Relations.relateR (B x) 1 (B y) 0

-- | Assert that two Refs are equal
writeRefEq :: (GaloisField n, Integral n) => Ref -> Ref -> M n ()
writeRefEq x y = do
  addOccurrenceOnRefUBit x
  addOccurrenceOnRefUBit y
  execRelations $ Relations.relateR x 1 y 0

-- | Assert that two RefFs are equal
writeRefFEq :: (GaloisField n, Integral n) => RefF -> RefF -> M n ()
writeRefFEq x y = do
  addOccurrenceOnRefUBit (F x)
  addOccurrenceOnRefUBit (F y)
  execRelations $ Relations.relateR (F x) 1 (F y) 0

-- | Assert that one RefB is the negation of another RefB
writeRefBNEq :: (GaloisField n, Integral n) => RefB -> RefB -> M n ()
writeRefBNEq x y = do
  addOccurrenceOnRefUBit (B x)
  addOccurrenceOnRefUBit (B y)
  execRelations $ Relations.relateB x (False, y)

-- | Assign a Integer to a RefU
writeRefUVal :: (GaloisField n, Integral n) => RefU -> U -> M n ()
writeRefUVal x c = execRelations $ Relations.assignS (Slice.fromRefU x) (toInteger c)

-- | Assign an Integer to a Limb
writeLimbVal :: (GaloisField n, Integral n) => Limb -> Integer -> M n ()
writeLimbVal limb val = mapM_ (\(x, c) -> execRelations (Relations.assignS x (toInteger c))) (Slice.fromLimbWithValue limb val)

-- | Assign an Integer to a Slice
writeSliceVal :: (GaloisField n, Integral n) => Slice -> Integer -> M n ()
writeSliceVal x c = execRelations $ Relations.assignS x (toInteger c)

-- | Assert that two RefUs are equal
writeRefUEq :: (GaloisField n, Integral n) => RefU -> RefU -> M n ()
writeRefUEq x y = execRelations $ Relations.relateS (Slice.fromRefU x) (Slice.fromRefU y)

-- | Assert that two Limbs are equal
-- TODO: eliminate this function
writeLimbEq :: (GaloisField n, Integral n) => Limb -> Limb -> M n ()
writeLimbEq a b =
  let as = Slice.fromLimb a
      bs = Slice.fromLimb b
   in case (as, bs) of
        ([(sliceA, coeffA)], [(sliceB, coeffB)]) ->
          if coeffA == coeffB
            then writeSliceEq sliceA sliceB
            else error $ "[ panic ] writeLimbEq: coefficient mismatch, " <> show coeffA <> " /= " <> show coeffB
        _ -> error $ "[ panic ] writeLimbEq: unexpected number of slices, " <> show (length as) <> " /= " <> show (length bs)

-- | Assert that two Slices are equal
writeSliceEq :: (GaloisField n, Integral n) => Slice -> Slice -> M n ()
writeSliceEq x y =
  if widthOf x == widthOf y
    then
      if widthOf x == 0
        then return () -- no need to add a constraint for slices of width 0
        else execRelations $ Relations.relateS x y
    else error $ "[ panic ] writeSliceEq: width mismatch, " <> show (widthOf x) <> " /= " <> show (widthOf y)

--------------------------------------------------------------------------------

addDivModHint :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> Either RefU U -> Either RefU U -> M n ()
addDivModHint x y q r = modify' $ \cs ->
  addOccurrences (Set.fromList [Hint x, Hint y, Hint q, Hint r]) $
    cs {cmDivMods = (x, y, q, r) Seq.<| cmDivMods cs}

addCLDivModHint :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> Either RefU U -> Either RefU U -> M n ()
addCLDivModHint x y q r = modify' $ \cs ->
  addOccurrences (Set.fromList [Hint x, Hint y, Hint q, Hint r]) $
    cs {cmCLDivMods = (x, y, q, r) Seq.<| cmCLDivMods cs}

-- | Width of all values are doubled in this hint
addModInvHint :: (GaloisField n, Integral n) => Either RefU U -> Either RefU U -> Either RefU U -> U -> M n ()
addModInvHint a output n p = modify' $ \cs ->
  addOccurrences (Set.fromList [Hint a, Hint output, Hint n]) $
    cs {cmModInvs = (right (U.widen (widthOf p)) a, right (U.widen (widthOf p)) output, right (U.widen (widthOf p)) n, U.widen (widthOf p) p) Seq.<| cmModInvs cs}

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

-- | Allocates a carry Slice with the given signs
allocCarrySlice :: (GaloisField n, Integral n) => [Bool] -> M n [(Slice, n)]
allocCarrySlice signs = do
  let aggregated = Slice.aggregateSigns signs
  forM aggregated $ \(sign, width, offset) -> do
    slice <- allocSlice width
    return (slice, if sign then 2 ^ offset else -(2 ^ offset))

-- | Allocates a Slice
allocSlice :: (GaloisField n, Integral n) => Width -> M n Slice
allocSlice w = do
  refU <- freshRefU w
  return $ Slice.fromRefU refU