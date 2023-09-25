module Keelung.Compiler.Compile.Util where

import Control.Arrow (right)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bits qualified
import Data.Either (partitionEithers)
import Data.Field.Galois (GaloisField)
import Data.Sequence (Seq)
import Data.Word (Word32)
import Keelung.Compiler.Compile.Error
import Keelung.Compiler.Compile.LC
import Keelung.Compiler.ConstraintModule
import Keelung.Compiler.Optimize.OccurB qualified as OccurB
import Keelung.Compiler.Optimize.OccurF qualified as OccurF
import Keelung.Compiler.Optimize.OccurU qualified as OccurU
import Keelung.Compiler.Relations.EquivClass qualified as EquivClass
import Keelung.Compiler.Relations.Field (Relations)
import Keelung.Compiler.Relations.Field qualified as Relations
import Keelung.Compiler.Syntax.Internal
import Keelung.Data.Constraint
import Keelung.Data.FieldInfo
import Keelung.Data.Limb (Limb (..))
import Keelung.Data.Limb qualified as Limb
import Keelung.Data.PolyG (PolyG)
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Data.PolyL qualified as PolyL
import Keelung.Data.Reference
import Keelung.Interpreter.Arithmetics qualified as U
import Keelung.Syntax.Counters

--------------------------------------------------------------------------------

-- | Monad for compilation
type M n = ReaderT (BootstrapCompiler n) (StateT (ConstraintModule n) (Except (Error n)))

-- | Run the monad
runM :: GaloisField n => BootstrapCompiler n -> FieldInfo -> Counters -> M n a -> Either (Error n) (ConstraintModule n)
runM compilers fieldInfo counters program =
  runExcept
    ( execStateT
        (runReaderT program compilers)
        (ConstraintModule fieldInfo counters OccurF.new (OccurB.new False) OccurU.new Relations.new mempty mempty mempty mempty mempty)
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

-- | Compile a linear combination of expressions into a polynomial
toPoly :: (GaloisField n, Integral n) => (Expr n -> M n (Either Ref n)) -> (n, [(Expr n, n)]) -> M n (Either n (PolyG n))
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
    addC [CAddL $ PolyL.fromPolyG $ PolyG.addConstant (-x * y) zs]
  (Constant x, Polynomial ys, Constant z) ->
    -- x * ys = z
    -- x * ys - z = 0
    case PolyG.multiplyBy x ys of
      Left _ -> return ()
      Right poly -> addC [CAddL $ PolyL.fromPolyG $ PolyG.addConstant (-z) poly]
  (Constant x, Polynomial ys, Polynomial zs) -> do
    -- x * ys = zs
    -- x * ys - zs = 0
    case PolyG.multiplyBy x ys of
      Left c ->
        -- c - zs = 0
        addC [CAddL $ PolyL.fromPolyG $ PolyG.addConstant (-c) zs]
      Right ys' -> case PolyG.merge ys' (PolyG.negate zs) of
        Left _ -> return ()
        Right poly -> addC [CAddL $ PolyL.fromPolyG poly]
  (Polynomial xs, Constant y, Constant z) -> writeMulWithLC (Constant y) (Polynomial xs) (Constant z)
  (Polynomial xs, Constant y, Polynomial zs) -> writeMulWithLC (Constant y) (Polynomial xs) (Polynomial zs)
  (Polynomial xs, Polynomial ys, _) -> addC [CMulL (PolyL.fromPolyG xs) (PolyL.fromPolyG ys) (toPolyL cs)]

writeAddWithPolyG :: (GaloisField n, Integral n) => Either n (PolyG n) -> M n ()
writeAddWithPolyG xs = case xs of
  Left _ -> return ()
  Right poly -> addC [CAddL (PolyL.fromPolyG poly)]

writeAddWithLC :: (GaloisField n, Integral n) => LC n -> M n ()
writeAddWithLC xs = case xs of
  Constant _ -> return ()
  Polynomial poly -> addC [CAddL (PolyL.fromPolyG poly)]

writeAddWithLCAndLimbs :: (GaloisField n, Integral n) => LC n -> n -> [(Limb, n)] -> M n ()
writeAddWithLCAndLimbs lc constant limbs = case lc of
  Constant _ -> return ()
  Polynomial poly ->
    --  PolyL.fromLimbs constant limbs

    --  case PolyL.insertLimbs constant limbs (PolyL.fromPolyG poly) of
    --       Left _ -> return ()
    --       Right polyL ->
    addC [CAddL (PolyL.insertLimbs constant limbs (PolyL.fromPolyG poly))]

-- writeAddWithPolyGAndLimbs :: (GaloisField n, Integral n) => PolyG n -> n -> Seq (Limb, n) -> M n ()
-- writeAddWithPolyGAndLimbs poly constant limbs = addC [CAdd poly (PolyL.buildWithSeq constant limbs)]

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
    countBitTestAsOccurU (B (RefUBit _ (RefUX width var) _)) =
      modify' (\cs -> cs {cmOccurrenceU = OccurU.increase width var (cmOccurrenceU cs)})
    countBitTestAsOccurU _ = return ()

    addOne :: (GaloisField n, Integral n) => Constraint n -> M n ()
    addOne (CAddL xs) = modify' (\cs -> addOccurrencesTuple (PolyL.varsSet xs) $ cs {cmAddL = xs : cmAddL cs})
    addOne (CVarBindF x c) = do
      execRelations $ Relations.assignF x c
    addOne (CVarBindB x c) = do
      execRelations $ Relations.assignB x c
    addOne (CVarBindL x c) = do
      execRelations $ Relations.assignL x c
    addOne (CVarBindU x c) = do
      execRelations $ Relations.assignU x c
    addOne (CVarEq x y) = do
      countBitTestAsOccurU x
      countBitTestAsOccurU y
      execRelations $ Relations.relateRefs x 1 y 0
    addOne (CVarEqF x y) = do
      execRelations $ Relations.relateRefs (F x) 1 (F y) 0
    addOne (CVarEqB x y) = do
      countBitTestAsOccurU (B x)
      countBitTestAsOccurU (B y)
      execRelations $ Relations.relateB x (True, y)
    addOne (CVarEqL x y) = do
      execRelations $ Relations.relateL x y
    addOne (CVarEqU x y) = do
      execRelations $ Relations.relateU x y
    addOne (CVarNEqB x y) = do
      countBitTestAsOccurU (B x)
      countBitTestAsOccurU (B y)
      execRelations $ Relations.relateB x (False, y)
    addOne (CMulL x y (Left c)) = modify' (\cs -> addOccurrencesTuple (PolyL.varsSet x) $ addOccurrencesTuple (PolyL.varsSet y) $ cs {cmMulL = (x, y, Left c) : cmMulL cs})
    addOne (CMulL x y (Right z)) = modify (\cs -> addOccurrencesTuple (PolyL.varsSet x) $ addOccurrencesTuple (PolyL.varsSet y) $ addOccurrencesTuple (PolyL.varsSet z) $ cs {cmMulL = (x, y, Right z) : cmMulL cs})

--------------------------------------------------------------------------------

writeMul :: (GaloisField n, Integral n) => (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> (n, [(Ref, n)]) -> M n ()
writeMul as bs cs = writeMulWithLC (fromPolyG $ uncurry PolyG.build as) (fromPolyG $ uncurry PolyG.build bs) (fromPolyG $ uncurry PolyG.build cs)

writeMulWithLimbs :: (GaloisField n, Integral n) => (n, [(Limb, n)]) -> (n, [(Limb, n)]) -> (n, [(Limb, n)]) -> M n ()
writeMulWithLimbs as bs cs = case (uncurry PolyL.fromLimbs as, uncurry PolyL.fromLimbs bs) of
  (Right as', Right bs') ->
    addC
      [ CMulL as' bs' (uncurry PolyL.fromLimbs cs)
      ]
  _ -> return ()

writeAdd :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> M n ()
writeAdd c as = writeAddWithPolyG (PolyG.build c as)

writeAddWithLimbs :: (GaloisField n, Integral n) => n -> [(Limb, n)] -> M n ()
writeAddWithLimbs constant limbs = case PolyL.fromLimbs constant limbs of
  Left _ -> return ()
  Right poly -> addC [CAddL poly]

writeVal :: (GaloisField n, Integral n) => Ref -> n -> M n ()
writeVal (F a) x = writeValF a x
writeVal (B a) x = writeValB a (x /= 0)

writeValF :: (GaloisField n, Integral n) => RefF -> n -> M n ()
writeValF a x = addC [CVarBindF (F a) x]

writeValB :: (GaloisField n, Integral n) => RefB -> Bool -> M n ()
writeValB a x = addC [CVarBindB a x]

writeValU :: (GaloisField n, Integral n) => RefU -> Integer -> M n ()
writeValU a x = addC [CVarBindU a x]

writeValL :: (GaloisField n, Integral n) => Limb -> Integer -> M n ()
writeValL a x = addC [CVarBindL a x]

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

writeEqL :: (GaloisField n, Integral n) => Limb -> Limb -> M n ()
writeEqL a b = addC [CVarEqL a b]

--------------------------------------------------------------------------------

-- | Hints
addEqZeroHint :: (GaloisField n, Integral n) => n -> [(Ref, n)] -> RefF -> M n ()
addEqZeroHint c xs m = case PolyG.build c xs of
  Left 0 -> writeValF m 0
  Left constant -> writeValF m (recip constant)
  Right poly -> modify' $ \cs -> cs {cmEqZeros = (poly, m) : cmEqZeros cs}

addEqZeroHintWithPoly :: (GaloisField n, Integral n) => Either n (PolyG n) -> RefF -> M n ()
addEqZeroHintWithPoly (Left 0) m = writeValF m 0
addEqZeroHintWithPoly (Left constant) m = writeValF m (recip constant)
addEqZeroHintWithPoly (Right poly) m = modify' $ \cs -> cs {cmEqZeros = (poly, m) : cmEqZeros cs}

addDivModHint :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Either RefU Integer -> Either RefU Integer -> Either RefU Integer -> M n ()
addDivModHint w x y q r = modify' $ \cs -> cs {cmDivMods = (right (U.new w) x, right (U.new w) y, right (U.new w) q, right (U.new w) r) : cmDivMods cs}

addModInvHint :: (GaloisField n, Integral n) => Width -> Either RefU Integer -> Either RefU Integer -> Either RefU Integer -> Integer -> M n ()
addModInvHint w a output n p = modify' $ \cs -> cs {cmModInvs = (right (U.new w) a, right (U.new w) output, right (U.new w) n, U.new w p) : cmModInvs cs}

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

-- | Calculate the number of bits required to represent an Integer.
widthOfInteger :: Integer -> Int
widthOfInteger 0 = 0
widthOfInteger x =
  let lowerBits = fromInteger x :: Word32
      higherBits = x `Data.Bits.shiftR` 32
   in if higherBits == 0
        then 32 - Data.Bits.countLeadingZeros lowerBits
        else 32 + widthOfInteger higherBits

-- | Calculate the lower bound and upper bound
calculateBounds :: Integer -> Seq Limb -> (Integer, Integer)
calculateBounds constant = foldl step (constant, constant)
  where
    step :: (Integer, Integer) -> Limb -> (Integer, Integer)
    step (lower, upper) limb = case Limb.lmbSigns limb of
      Left True -> (lower, upper + 2 ^ Limb.lmbWidth limb - 1)
      Left False -> (lower - 2 ^ Limb.lmbWidth limb + 1, upper)
      Right xs -> let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower + lower', upper + upper')

    calculateBoundsOfigns :: (Integer, Integer) -> [Bool] -> (Integer, Integer)
    calculateBoundsOfigns (_, _) [] = (0, 0)
    calculateBoundsOfigns (lower, upper) (True : xs) = let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower' * 2, upper' * 2 + 1)
    calculateBoundsOfigns (lower, upper) (False : xs) = let (lower', upper') = calculateBoundsOfigns (lower, upper) xs in (lower' * 2 - 1, upper' * 2)

-- | Calculate the carry signs of a 'LimbColumn'.
calculateCarrySigns :: Int -> Integer -> Seq Limb -> [Bool]
calculateCarrySigns limbWidth constant limbs =
  let (lower, upper) = calculateBounds constant limbs
   in if lower < 0
        then
          if (-lower) <= 2 ^ limbWidth
            then
              let range = upper + 2 ^ limbWidth
                  carryWidth = widthOfInteger range
               in False : replicate (carryWidth - limbWidth - 1) True
            else
              let range = upper - lower + 2 ^ limbWidth - 1
                  carryWidth = widthOfInteger range
               in map (not . Data.Bits.testBit (-lower + 2 ^ limbWidth)) [limbWidth .. carryWidth - 1]
        else
          let carryWidth = widthOfInteger upper
           in replicate (carryWidth - limbWidth) True
