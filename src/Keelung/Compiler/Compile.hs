{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Arrow (left)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Bits qualified
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (foldl'), toList)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Keelung.Compiler.Compile.Error qualified as Compile
import Keelung.Compiler.Compile.Relations.FieldRelations qualified as FieldRelations
import Keelung.Compiler.Constraint
import Keelung.Compiler.ConstraintSystem
import Keelung.Compiler.Error
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import Keelung.Data.PolyG qualified as PolyG
import Keelung.Syntax.Counters (Counters, VarSort (..), VarType (..), addCount, getCount)
import qualified Data.Set as Set

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => Bool -> TypeErased n -> Either (Error n) (ConstraintSystem n)
run useNewOptimizer (TypeErased untypedExprs _ counters assertions sideEffects) = left CompileError $ runM useNewOptimizer counters $ do
  forM_ untypedExprs $ \(var, expr) -> do
    case expr of
      ExprB x -> do
        let out = RefBO var
        compileExprB out x
      ExprF x -> do
        let out = RefFO var
        compileExprF out x
      ExprU x -> do
        let out = RefUO (widthOfU x) var
        compileExprU out x

  -- compile assertions to constraints
  mapM_ compileAssertion assertions

  -- compile all side effects
  mapM_ compileSideEffect sideEffects

-- | Compile side effects
compileSideEffect :: (GaloisField n, Integral n) => SideEffect n -> M n ()
compileSideEffect (AssignmentB2 var val) = compileExprB (RefB var) val
compileSideEffect (AssignmentF2 var val) = compileExprF (RefF var) val
compileSideEffect (AssignmentU2 width var val) = compileExprU (RefU width var) val
compileSideEffect (DivMod width dividend divisor quotient remainder) = compileDivModU width dividend divisor quotient remainder
compileSideEffect (AssertLTE width value bound) = assertLTE width value bound

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = case expr of
  ExprB (EqB x y) -> compileAssertionEqB x y
  ExprB (EqF x y) -> compileAssertionEqF x y
  ExprB (EqU x y) -> compileAssertionEqU x y
  ExprB x -> do
    out <- freshRefB
    compileExprB out x
    add $ cVarBindB out 1 -- out = 1
  ExprF x -> do
    out <- freshRefF
    compileExprF out x
    add $ cVarBindF (F out) 1
  ExprU x -> do
    out <- freshRefU (widthOfU x)
    compileExprU out x
    add $ cVarBindU out 1

compileAssertionEqB :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> M n ()
compileAssertionEqB (VarB a) (ValB b) = add $ cVarBindB (RefB a) b
compileAssertionEqB (VarB a) (VarB b) = add $ cVarEqB (RefB a) (RefB b)
compileAssertionEqB (VarB a) (VarBO b) = add $ cVarEqB (RefB a) (RefBO b)
compileAssertionEqB (VarB a) (VarBI b) = add $ cVarEqB (RefB a) (RefBI b)
compileAssertionEqB (VarB a) b = do
  out <- freshRefB
  compileExprB out b
  add $ cVarEqB (RefB a) out
compileAssertionEqB (VarBO a) (ValB b) = add $ cVarBindB (RefBO a) b
compileAssertionEqB (VarBO a) (VarB b) = add $ cVarEqB (RefBO a) (RefB b)
compileAssertionEqB (VarBO a) (VarBO b) = add $ cVarEqB (RefBO a) (RefBO b)
compileAssertionEqB (VarBO a) (VarBI b) = add $ cVarEqB (RefBO a) (RefBI b)
compileAssertionEqB (VarBO a) b = do
  out <- freshRefB
  compileExprB out b
  add $ cVarEqB (RefBO a) out
compileAssertionEqB (VarBI a) (ValB b) = add $ cVarBindB (RefBI a) b
compileAssertionEqB (VarBI a) (VarB b) = add $ cVarEqB (RefBI a) (RefB b)
compileAssertionEqB (VarBI a) (VarBO b) = add $ cVarEqB (RefBI a) (RefBO b)
compileAssertionEqB (VarBI a) (VarBI b) = add $ cVarEqB (RefBI a) (RefBI b)
compileAssertionEqB (VarBI a) b = do
  out <- freshRefB
  compileExprB out b
  add $ cVarEqB (RefBI a) out
compileAssertionEqB a b = do
  a' <- freshRefB
  b' <- freshRefB
  compileExprB a' a
  compileExprB b' b
  add $ cVarEqB a' b'

compileAssertionEqF :: (GaloisField n, Integral n) => ExprF n -> ExprF n -> M n ()
compileAssertionEqF (VarF a) (ValF b) = add $ cVarBindF (F $ RefF a) b
compileAssertionEqF (VarF a) (VarF b) = add $ cVarEqF (RefF a) (RefF b)
compileAssertionEqF (VarF a) (VarFO b) = add $ cVarEqF (RefF a) (RefFO b)
compileAssertionEqF (VarF a) (VarFI b) = add $ cVarEqF (RefF a) (RefFI b)
compileAssertionEqF (VarF a) b = do
  out <- freshRefF
  compileExprF out b
  add $ cVarEqF (RefF a) out
compileAssertionEqF (VarFO a) (ValF b) = add $ cVarBindF (F $ RefFO a) b
compileAssertionEqF (VarFO a) (VarF b) = add $ cVarEqF (RefFO a) (RefF b)
compileAssertionEqF (VarFO a) (VarFO b) = add $ cVarEqF (RefFO a) (RefFO b)
compileAssertionEqF (VarFO a) b = do
  out <- freshRefF
  compileExprF out b
  add $ cVarEqF (RefFO a) out
compileAssertionEqF (VarFI a) (ValF b) = add $ cVarBindF (F $ RefFI a) b
compileAssertionEqF (VarFI a) (VarF b) = add $ cVarEqF (RefFI a) (RefF b)
compileAssertionEqF (VarFI a) (VarFO b) = add $ cVarEqF (RefFI a) (RefF b)
compileAssertionEqF (VarFI a) b = do
  out <- freshRefF
  compileExprF out b
  add $ cVarEqF (RefFI a) out
compileAssertionEqF a b = do
  a' <- freshRefF
  b' <- freshRefF
  compileExprF a' a
  compileExprF b' b
  add $ cVarEqF a' b'

compileAssertionEqU :: (GaloisField n, Integral n) => ExprU n -> ExprU n -> M n ()
compileAssertionEqU (VarU w a) (ValU _ b) = add $ cVarBindU (RefU w a) b
compileAssertionEqU (VarU w a) (VarU _ b) = add $ cVarEqU (RefU w a) (RefU w b)
compileAssertionEqU (VarU w a) (VarUO _ b) = add $ cVarEqU (RefU w a) (RefUO w b)
compileAssertionEqU (VarU w a) (VarUI _ b) = add $ cVarEqU (RefU w a) (RefUI w b)
compileAssertionEqU (VarU w a) b = do
  out <- freshRefU w
  compileExprU out b
  add $ cVarEqU (RefU w a) out
compileAssertionEqU (VarUO w a) (ValU _ b) = add $ cVarBindU (RefUO w a) b
compileAssertionEqU (VarUO w a) (VarU _ b) = add $ cVarEqU (RefUO w a) (RefU w b)
compileAssertionEqU (VarUO w a) (VarUO _ b) = add $ cVarEqU (RefUO w a) (RefUO w b)
compileAssertionEqU (VarUO w a) b = do
  out <- freshRefU w
  compileExprU out b
  add $ cVarEqU (RefUO w a) out
compileAssertionEqU (VarUI w a) (ValU _ b) = add $ cVarBindU (RefUI w a) b
compileAssertionEqU (VarUI w a) (VarU _ b) = add $ cVarEqU (RefUI w a) (RefU w b)
compileAssertionEqU (VarUI w a) (VarUO _ b) = add $ cVarEqU (RefUI w a) (RefUO w b)
compileAssertionEqU (VarUI w a) b = do
  out <- freshRefU w
  compileExprU out b
  add $ cVarEqU (RefUI w a) out
compileAssertionEqU a b = do
  let width = widthOfU a
  a' <- freshRefU width
  b' <- freshRefU width
  compileExprU a' a
  compileExprU b' b
  add $ cVarEqU a' b'

-- compileRelations :: (GaloisField n, Integral n) => Relations n -> M n ()
-- compileRelations (Relations vb eb) = do
--   -- intermediate variable bindings of values
--   forM_ (IntMap.toList (structF vb)) $ \(var, val) -> add $ cVarBindF (RefF var) val
--   forM_ (IntMap.toList (structB vb)) $ \(var, val) -> add $ cVarBindB (RefB var) val
--   forM_ (IntMap.toList (structU vb)) $ \(width, bindings) ->
--     forM_ (IntMap.toList bindings) $ \(var, val) -> add $ cVarBindU (RefU width var) val
--   -- intermediate variable bindings of expressions
--   forM_ (IntMap.toList (structF eb)) $ \(var, val) -> compileExprF (RefF var) val
--   forM_ (IntMap.toList (structB eb)) $ \(var, val) -> compileExprB (RefB var) val
--   forM_ (IntMap.toList (structU eb)) $ \(width, bindings) ->
--     forM_ (IntMap.toList bindings) $ \(var, val) -> compileExprU (RefU width var) val

--------------------------------------------------------------------------------

-- | Monad for compilation
type M n = StateT (ConstraintSystem n) (Except (Compile.Error n))

runM :: GaloisField n => Bool -> Counters -> M n a -> Either (Compile.Error n) (ConstraintSystem n)
runM useNewOptimizer counters program =
  runExcept
    ( execStateT
        program
        (ConstraintSystem counters useNewOptimizer mempty mempty mempty FieldRelations.new mempty mempty mempty mempty mempty mempty)
    )

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\cs -> cs {csCounters = f (csCounters cs)})

add :: (GaloisField n, Integral n) => [Constraint n] -> M n ()
add = mapM_ addOne
  where
    addOne :: (GaloisField n, Integral n) => Constraint n -> M n ()
    addOne (CAddF xs) = modify' (\cs -> addOccurrences (PolyG.vars xs) $ cs {csAddF = xs : csAddF cs})
    addOne (CVarBindF x c) = do
      cs <- get
      csFieldRelations' <- lift $ FieldRelations.bindField x c (csFieldRelations cs)
      put cs {csFieldRelations = csFieldRelations'}
    addOne (CVarBindB x c) = do
      cs <- get
      csFieldRelations' <- lift $ FieldRelations.bindBoolean x (c == 1) (csFieldRelations cs)
      put cs {csFieldRelations = csFieldRelations'}
    addOne (CVarBindU x c) = do
      cs <- get
      csFieldRelations' <- lift $ FieldRelations.bindUInt x c (csFieldRelations cs)
      put cs {csFieldRelations = csFieldRelations'}
    -- put cs {csUIntRelations = csUIntRelations'}
    addOne (CVarEq x y) = do
      cs <- get
      result <- lift $ FieldRelations.relateRefF x (1, y, 0) (csFieldRelations cs)
      case result of
        Nothing -> return ()
        Just csFieldRelations' -> put cs {csFieldRelations = csFieldRelations'}
    addOne (CVarEqF x y) = do
      cs <- get
      result <- lift $ FieldRelations.relateRefF (F x) (1, F y, 0) (csFieldRelations cs)
      case result of
        Nothing -> return ()
        Just csFieldRelations' -> put cs {csFieldRelations = csFieldRelations'}
    addOne (CVarEqB x y) = do
      cs <- get
      csFieldRelations' <- lift $ FieldRelations.relateBoolean x (True, y) (csFieldRelations cs)
      put $ cs {csFieldRelations = csFieldRelations'}
    addOne (CVarNEqB x y) = do
      cs <- get
      csFieldRelations' <- lift $ FieldRelations.relateBoolean x (False, y) (csFieldRelations cs)
      put $ cs {csFieldRelations = csFieldRelations'}
    addOne (CVarEqU x y) = do
      cs <- get
      csFieldRelations' <- lift $ FieldRelations.assertEqualUInt x y (csFieldRelations cs)
      put $ cs {csFieldRelations = csFieldRelations'}
    -- case result of
    --   Nothing -> return ()
    --   Just csUIntRelations' -> put cs {csUIntRelations = csUIntRelations'}
    addOne (CMulF x y (Left c)) = modify' (\cs -> addOccurrences (PolyG.vars x) $ addOccurrences (PolyG.vars y) $ cs {csMulF = (x, y, Left c) : csMulF cs})
    addOne (CMulF x y (Right z)) = do
      modify (\cs -> addOccurrences (PolyG.vars x) $ addOccurrences (PolyG.vars y) $ addOccurrences (PolyG.vars z) $ cs {csMulF = (x, y, Right z) : csMulF cs})
    addOne (CNEqF x y m) = modify' (\cs -> addOccurrences (Set.fromList [x, y, m]) $ cs {csNEqF = Map.insert (x, y) m (csNEqF cs)})
    addOne (CNEqU x y m) = modify' (\cs -> addOccurrences (Set.fromList [x, y])  $ addOccurrences (Set.singleton m)  $ cs {csNEqU = Map.insert (x, y) m (csNEqU cs)})

-- addOne (CRotateU x y _n) = do
--   cs <- get
--   case UIntRelations.relate x (True, y) (csUIntRelations cs) of
--     Nothing -> return ()
--     Just csUIntRelations' -> put cs {csUIntRelations = csUIntRelations'}

-- TODO: remove this
addOccurrencesUTemp :: [RefU] -> M n ()
addOccurrencesUTemp = modify' . addOccurrences . Set.fromList

addDivModHint :: (GaloisField n, Integral n) => RefU -> RefU -> RefU -> RefU -> M n ()
addDivModHint x y q r = modify' $ \cs -> cs {csDivMods = (x, y, q, r) : csDivMods cs}

addModInvHint :: (GaloisField n, Integral n) => RefU -> RefU -> Integer -> M n ()
addModInvHint x n p = modify' $ \cs -> cs {csModInvs = (x, n, p) : csModInvs cs}

freshRefF :: M n RefT
freshRefF = do
  counters <- gets csCounters
  let index = getCount OfIntermediate OfField counters
  modifyCounter $ addCount OfIntermediate OfField 1
  return $ RefF index

freshRefB :: M n RefB
freshRefB = do
  counters <- gets csCounters
  let index = getCount OfIntermediate OfBoolean counters
  modifyCounter $ addCount OfIntermediate OfBoolean 1
  return $ RefB index

-- freshVarB :: M n (ExprB n)
-- freshVarB = do
--   counters <- gets csCounters
--   let index = getCount OfIntermediate OfBoolean counters
--   modifyCounter $ addCount OfIntermediate OfBoolean 1
--   return $ VarB index

freshRefU :: Width -> M n RefU
freshRefU width = do
  counters <- gets csCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ RefU width index

freshExprU :: Width -> M n (ExprU n)
freshExprU width = do
  counters <- gets csCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ VarU width index

----------------------------------------------------------------

compileExprB :: (GaloisField n, Integral n) => RefB -> ExprB n -> M n ()
compileExprB out expr = case expr of
  ValB val -> add $ cVarBindB out val -- out = val
  VarB var -> add $ cVarEqB out (RefB var) -- out = var
  VarBO var -> add $ cVarEqB out (RefBO var) -- out = var
  VarBI var -> add $ cVarEqB out (RefBI var) -- out = var
  VarBP var -> add $ cVarEqB out (RefBP var) -- out = var
  AndB x0 x1 xs -> do
    a <- wireB x0
    b <- wireB x1
    vars <- mapM wireB xs
    case vars of
      Empty ->
        add $ cMulSimpleF (RefBtoRefF a) (RefBtoRefF b) (RefBtoRefF out) -- out = a * b
      (c :<| Empty) -> do
        aAndb <- freshRefB
        add $ cMulSimpleF (RefBtoRefF a) (RefBtoRefF b) (RefBtoRefF aAndb) -- aAndb = a * b
        add $ cMulSimpleF (RefBtoRefF aAndb) (RefBtoRefF c) (RefBtoRefF out) -- out = aAndb * c
      _ -> do
        -- the number of operands
        let n = 2 + fromIntegral (length vars)
        -- polynomial = n - sum of operands
        let polynomial = (n, (RefBtoRefF a, -1) : (RefBtoRefF b, -1) : [(RefBtoRefF v, -1) | v <- toList vars])
        -- if the answer is 1 then all operands must be 1
        --    (n - sum of operands) * out = 0
        add $
          cMulF
            polynomial
            (0, [(RefBtoRefF out, 1)])
            (0, [])
        -- if the answer is 0 then not all operands must be 1:
        --    (n - sum of operands) * inv = 1 - out
        inv <- freshRefB
        add $
          cMulF
            polynomial
            (0, [(RefBtoRefF inv, 1)])
            (1, [(RefBtoRefF out, -1)])
  OrB x0 x1 xs -> do
    compileOrBs out x0 x1 xs
  XorB x y -> do
    x' <- wireB x
    y' <- wireB y
    compileXorB out x' y'
  NotB x -> do
    x' <- wireB x
    add $ cVarNEqB x' out
  IfB p x y -> do
    p' <- wireB p
    x' <- wireB x
    y' <- wireB y
    compileIfB out p' x' y'
  NEqB x y -> compileExprB out (XorB x y)
  NEqF x y -> do
    x' <- wireF x
    y' <- wireF y
    compileEqualityF False out x' y'
  NEqU x y -> do
    x' <- wireU x
    y' <- wireU y
    compileEqualityU False out x' y'
  EqB x y -> do
    x' <- wireB x
    y' <- wireB y
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    --     x * y + (1 - x) * (1 - y) = out
    -- =>
    --    (1 - x) * (1 - 2y) = (out - y)
    add $
      cMulF
        (1, [(RefBtoRefF x', -1)])
        (1, [(RefBtoRefF y', -2)])
        (0, [(RefBtoRefF out, 1), (RefBtoRefF y', -1)])
  EqF x y -> do
    x' <- wireF x
    y' <- wireF y
    compileEqualityF True out x' y'
  EqU x y -> do
    x' <- wireU x
    y' <- wireU y
    compileEqualityU True out x' y'
  -- LTEU w x y -> do
  --   x' <- wireU x
  --   y' <- wireU y
  --   assertLTEU w out x' y'
  BitU x i -> do
    x' <- wireU x
    let width = widthOfU x
    add $ cVarEqB out (RefUBit width x' (i `mod` width)) -- out = x'[i]

compileExprF :: (GaloisField n, Integral n) => RefT -> ExprF n -> M n ()
compileExprF out expr = case expr of
  ValF val -> add $ cVarBindF (F out) val -- out = val
  VarF var -> add $ cVarEqF out (RefF var) -- out = var
  VarFO var -> add $ cVarEqF out (RefFO var) -- out = var
  VarFI var -> add $ cVarEqF out (RefFI var) -- out = var
  VarFP var -> add $ cVarEqF out (RefFP var) -- out = var
  SubF x y -> do
    x' <- toTerm x
    y' <- toTerm y
    compileTerms out (x' :<| negateTerm y' :<| Empty)
  AddF x y rest -> do
    terms <- mapM toTerm (x :<| y :<| rest)
    compileTerms out terms
  MulF x y -> do
    x' <- wireF x
    y' <- wireF y
    add $ cMulSimpleF (F x') (F y') (F out)
  DivF x y -> do
    x' <- wireF x
    y' <- wireF y
    add $ cMulSimpleF (F y') (F out) (F x')
  -- MMIF x p -> do
  --   -- See: https://github.com/btq-ag/keelung-compiler/issues/14
  --   -- 1. x * x⁻¹ = np + 1
  --   -- 2. n ≤ ⌈log₂p⌉

  --   -- constraint: n ≤ ⌈log₂p⌉
  --   let upperBoundOfN = ceiling (logBase 2 (fromIntegral p) :: Double) :: Integer
  --   let bitWidthOfUIntThatCanStoreUpperBoundOfN = ceiling (logBase 2 (fromIntegral upperBoundOfN) :: Double) :: Int
  --   n <- freshRefU bitWidthOfUIntThatCanStoreUpperBoundOfN
  --   let diff = 2 ^ bitWidthOfUIntThatCanStoreUpperBoundOfN - upperBoundOfN

  --   -- constraint: x * x⁻¹ = np + 1
  --   x' <- wireF x
  --   inv <- freshRefF
  --   add $ cMulF (0, [(x', 1)]) (0, [(inv, -1)]) (1, [(RefUVal n, fromIntegral p)])
  IfF p x y -> do
    p' <- wireB p
    x' <- wireF x
    y' <- wireF y
    compileIfF (F out) p' (F x') (F y')
  BtoF x -> do
    result <- freshRefB
    compileExprB result x
    add $ cVarEq (F out) (RefBtoRefF result) -- out = var

compileExprU :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compileExprU out expr = case expr of
  ValU width val -> do
    -- constraint for UInt : out = val
    add $ cVarBindU out val
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      let bit = testBit val i
      add $ cVarBindB (RefUBit width out i) bit -- out[i] = bit
  VarU width var -> do
    add $ cVarEqU out (RefU width var)
  VarUO width var -> do
    add $ cVarEqU out (RefU width var) -- out = var
  VarUI width var -> do
    let ref = RefUI width var
    -- constraint for UInt : out = ref
    add $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      add $ cVarEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
  VarUP width var -> do
    let ref = RefUP width var
    -- constraint for UInt : out = ref
    add $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      add $ cVarEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
  SubU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileSubU w out x' y'
  AddU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileAddU w out x' y'
  MulU w x y -> do
    x' <- wireU x
    y' <- wireU y
    compileMulU w out x' y'
  MMIU w a p -> do
    -- See: https://github.com/btq-ag/keelung-compiler/issues/14
    -- 1. a * a⁻¹ = np + 1
    -- 2. n ≤ ⌈log₂p⌉
    a' <- wireU a
    n <- freshExprU w
    nRef <- wireU n
    let ceilingLg2P = ceiling (logBase 2 (fromInteger p) :: Double)
    add $ cMulF (0, [(RefUVal a', 1)]) (0, [(RefUVal out, 1)]) (1, [(RefUVal nRef, fromInteger p)])
    addModInvHint a' nRef p
    assertLTE w n ceilingLg2P
  AndU w x y xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      compileExprB
        (RefUBit w out i)
        (AndB (BitU x i) (BitU y i) (fmap (`BitU` i) xs))
  OrU w x y xs -> do
    forM_ [0 .. w - 1] $ \i -> do
      compileExprB
        (RefUBit w out i)
        (OrB (BitU x i) (BitU y i) (fmap (`BitU` i) xs))
  XorU w x y -> do
    forM_ [0 .. w - 1] $ \i -> do
      compileExprB
        (RefUBit w out i)
        (XorB (BitU x i) (BitU y i))
  NotU w x -> do
    forM_ [0 .. w - 1] $ \i -> do
      compileExprB
        (RefUBit w out i)
        (NotB (BitU x i))
  IfU _ p x y -> do
    p' <- wireB p
    x' <- wireU x
    y' <- wireU y
    compileIfU out p' x' y'
  RoLU w n x -> do
    x' <- wireU x
    -- add $ cRotateU out x' n
    forM_ [0 .. w - 1] $ \i -> do
      let i' = (i - n) `mod` w
      add $ cVarEqB (RefUBit w out i) (RefUBit w x' i') -- out[i] = x'[i']
  ShLU w n x -> do
    x' <- wireU x
    case compare n 0 of
      EQ -> add $ cVarEqU out x'
      GT -> do
        -- fill lower bits with 0s
        forM_ [0 .. n - 1] $ \i -> do
          add $ cVarBindB (RefUBit w out i) 0 -- out[i] = 0
          -- shift upper bits
        forM_ [n .. w - 1] $ \i -> do
          let i' = i - n
          add $ cVarEqB (RefUBit w out i) (RefUBit w x' i') -- out[i] = x'[i']
      LT -> do
        -- shift lower bits
        forM_ [0 .. w + n - 1] $ \i -> do
          let i' = i - n
          add $ cVarEqB (RefUBit w out i) (RefUBit w x' i') -- out[i] = x'[i']
          -- fill upper bits with 0s
        forM_ [w + n .. w - 1] $ \i -> do
          add $ cVarBindB (RefUBit w out i) 0 -- out[i] = 0
  SetU w x j b -> do
    x' <- wireU x
    b' <- wireB b
    forM_ [0 .. w - 1] $ \i -> do
      if i == j
        then add $ cVarEqB (RefUBit w out i) b' -- out[i] = b
        else add $ cVarEqB (RefUBit w out i) (RefUBit w x' i) -- out[i] = x[i]
  BtoU w x -> do
    -- 1. wire 'out[ZERO]' to 'x'
    result <- freshRefB
    compileExprB result x
    add $ cVarEqB (RefUBit w out 0) result -- out[0] = x
    -- 2. wire 'out[SUCC _]' to '0' for all other bits
    forM_ [1 .. w - 1] $ \i ->
      add $ cVarBindB (RefUBit w out i) 0 -- out[i] = 0

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars RefT n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: (GaloisField n, Integral n) => ExprF n -> M n (Term n)
toTerm (MulF (ValF m) (ValF n)) = return $ Constant (m * n)
toTerm (MulF (VarF var) (ValF n)) = return $ WithVars (RefF var) n
toTerm (MulF (VarFI var) (ValF n)) = return $ WithVars (RefFI var) n
toTerm (MulF (VarFO var) (ValF n)) = return $ WithVars (RefFO var) n
toTerm (MulF (ValF n) (VarF var)) = return $ WithVars (RefF var) n
toTerm (MulF (ValF n) (VarFI var)) = return $ WithVars (RefFI var) n
toTerm (MulF (ValF n) (VarFO var)) = return $ WithVars (RefFO var) n
toTerm (MulF (ValF n) expr) = do
  out <- freshRefF
  compileExprF out expr
  return $ WithVars out n
toTerm (MulF expr (ValF n)) = do
  out <- freshRefF
  compileExprF out expr
  return $ WithVars out n
toTerm (ValF n) =
  return $ Constant n
toTerm (VarF var) =
  return $ WithVars (RefF var) 1
toTerm (VarFI var) =
  return $ WithVars (RefFI var) 1
toTerm (VarFO var) =
  return $ WithVars (RefFO var) 1
toTerm expr = do
  out <- freshRefF
  compileExprF out expr
  return $ WithVars out 1

-- | Negate a Term
negateTerm :: Num n => Term n -> Term n
negateTerm (WithVars var c) = WithVars var (negate c)
negateTerm (Constant c) = Constant (negate c)

compileTerms :: (GaloisField n, Integral n) => RefT -> Seq (Term n) -> M n ()
compileTerms out terms =
  let (constant, varsWithCoeffs) = foldl' go (0, []) terms
   in case varsWithCoeffs of
        [] -> add $ cVarBindF (F out) constant
        _ -> add $ cAddF constant $ (F out, -1) : varsWithCoeffs
  where
    go :: Num n => (n, [(RefF, n)]) -> Term n -> (n, [(RefF, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (F var, coeff) : pairs)

-- | If the expression is not already a variable, create a new variable
wireB :: (GaloisField n, Integral n) => ExprB n -> M n RefB
wireB (VarB ref) = return (RefB ref)
wireB (VarBO ref) = return (RefBO ref)
wireB (VarBI ref) = return (RefBI ref)
wireB (VarBP ref) = return (RefBP ref)
wireB expr = do
  out <- freshRefB
  compileExprB out expr
  return out

wireF :: (GaloisField n, Integral n) => ExprF n -> M n RefT
wireF (VarF ref) = return (RefF ref)
wireF (VarFO ref) = return (RefFO ref)
wireF (VarFI ref) = return (RefFI ref)
wireF (VarFP ref) = return (RefFP ref)
wireF expr = do
  out <- freshRefF
  compileExprF out expr
  return out

wireU :: (GaloisField n, Integral n) => ExprU n -> M n RefU
wireU (VarU w ref) = return (RefU w ref)
wireU (VarUO w ref) = return (RefUO w ref)
wireU (VarUI w ref) = return (RefUI w ref)
wireU (VarUP w ref) = return (RefUP w ref)
wireU expr = do
  out <- freshRefU (widthOfU expr)
  compileExprU out expr
  return out

--------------------------------------------------------------------------------

-- | Equalities are compiled with inequalities and inequalities with CNEQ constraints.
--    Constraint 'x != y = out'
--    The encoding is, for some 'm':
--        1. (x - y) * m = out
--        2. (x - y) * (1 - out) = 0
compileEqualityU :: (GaloisField n, Integral n) => Bool -> RefB -> RefU -> RefU -> M n ()
compileEqualityU isEq out x y =
  if x == y
    then do
      -- in this case, the variable x and y happend to be the same
      if isEq
        then compileExprB out (ValB 1)
        else compileExprB out (ValB 0)
    else do
      -- introduce a new variable m
      m <- freshRefF
      if isEq
        then do
          --  1. (x - y) * m = 1 - out
          --  2. (x - y) * out = 0
          add $
            cMulF
              (0, [(RefUVal x, 1), (RefUVal y, -1)])
              (0, [(F m, 1)])
              (1, [(RefBtoRefF out, -1)])
          add $
            cMulF
              (0, [(RefUVal x, 1), (RefUVal y, -1)])
              (0, [(RefBtoRefF out, 1)])
              (0, [])
        else do
          --  1. (x - y) * m = out
          --  2. (x - y) * (1 - out) = 0
          add $
            cMulF
              (0, [(RefUVal x, 1), (RefUVal y, -1)])
              (0, [(F m, 1)])
              (0, [(RefBtoRefF out, 1)])
          add $
            cMulF
              (0, [(RefUVal x, 1), (RefUVal y, -1)])
              (1, [(RefBtoRefF out, -1)])
              (0, [])

      --  keep track of the relation between (x - y) and m
      add $ cNEqU x y m

compileEqualityF :: (GaloisField n, Integral n) => Bool -> RefB -> RefT -> RefT -> M n ()
compileEqualityF isEq out x y =
  if x == y
    then do
      -- in this case, the variable x and y happend to be the same
      if isEq
        then compileExprB out (ValB 1)
        else compileExprB out (ValB 0)
    else do
      -- introduce a new variable m
      -- if diff = 0 then m = 0 else m = recip diff
      m <- freshRefF

      if isEq
        then do
          --  1. (x - y) * m = 1 - out
          --  2. (x - y) * out = 0
          add $
            cMulF
              (0, [(F x, 1), (F y, -1)])
              (0, [(F m, 1)])
              (1, [(RefBtoRefF out, -1)])
          add $
            cMulF
              (0, [(F x, 1), (F y, -1)])
              (0, [(RefBtoRefF out, 1)])
              (0, [])
        else do
          --  1. (x - y) * m = out
          --  2. (x - y) * (1 - out) = 0
          add $
            cMulF
              (0, [(F x, 1), (F y, -1)])
              (0, [(F m, 1)])
              (0, [(RefBtoRefF out, 1)])
          add $
            cMulF
              (0, [(F x, 1), (F y, -1)])
              (1, [(RefBtoRefF out, -1)])
              (0, [])

      --  keep track of the relation between (x - y) and m
      add $ cNEqF x y m

--------------------------------------------------------------------------------

-- | Encoding addition on UInts with multiple operands: O(1)
--      A       =          2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =          2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2ⁿ⁺¹Cₙ + 2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      Result  =          2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      C       = A + B
compileAddOrSubU :: (GaloisField n, Integral n) => Bool -> Width -> RefU -> RefU -> RefU -> M n ()
compileAddOrSubU isSub width out a b = do
  c <- freshRefU (width + 1)
  -- C = A + B
  add $ cAddF 0 [(RefUVal a, 1), (RefUVal b, if isSub then -1 else 1), (RefUVal c, -1)]
  -- copying bits from C to 'out'
  forM_ [0 .. width - 1] $ \i -> do
    -- Cᵢ = outᵢ
    add $ cVarEqB (RefUBit width c i) (RefUBit width out i)
  -- HACK: add occurences of RefUs
  addOccurrencesUTemp [out, a, b, c]

compileAddU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileAddU = compileAddOrSubU False

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileSubU = compileAddOrSubU True

-- | Encoding addition on UInts with multiple operands: O(2)
--      A       =   2ⁿAₙ₋₁ + ... + 2A₁ + A₀
--      B       =   2ⁿBₙ₋₁ + ... + 2B₁ + B₀
--      C       = 2²ⁿC₂ₙ₋₁ + ... + 2C₁ + C₀
--      Result  =   2ⁿCₙ₋₁ + ... + 2C₁ + C₀
--      C       = A * B
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> RefU -> RefU -> M n ()
compileMulU width out a b = do
  c <- freshRefU (width * 2)
  -- C = A * B
  add $ cMulF (0, [(RefUVal a, 1)]) (0, [(RefUVal b, 1)]) (0, [(RefUVal c, 1)])
  -- copying bits from C to 'out'
  forM_ [0 .. width - 1] $ \i -> do
    -- Cᵢ = outᵢ
    add $ cVarEqB (RefUBit width c i) (RefUBit width out i)
  -- HACK: add occurences of RefUs
  addOccurrencesUTemp [out, a, b, c]

-- | An universal way of compiling a conditional
compileIfB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> RefB -> M n ()
compileIfB out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  out = p * x + y - p * y
  --      =>
  --  (out - y) = p * (x - y)
  add $
    cMulF
      (0, [(RefBtoRefF p, 1)])
      (0, [(RefBtoRefF x, 1), (RefBtoRefF y, -1)])
      (0, [(RefBtoRefF y, -1), (RefBtoRefF out, 1)])

compileIfF :: (GaloisField n, Integral n) => RefF -> RefB -> RefF -> RefF -> M n ()
compileIfF out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  out = p * x + y - p * y
  --      =>
  --  (out - y) = p * x - p * y
  --      =>
  --  (out - y) = p * (x - y)
  add $
    cMulF
      (0, [(RefBtoRefF p, 1)])
      (0, [(x, 1), (y, -1)])
      (0, [(y, -1), (out, 1)])

compileIfU :: (GaloisField n, Integral n) => RefU -> RefB -> RefU -> RefU -> M n ()
compileIfU out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  out = p * x + y - p * y
  --      =>
  --  (out - y) = p * x - p * y
  --      =>
  --  (out - y) = p * (x - y)
  add $
    cMulF
      (0, [(RefBtoRefF p, 1)])
      (0, [(RefUVal x, 1), (RefUVal y, -1)])
      (0, [(RefUVal y, -1), (RefUVal out, 1)])

compileOrB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
compileOrB out x y = do
  -- (1 - x) * y = (out - x)
  add $
    cMulF
      (1, [(RefBtoRefF x, -1)])
      (0, [(RefBtoRefF y, 1)])
      (0, [(RefBtoRefF x, -1), (RefBtoRefF out, 1)])

compileOrBs :: (GaloisField n, Integral n) => RefB -> ExprB n -> ExprB n -> Seq (ExprB n) -> M n ()
compileOrBs out x0 x1 xs = do
  a <- wireB x0
  b <- wireB x1
  vars <- mapM wireB xs
  case vars of
    Empty -> compileOrB out a b
    (c :<| Empty) -> do
      -- only 3 operands
      aOrb <- freshRefB
      compileOrB aOrb a b
      compileOrB out aOrb c
    _ -> do
      -- more than 3 operands, rewrite it as an inequality instead:
      --      if all operands are 0           then 0 else 1
      --  =>  if the sum of operands is 0     then 0 else 1
      --  =>  if the sum of operands is not 0 then 1 else 0
      --  =>  the sum of operands is not 0
      compileExprB
        out
        ( NEqF
            (ValF 0)
            ( AddF
                (BtoF x0)
                (BtoF x1)
                (fmap BtoF xs)
            )
        )

-- assertOrBs :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> ExprB n -> Seq (ExprB n) -> M n ()
-- assertOrBs out x0 x1 xs = case xs of
--   Empty -> assertOrB out x0 x1
--   (x2 :<| Empty) -> do
--     -- only 3 operands
--     aOrb <- freshVarB
--     assertOrB aOrb x0 x1
--     assertOrB out aOrb x2
--   _ -> do
--     -- more than 3 operands, rewrite it as an inequality instead:
--     --      if all operands are 0           then 0 else 1
--     --  =>  if the sum of operands is 0     then 0 else 1
--     --  =>  if the sum of operands is not 0 then 1 else 0
--     --  =>  the sum of operands is not 0

--     let sumOfOperands = AddF (BtoF x0) (BtoF x1) (fmap BtoF xs)
--     case out of
--       -- if the output is 0, then the sum of operands must be 0
--       ValB 0 -> assertExprF 0 sumOfOperands
--       -- if the output is 1, then the sum of operands must not be 0
--       ValB _ -> assertNotZeroF sumOfOperands
--       _ -> do
--         out' <- wireB out
--         compileExprB
--           out'
--           ( NEqF
--               (ValF 0)
--               ( AddF
--                   (BtoF x0)
--                   (BtoF x1)
--                   (fmap BtoF xs)
--               )
--           )

compileXorB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
compileXorB out x y = do
  -- (1 - 2x) * (y + 1) = (1 + out - 3x)
  add $
    cMulF
      (1, [(RefBtoRefF x, -2)])
      (1, [(RefBtoRefF y, 1)])
      (1, [(RefBtoRefF x, -3), (RefBtoRefF out, 1)])

--------------------------------------------------------------------------------

-- assertExprB :: (GaloisField n, Integral n) => Bool -> ExprB n -> M n ()
-- assertExprB val expr = do
--   ref <- wireB expr
--   add [CVarBindB ref (if val then 1 else 0)]

-- assertExprF :: (GaloisField n, Integral n) => n -> ExprF n -> M n ()
-- assertExprF val expr = do
--   ref <- wireF expr
--   add [CVarBindF ref val]

-- assertNotZeroF :: (GaloisField n, Integral n) => ExprF n -> M n ()
-- assertNotZeroF expr = do
--   ref <- wireF expr
--   -- introduce a new variable m, such that `expr * m = 1`
--   m <- freshRefF
--   add $
--     cMulF
--       (0, [(ref, 1)])
--       (0, [(m, 1)])
--       (1, [])

assertNotZeroU :: (GaloisField n, Integral n) => Width -> ExprU n -> M n ()
assertNotZeroU width expr = do
  ref <- wireU expr
  -- introduce a new variable m, such that `expr * m = 1`
  m <- freshRefU width
  add $
    cMulF
      (0, [(RefUVal ref, 1)])
      (0, [(RefUVal m, 1)])
      (1, [])

-- | Assert that x is less than or equal to y
--
-- TODO, replace with a more efficient implementation
--  as in A.3.2.2 Range check in https://zips.z.cash/protocol/protocol.pdf
-- assertLTEU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> M n ()
-- assertLTEU width x y = do
--   --    x ≤ y
--   --  =>
--   --    0 ≤ y - x
--   --  that is, there exists a BinRep of y - x
--   difference <- freshRefU width
--   compileSubU width difference y x
assertLTU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> M n ()
assertLTU width x y = do
  --    x < y
  --  =>
  --    0 < y - x
  --  that is, there exists a non-zero BinRep of y - x
  difference <- freshExprU width
  difference' <- wireU difference
  compileSubU width difference' y x
  assertNotZeroU width difference

-- -- | Assert that the BinRep of a UInt is non-zero
-- assertBinRepNonZeroU :: (GaloisField n, Integral n) => Width -> ExprU n -> M n ()
-- assertBinRepNonZeroU width x
--   | width < 1 = error "[ panic ] assertBinRepNonZeroU: width of a UInt must be at least 1"
--   | width == 1 = do
--       --    x != 0
--       --  =>
--       --    x == 1
--       --  =>
--       --    x[0] == 1
--       assertExprB True (BitU x 0)
--   | width == 2 = do
--       --    x != 0
--       --  =>
--       --    x[0] ∨ x[1] == 1
--       --  =>
--       --    (1 - x[0]) * x[1] = (1 - x[0])
--       assertOrB (ValB 1) (BitU x 0) (BitU x 1)
--   | width == 3 = do
--       --    x != 0
--       --  =>
--       --    x[0] + x[1] + ... + x[n] != 0
--       --  =>
--       --    (1 - x[0]) * x[1] = (1 - x[0])
--       --    (1 - x[0]) * x[2] = (1 - x[0])
--       return ()

--  = case compare width 1 of
--   LT -> error "[ panic ] assertBinRepNonZeroU: width of a UInt must be at least 1"
--   EQ -> do
--       --    divisor != 0
--       --  =>
--       --    divisor == 1
--       --  =>
--       --    divisor[0] == 1
--       add [CVarBindB (RefUBit width divisor 0) 1]
--   GT -> do

--         -- more than 3 operands, rewrite it as an inequality instead:
--         --      if all operands are 0           then 0 else 1
--         --  =>  if the sum of operands is 0     then 0 else 1
--         --  =>  if the sum of operands is not 0 then 1 else 0
--         --  =>  the sum of operands is not 0

--   one <- freshRefU width
--   compileSubU width one x (ValU width 1)
--   GT -> do
--     --    divisor != 0
--     --  =>
--     --    conjunction of all bits of divisor = 1
--     compileOrBs
--     -- add $ cGeqB (0, [(divisor, 1)]) (0, [(RefUtoRefB quotient, 2)])
-- -- compileOrBs

-- | Division with remainder on UInts
--    1. dividend = divisor * quotient + remainder
--    2. 0 ≤ remainder < divisor
--    3. 0 < divisor
compileDivModU :: (GaloisField n, Integral n) => Width -> ExprU n -> ExprU n -> ExprU n -> ExprU n -> M n ()
compileDivModU width dividend divisor quotient remainder = do
  --    dividend = divisor * quotient + remainder
  --  =>
  --    divisor * quotient = dividend - remainder
  remainderRef <- wireU remainder
  divisorRef <- wireU divisor
  quotientRef <- wireU quotient
  dividendRef <- wireU dividend
  addDivModHint dividendRef divisorRef quotientRef remainderRef
  add $
    cMulF
      (0, [(RefUVal divisorRef, 1)])
      (0, [(RefUVal quotientRef, 1)])
      (0, [(RefUVal dividendRef, 1), (RefUVal remainderRef, -1)])
  --    0 ≤ remainder < divisor
  assertLTU width remainderRef divisorRef
  -- --    0 < divisor
  -- -- =>
  -- --    divisor != 0
  assertNotZeroU width divisor

--------------------------------------------------------------------------------

-- | Assert that a UInt is smaller than or equal to some constant
-- reference doc: A.3.2.2 Range Check https://zips.z.cash/protocol/protocol.pdf
assertLTE :: (GaloisField n, Integral n) => Width -> ExprU n -> Integer -> M n ()
assertLTE width a c = do
  ref <- wireU a
  -- because we don't have to execute the `go` function for trailing ones of `c`
  -- we can limit the range of bits of c from `[width-1, width-2 .. 0]` to `[width-1, width-2 .. countTrailingOnes]`
  foldM_ (go ref) Nothing [width - 1, width - 2 .. (width - 2) `min` countTrailingOnes]
  where
    -- for counting the number of trailing ones of `c`
    countTrailingOnes :: Int
    countTrailingOnes =
      fst $
        foldl
          ( \(count, keepCounting) i ->
              if keepCounting && Data.Bits.testBit c i then (count + 1, True) else (count, False)
          )
          (0, True)
          [0 .. width - 1]

    go :: (GaloisField n, Integral n) => RefU -> Maybe RefF -> Int -> M n (Maybe RefF)
    go ref Nothing i =
      let aBit = RefUBit width ref i
       in -- have not found the first bit in 'c' that is 1 yet
          if Data.Bits.testBit c i
            then do
              return $ Just (RefBtoRefF aBit) -- when found, return a[i] and a counter
            else do
              -- a[i] = 0
              add $ cVarBindB aBit 0
              return Nothing -- otherwise, continue searching
    go ref (Just acc) i =
      let aBit = RefBtoRefF (RefUBit width ref i)
       in if Data.Bits.testBit c i
            then do
              -- constraint for the next accumulator
              acc' <- freshRefF
              add $ cMulF (0, [(acc, 1)]) (0, [(aBit, 1)]) (0, [(F acc', 1)])
              return $ Just (F acc')
            else do
              -- constraint on a[i]
              add $ cMulF (1, [(acc, -1), (aBit, -1)]) (0, [(aBit, 1)]) (0, [])
              -- pass down the accumulator
              return $ Just acc