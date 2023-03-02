{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Monad
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (foldl'), toList)
import Data.IntMap qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq (..))
import Keelung.Compiler.Constraint
import Keelung.Compiler.Optimize.MinimizeConstraints.UnionFind qualified as UnionFind
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax.Counters (Counters, VarSort (..), VarType (..), addCount, getCount)

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => Bool -> TypeErased n -> ConstraintSystem n
run useNewOptimizer (TypeErased untypedExprs _ counters relations assertions divModRelsU) = runM useNewOptimizer counters $ do
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

  -- compile all relations to constraints
  compileRelations relations

  -- compile assertions to constraints
  mapM_ compileAssertion assertions

  -- compile DivMod relations to constraints
  mapM_ (\(width, (dividend, divisor, quotient, remainder)) -> compileDivModU width dividend divisor quotient remainder) (IntMap.toList divModRelsU)

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
    add $ cVarBindF out 1
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
compileAssertionEqF (VarF a) (ValF b) = add $ cVarBindF (RefF a) b
compileAssertionEqF (VarF a) (VarF b) = add $ cVarEqF (RefF a) (RefF b)
compileAssertionEqF (VarF a) (VarFO b) = add $ cVarEqF (RefF a) (RefFO b)
compileAssertionEqF (VarF a) (VarFI b) = add $ cVarEqF (RefF a) (RefFI b)
compileAssertionEqF (VarF a) b = do
  out <- freshRefF
  compileExprF out b
  add $ cVarEqF (RefF a) out
compileAssertionEqF (VarFO a) (ValF b) = add $ cVarBindF (RefFO a) b
compileAssertionEqF (VarFO a) (VarF b) = add $ cVarEqF (RefFO a) (RefF b)
compileAssertionEqF (VarFO a) (VarFO b) = add $ cVarEqF (RefFO a) (RefFO b)
compileAssertionEqF (VarFO a) b = do
  out <- freshRefF
  compileExprF out b
  add $ cVarEqF (RefFO a) out
compileAssertionEqF (VarFI a) (ValF b) = add $ cVarBindF (RefFI a) b
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

compileRelations :: (GaloisField n, Integral n) => Relations n -> M n ()
compileRelations (Relations vb eb) = do
  -- intermediate variable bindings of values
  forM_ (IntMap.toList (structF vb)) $ \(var, val) -> add $ cVarBindF (RefF var) val
  forM_ (IntMap.toList (structB vb)) $ \(var, val) -> add $ cVarBindB (RefB var) val
  forM_ (IntMap.toList (structU vb)) $ \(width, bindings) ->
    forM_ (IntMap.toList bindings) $ \(var, val) -> add $ cVarBindU (RefU width var) val
  -- intermediate variable bindings of expressions
  forM_ (IntMap.toList (structF eb)) $ \(var, val) -> compileExprF (RefF var) val
  forM_ (IntMap.toList (structB eb)) $ \(var, val) -> compileExprB (RefB var) val
  forM_ (IntMap.toList (structU eb)) $ \(width, bindings) ->
    forM_ (IntMap.toList bindings) $ \(var, val) -> compileExprU (RefU width var) val

--------------------------------------------------------------------------------

-- | Monad for compilation
type M n = State (ConstraintSystem n)

runM :: GaloisField n => Bool -> Counters -> M n a -> ConstraintSystem n
runM useNewOptimizer counters program = execState program (ConstraintSystem counters useNewOptimizer mempty mempty mempty mempty UnionFind.new mempty UnionFind.new mempty mempty mempty mempty mempty mempty mempty mempty)

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\cs -> cs {csCounters = f (csCounters cs)})

add :: GaloisField n => [Constraint n] -> M n ()
add = mapM_ addOne
  where
    addOne :: GaloisField n => Constraint n -> M n ()
    addOne (CAddF xs) = modify (\cs -> cs {csAddF = xs : csAddF cs, csOccurrenceF = addOccurrencesWithPolyG xs (csOccurrenceF cs)})
    addOne (CAddB xs) = modify (\cs -> cs {csAddB = xs : csAddB cs, csOccurrenceB = addOccurrencesWithPolyG xs (csOccurrenceB cs)})
    addOne (CAddU xs) = modify (\cs -> cs {csAddU = xs : csAddU cs, csOccurrenceU = addOccurrencesWithPolyG xs (csOccurrenceU cs)})
    addOne (CVarBindF x c) = do
      cs <- get
      let csVarEqF' = UnionFind.bindToValue x c (csVarEqF cs)
      put cs {csVarEqF = csVarEqF'}
    addOne (CVarBindB x c) = modify (\cs -> cs {csVarBindB = Map.insert x c (csVarBindB cs), csOccurrenceB = addOccurrences [x] (csOccurrenceB cs)})
    -- addOne (CVarBindU x c) = modify (\cs -> cs {csVarBindU = Map.insert x c (csVarBindU cs), csOccurrenceU = addOccurrences [x] (csOccurrenceU cs)})
    addOne (CVarBindU x c) = do
      cs <- get
      let csVarEqU' = UnionFind.bindToValue x c (csVarEqU cs)
      put cs {csVarEqU = csVarEqU'}
    addOne (CVarEqF x y) = do
      cs <- get
      case UnionFind.relate x (1, y, 0) (csVarEqF cs) of
        Nothing -> return ()
        Just csVarEqF' -> put cs {csVarEqF = csVarEqF'}
    addOne (CVarEqB x y) = modify (\cs -> cs {csVarEqB = (x, y) : csVarEqB cs})
    -- addOne (CVarEqU x y) = modify (\cs -> cs {csVarEqU = (x, y) : csVarEqU cs})
    addOne (CVarEqU x y) = do
      cs <- get
      case UnionFind.relate x (1, y, 0) (csVarEqU cs) of
        Nothing -> return ()
        Just csVarEqU' -> put cs {csVarEqU = csVarEqU'}
    addOne (CMulF x y (Left c)) = modify (\cs -> cs {csMulF = (x, y, Left c) : csMulF cs, csOccurrenceF = addOccurrencesWithPolyG x $ addOccurrencesWithPolyG y (csOccurrenceF cs)})
    addOne (CMulF x y (Right z)) = modify (\cs -> cs {csMulF = (x, y, Right z) : csMulF cs, csOccurrenceF = addOccurrencesWithPolyG x $ addOccurrencesWithPolyG y $ addOccurrencesWithPolyG z (csOccurrenceF cs)})
    addOne (CMulB x y (Left c)) = modify (\cs -> cs {csMulB = (x, y, Left c) : csMulB cs, csOccurrenceB = addOccurrencesWithPolyG x $ addOccurrencesWithPolyG y (csOccurrenceB cs)})
    addOne (CMulB x y (Right z)) = modify (\cs -> cs {csMulB = (x, y, Right z) : csMulB cs, csOccurrenceB = addOccurrencesWithPolyG x $ addOccurrencesWithPolyG y $ addOccurrencesWithPolyG z (csOccurrenceB cs)})
    addOne (CMulU x y (Left c)) = modify (\cs -> cs {csMulU = (x, y, Left c) : csMulU cs, csOccurrenceU = addOccurrencesWithPolyG x $ addOccurrencesWithPolyG y (csOccurrenceU cs)})
    addOne (CMulU x y (Right z)) = modify (\cs -> cs {csMulU = (x, y, Right z) : csMulU cs, csOccurrenceU = addOccurrencesWithPolyG x $ addOccurrencesWithPolyG y $ addOccurrencesWithPolyG z (csOccurrenceU cs)})
    addOne (CNEqF x y m) = modify (\cs -> cs {csNEqF = Map.insert (x, y) m (csNEqF cs), csOccurrenceF = addOccurrences [x, y, m] (csOccurrenceF cs)})
    addOne (CNEqU x y m) = modify (\cs -> cs {csNEqU = Map.insert (x, y) m (csNEqU cs), csOccurrenceU = addOccurrences [x, y, m] (csOccurrenceU cs)})

freshRefF :: M n RefF
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

freshVarU :: Width -> M n (ExprU n)
freshVarU width = do
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
        add $ cMulSimpleB a b out -- out = a * b
      (c :<| Empty) -> do
        aAndb <- freshRefB
        add $ cMulSimpleB a b aAndb -- aAndb = a * b
        add $ cMulSimpleB aAndb c out -- out = aAndb * c
      _ -> do
        -- the number of operands
        let n = 2 + fromIntegral (length vars)
        -- polynomial = n - sum of operands
        let polynomial = (n, (a, -1) : (b, -1) : [(v, -1) | v <- toList vars])
        -- if the answer is 1 then all operands must be 1
        --    (n - sum of operands) * out = 0
        add $
          cMulB
            polynomial
            (0, [(out, 1)])
            (0, [])
        -- if the answer is 0 then not all operands must be 1:
        --    (n - sum of operands) * inv = 1 - out
        inv <- freshRefB
        add $
          cMulB
            polynomial
            (0, [(inv, 1)])
            (1, [(out, -1)])
  OrB x0 x1 xs -> do
    compileOrBs out x0 x1 xs
  XorB x y -> do
    x' <- wireB x
    y' <- wireB y
    compileXorB out x' y'
  NotB x -> do
    x' <- wireB x
    add $ cAddB 1 [(x', -1), (out, -1)] -- out = 1 - x'
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
      cMulB
        (1, [(x', -1)])
        (1, [(y', -2)])
        (0, [(out, 1), (y', -1)])
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
    add $ cVarEqB out (RefUBit (widthOfU x) x' i) -- out = x'[i]

compileExprF :: (GaloisField n, Integral n) => RefF -> ExprF n -> M n ()
compileExprF out expr = case expr of
  ValF val -> add $ cVarBindF out val -- out = val
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
    add $ cMulSimpleF x' y' out
  DivF x y -> do
    x' <- wireF x
    y' <- wireF y
    add $ cMulSimpleF y' out x'
  IfF p x y -> do
    p' <- wireB p
    x' <- wireF x
    y' <- wireF y
    compileIfF out p' x' y'
  BtoF x -> do
    result <- freshRefB
    compileExprB result x
    add $ cVarEqF out (RefBtoRefF result) -- out = var

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
    let ref = RefU width var
    -- constraint for UInt : out = ref
    add $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      add $ cVarEqB (RefUBit width out i) (RefUBit width ref i) -- out[i] = ref[i]
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
  | WithVars RefF n -- cx

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

compileTerms :: GaloisField n => RefF -> Seq (Term n) -> M n ()
compileTerms out terms =
  let (constant, varsWithCoeffs) = foldl' go (0, []) terms
   in case varsWithCoeffs of
        [] -> add $ cVarBindF out constant
        _ -> add $ cAddF constant $ (out, -1) : varsWithCoeffs
  where
    go :: Num n => (n, [(RefF, n)]) -> Term n -> (n, [(RefF, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (var, coeff) : pairs)

-- | If the expression is not already a variable, create a new variable
wireB :: (GaloisField n, Integral n) => ExprB n -> M n RefB
wireB (VarB ref) = return (RefB ref)
wireB (VarBO ref) = return (RefBO ref)
wireB (VarBI ref) = return (RefBI ref)
wireB expr = do
  out <- freshRefB
  compileExprB out expr
  return out

wireF :: (GaloisField n, Integral n) => ExprF n -> M n RefF
wireF (VarF ref) = return (RefF ref)
wireF (VarFO ref) = return (RefFO ref)
wireF (VarFI ref) = return (RefFI ref)
wireF expr = do
  out <- freshRefF
  compileExprF out expr
  return out

wireU :: (GaloisField n, Integral n) => ExprU n -> M n RefU
wireU (VarU w ref) = return (RefU w ref)
wireU (VarUO w ref) = return (RefUO w ref)
wireU (VarUI w ref) = return (RefUI w ref)
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
      -- if diff = 0 then m = 0 else m = recip diff
      let width = case x of
            RefUO w _ -> w
            RefUI w _ -> w
            RefUP w _ -> w
            RefU w _ -> w
            RefBtoRefU _ -> 1 -- TODO: reexamine this
      m <- freshRefU width

      if isEq
        then do
          --  1. (x - y) * m = 1 - out
          --  2. (x - y) * out = 0
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (1, [(RefBtoRefU out, -1)])
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (0, [(RefBtoRefU out, 1)])
              (0, [])
        else do
          --  1. (x - y) * m = out
          --  2. (x - y) * (1 - out) = 0
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (0, [(RefBtoRefU out, 1)])
          add $
            cMulU
              (0, [(x, 1), (y, -1)])
              (1, [(RefBtoRefU out, -1)])
              (0, [])

      --  keep track of the relation between (x - y) and m
      add $ cNEqU x y m

compileEqualityF :: (GaloisField n, Integral n) => Bool -> RefB -> RefF -> RefF -> M n ()
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
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (1, [(RefBtoRefF out, -1)])
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (0, [(RefBtoRefF out, 1)])
              (0, [])
        else do
          --  1. (x - y) * m = out
          --  2. (x - y) * (1 - out) = 0
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (0, [(m, 1)])
              (0, [(RefBtoRefF out, 1)])
          add $
            cMulF
              (0, [(x, 1), (y, -1)])
              (1, [(RefBtoRefF out, -1)])
              (0, [])

      --  keep track of the relation between (x - y) and m
      add $ cNEqF x y m

--------------------------------------------------------------------------------

-- | Encoding addition on UInts with multiple operands: O(1)
--    C = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
compileAddOrSubU :: (GaloisField n, Integral n) => Bool -> Width -> RefU -> RefU -> RefU -> M n ()
compileAddOrSubU isSub width out x y = do
  let multiplier = 2 ^ width
  -- We can refactor
  --    out = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
  -- into the form of
  --    (-2ⁿ * Aₙ₋₁) * (Bₙ₋₁) = (out - A - B)
  add $
    cMulU
      (0, [(RefBtoRefU (RefUBit width x (width - 1)), -multiplier)])
      (0, [(RefBtoRefU (RefUBit width y (width - 1)), 1)])
      (0, [(out, 1), (x, -1), (y, if isSub then 1 else -1)])

compileAddU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileAddU = compileAddOrSubU False

compileSubU :: (GaloisField n, Integral n) => Width -> RefU -> RefU -> RefU -> M n ()
compileSubU = compileAddOrSubU True

-- | Encoding addition on UInts with multiple operands: O(2)
--    C + 2ⁿ * Q = A * B
compileMulU :: (GaloisField n, Integral n) => Int -> RefU -> RefU -> RefU -> M n ()
compileMulU width out a b = do
  -- (a) * (b) = result + 2ⁿ * quotient
  quotient <- freshRefU width
  add $ cMulU (0, [(a, 1)]) (0, [(b, 1)]) (0, [(out, 1), (quotient, 2 ^ width)])

-- | An universal way of compiling a conditional
compileIfB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> RefB -> M n ()
compileIfB out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  out = p * x + y - p * y
  --      =>
  --  (out - y) = p * (x - y)
  add $
    cMulB
      (0, [(p, 1)])
      (0, [(x, 1), (y, -1)])
      (0, [(y, -1), (out, 1)])

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
    cMulU
      (0, [(RefBtoRefU p, 1)])
      (0, [(x, 1), (y, -1)])
      (0, [(y, -1), (out, 1)])

compileOrB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
compileOrB out x y = do
  -- (1 - x) * y = (out - x)
  add $
    cMulB
      (1, [(x, -1)])
      (0, [(y, 1)])
      (0, [(x, -1), (out, 1)])

-- assertOrB :: (GaloisField n, Integral n) => ExprB n -> ExprB n -> ExprB n -> M n ()
-- assertOrB (ValB 0) (ValB 0) (ValB 0) = return ()
-- assertOrB (ValB 0) (ValB _) (ValB _) = error "[ error ] assertOrB: invalid constraint"
-- assertOrB (ValB 1) (ValB 0) (ValB 0) = error "[ error ] assertOrB: invalid constraint"
-- assertOrB (ValB 1) (ValB _) (ValB _) = return ()
-- assertOrB out x y = do
--   out' <- wireB out
--   x' <- wireB x
--   y' <- wireB y
--   -- (1 - x) * y = (out - x)
--   add $
--     cMulB
--       (1, [(x', -1)])
--       (0, [(y', 1)])
--       (0, [(x', -1), (out', 1)])

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
    cMulB
      (1, [(x, -2)])
      (1, [(y, 1)])
      (1, [(x, -3), (out, 1)])

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
    cMulU
      (0, [(ref, 1)])
      (0, [(m, 1)])
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
  difference <- freshVarU width
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
  add $
    cMulU
      (0, [(divisorRef, 1)])
      (0, [(quotientRef, 1)])
      (0, [(dividendRef, 1), (remainderRef, -1)])
  --    0 ≤ remainder < divisor
  assertLTU width remainderRef divisorRef
  -- --    0 < divisor
  -- -- =>
  -- --    divisor != 0
  assertNotZeroU width divisor