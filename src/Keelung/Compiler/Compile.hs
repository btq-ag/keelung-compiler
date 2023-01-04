{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Monad
import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (foldl'), toList)
import qualified Data.IntMap as IntMap
import Data.Sequence (Seq (..))
import qualified Data.Set as Set
import qualified Keelung.Compiler.Constraint as Constraint
import Keelung.Compiler.Constraint2
import qualified Keelung.Compiler.Constraint2 as Constraint2
import Keelung.Compiler.Syntax.FieldBits (FieldBits (..))
import Keelung.Compiler.Syntax.Untyped
import Keelung.Data.Struct (Struct (..))
import Keelung.Syntax.Counters (Counters, VarSort (..), VarType (..), addCount, getCount)

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => TypeErased n -> Constraint.ConstraintSystem n
run (TypeErased untypedExprs _ counters relations assertions) = runM counters $ do
  forM_ untypedExprs $ \untypedExpr -> do
    case untypedExpr of
      ExprB x -> do
        out <- freshRefBO
        compileExprB out x
      ExprF x -> do
        out <- freshRefFO
        compileExprF out x
      ExprU x -> do
        out <- freshRefUO (widthOfU x)
        compileExprU out x

  -- compile all relations to constraints
  compileRelations relations

  -- compile assertions to constraints
  mapM_ compileAssertion assertions

  constraints <- gets envConstraints

  -- get new counters because the output variables have been bumped
  counters' <- gets envCounters

  return
    ( Constraint.ConstraintSystem
        (Set.fromList $ map (Constraint2.fromConstraint counters') constraints)
        counters'
    )

-- | Compile the constraint 'out = x'.
compileAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
compileAssertion expr = do
  -- 1 = expr
  case expr of
    ExprB x -> do
      out <- freshRefB
      compileExprB out x
      add $ cAddB 1 [(out, -1)]
    ExprF x -> do
      out <- freshRefF
      compileExprF out x
      add $ cAddF 1 [(out, -1)]
    ExprU x -> do
      out <- freshRefU (widthOfU x)
      compileExprU out x
      add $ cVarBindU out 1

compileRelations :: (GaloisField n, Integral n) => Relations n -> M n ()
compileRelations (Relations vb vbi eb ebi) = do
  -- intermediate variable bindings of values
  forM_ (IntMap.toList (structF vb)) $ \(var, val) -> add $ cAddF val [(RefF var, -1)]
  forM_ (IntMap.toList (structB vb)) $ \(var, val) -> add $ cAddB val [(RefB var, -1)]
  forM_ (IntMap.toList (structU vb)) $ \(width, bindings) ->
    forM_ (IntMap.toList bindings) $ \(var, val) -> add $ cVarBindU (RefU width var) val
  -- input variable bindings of values
  forM_ (IntMap.toList (structF vbi)) $ \(var, val) -> add $ cAddF val [(RefFI var, -1)]
  forM_ (IntMap.toList (structB vbi)) $ \(var, val) -> add $ cAddB val [(RefBI var, -1)]
  forM_ (IntMap.toList (structU vbi)) $ \(width, bindings) ->
    forM_ (IntMap.toList bindings) $ \(var, val) -> add $ cVarBindU (RefUI width var) val
  -- intermediate variable bindings of expressions
  forM_ (IntMap.toList (structF eb)) $ \(var, val) -> compileExprF (RefF var) val
  forM_ (IntMap.toList (structB eb)) $ \(var, val) -> compileExprB (RefB var) val
  forM_ (IntMap.toList (structU eb)) $ \(width, bindings) ->
    forM_ (IntMap.toList bindings) $ \(var, val) -> compileExprU (RefU width var) val
  -- input variable bindings of expressions
  forM_ (IntMap.toList (structF ebi)) $ \(var, val) -> compileExprF (RefFI var) val
  forM_ (IntMap.toList (structB ebi)) $ \(var, val) -> compileExprB (RefBI var) val
  forM_ (IntMap.toList (structU ebi)) $ \(width, bindings) ->
    forM_ (IntMap.toList bindings) $ \(var, val) -> compileExprU (RefUI width var) val

--------------------------------------------------------------------------------

-- | Monad for compilation
data Env n = Env
  { envCounters :: Counters,
    envConstraints :: [Constraint n]
  }

type M n = State (Env n)

runM :: GaloisField n => Counters -> M n a -> a
runM counters program = evalState program (Env counters mempty)

modifyCounter :: (Counters -> Counters) -> M n ()
modifyCounter f = modify (\env -> env {envCounters = f (envCounters env)})

add :: GaloisField n => [Constraint n] -> M n ()
add cs =
  modify (\env -> env {envConstraints = cs <> envConstraints env})

freshRefF :: M n RefF
freshRefF = do
  counters <- gets envCounters
  let index = getCount OfIntermediate OfField counters
  modifyCounter $ addCount OfIntermediate OfField 1
  return $ RefF index

-- fresh :: M n RefB
fresh :: VarSort -> VarType -> (Int -> ref) -> M n ref
fresh sort kind ctor = do
  counters <- gets envCounters
  let index = getCount sort kind counters
  modifyCounter $ addCount sort kind 1
  return $ ctor index

freshRefBO :: M n RefB
freshRefBO = fresh OfOutput OfBoolean RefBO

freshRefFO :: M n RefF
freshRefFO = fresh OfOutput OfField RefFO

freshRefUO :: Width -> M n RefU
freshRefUO width = fresh OfOutput (OfUInt width) (RefUO width)

freshRefB :: M n RefB
freshRefB = do
  counters <- gets envCounters
  let index = getCount OfIntermediate OfBoolean counters
  modifyCounter $ addCount OfIntermediate OfBoolean 1
  return $ RefB index

freshRefU :: Width -> M n RefU
freshRefU width = do
  counters <- gets envCounters
  let index = getCount OfIntermediate (OfUInt width) counters
  modifyCounter $ addCount OfIntermediate (OfUInt width) 1
  return $ RefU width index

----------------------------------------------------------------

compileExprB :: (GaloisField n, Integral n) => RefB -> ExprB n -> M n ()
compileExprB out expr = case expr of
  ValB val -> add $ cAddB val [(out, -1)] -- out = val
  VarB var -> do
    add $ cAddB 0 [(out, 1), (RefB var, -1)] -- out = var
  VarBO var -> do
    add $ cAddB 0 [(out, 1), (RefBO var, -1)] -- out = var
  VarBI var -> do
    add $ cAddB 0 [(out, 1), (RefBI var, -1)] -- out = var
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
  XorB x y -> do
    x' <- wireB x
    y' <- wireB y
    compileXorB out x' y'
  NotB x -> do
    x' <- wireB x
    add $ cAddB 1 [(x', -1), (out, -1)] -- out = 1 - x
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
  BitU x i -> do
    x' <- wireU x
    add $ cAddB 0 [(out, 1), (RefUBit (widthOfU x) x' i, -1)] -- out = var

compileExprF :: (GaloisField n, Integral n) => RefF -> ExprF n -> M n ()
compileExprF out expr = case expr of
  ValF val -> add $ cAddF val [(out, -1)] -- out = val
  VarF var -> do
    add $ cAddF 0 [(out, 1), (RefF var, -1)] -- out = var
  VarFO var -> do
    add $ cAddF 0 [(out, 1), (RefFO var, -1)] -- out = var
  VarFI var -> do
    add $ cAddF 0 [(out, 1), (RefFI var, -1)] -- out = var
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
    add $ cAddF 0 [(out, 1), (RefBtoRefF result, -1)] -- out = var

compileExprU :: (GaloisField n, Integral n) => RefU -> ExprU n -> M n ()
compileExprU out expr = case expr of
  ValU width val -> do
    -- constraint for UInt : out = val
    add $ cVarBindU out val
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      let bit = testBit val i
      add $ cAddB bit [(RefUBit width out i, -1)] -- out = var
  VarU width var -> do
    let ref = RefU width var
    -- constraint for UInt : out = ref
    add $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      add $ cAddB 0 [(RefUBit width out i, -1), (RefUBit width ref i, 1)] -- out[i] = ref[i]
  VarUO width var -> do
    add $ cVarEqU out (RefU width var) -- out = var
  VarUI width var -> do
    let ref = RefUI width var
    -- constraint for UInt : out = ref
    add $ cVarEqU out ref
    -- constraints for BinRep of UInt
    forM_ [0 .. width - 1] $ \i -> do
      add $ cAddB 0 [(RefUBit width out i, -1), (RefUBit width ref i, 1)] -- out[i] = ref[i]
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
      add $ cAddB 0 [(RefUBit w out i, 1), (RefUBit w x' i', -1)]
  ShLU w n x -> do
    x' <- wireU x
    case compare n 0 of
      EQ -> add $ cVarEqU out x'
      GT -> do
        -- fill lower bits with 0s
        forM_ [0 .. n - 1] $ \i -> do
          add $ cAddB 0 [(RefUBit w out i, 1)]
        -- shift upper bits
        forM_ [n .. w - 1] $ \i -> do
          let i' = i - n
          add $ cAddB 0 [(RefUBit w out i, 1), (RefUBit w x' i', -1)]
      LT -> do
        -- shift lower bits
        forM_ [0 .. w + n - 1] $ \i -> do
          let i' = i - n
          add $ cAddB 0 [(RefUBit w out i, 1), (RefUBit w x' i', -1)]
        -- fill upper bits with 0s
        forM_ [w + n .. w - 1] $ \i -> do
          add $ cAddB 0 [(RefUBit w out i, 1)]
  BtoU w x -> do
    -- 1. wire 'out[ZERO]' to 'x'
    result <- freshRefB
    compileExprB result x
    add $ cAddB 0 [(RefUBit w out 0, 1), (result, -1)]
    -- 2. wire 'out[SUCC _]' to '0' for all other bits
    forM_ [1 .. w - 1] $ \i ->
      add $ cAddB 0 [(RefUBit w out i, 1)]

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
   in add $ cAddF constant $ (out, -1) : varsWithCoeffs
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
            RefU w _ -> w
            RefUI w _ -> w
            RefUO w _ -> w
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
  -- locate the binary representations of the operands
  -- xBinRepStart <- lookupBinRep width x
  -- yBinRepStart <- lookupBinRep width y

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
  --  (out - x) = (1 - p) * (y - x)
  add $
    cMulB
      (1, [(p, -1)])
      (0, [(x, -1), (y, 1)])
      (0, [(x, -1), (out, 1)])

compileIfF :: (GaloisField n, Integral n) => RefF -> RefB -> RefF -> RefF -> M n ()
compileIfF out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  (out - x) = (1 - p) * (y - x)
  add $
    cMulF
      (1, [(RefBtoRefF p, -1)])
      (0, [(x, -1), (y, 1)])
      (0, [(x, -1), (out, 1)])

compileIfU :: (GaloisField n, Integral n) => RefU -> RefB -> RefU -> RefU -> M n ()
compileIfU out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  (out - x) = (1 - p) * (y - x)
  add $
    cMulU
      (1, [(RefBtoRefU p, -1)])
      (0, [(x, -1), (y, 1)])
      (0, [(x, -1), (out, 1)])

compileOrB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
compileOrB out x y = do
  -- (1 - x) * y = (out - x)
  add $
    cMulB
      (1, [(x, -1)])
      (0, [(y, 1)])
      (0, [(x, -1), (out, 1)])

compileXorB :: (GaloisField n, Integral n) => RefB -> RefB -> RefB -> M n ()
compileXorB out x y = do
  -- (1 - 2x) * (y + 1) = (1 + out - 3x)
  add $
    cMulB
      (1, [(x, -2)])
      (1, [(y, 1)])
      (1, [(x, -3), (out, 1)])