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
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Compiler.Constraint
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1CS (CNEQ (..))
import Keelung.Syntax.BinRep (BinRep (..), BinReps)
import qualified Keelung.Syntax.BinRep as BinRep
import Keelung.Syntax.VarCounters
import Keelung.Types

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => TypeErased n -> ConstraintSystem n
run (TypeErased untypedExprs counters relations assertions assignments numBinReps customBinReps) = runM counters $ do
  -- we need to encode `untypedExprs` to constriants and wire them to 'outputVars'
  forM_ (zip (outputVars counters) untypedExprs) (uncurry encode)

  -- Compile all relations
  encodeRelations relations

  -- Compile assignments to constraints
  mapM_ encodeAssignment assignments

  -- Compile assertions to constraints
  mapM_ encodeAssertion assertions

  constraints <- gets envConstraints

  extraBinReps <- gets envExtraBinReps

  counters' <- gets envVarCounters

  return
    ( ConstraintSystem
        constraints
        numBinReps
        (customBinReps <> extraBinReps)
        counters'
    )

-- | Encode the constraint 'out = x'.
encodeAssertion :: (GaloisField n, Integral n) => Expr n -> M n ()
encodeAssertion expr = do
  out <- freshVar
  encode out expr
  add $ cadd 1 [(out, -1)] -- 1 = expr

-- | Encode the constraint 'out = expr'.
encodeAssignment :: (GaloisField n, Integral n) => Assignment n -> M n ()
encodeAssignment (AssignmentB var expr) = encodeExprB var expr
encodeAssignment (AssignmentN var expr) = encodeExprN var expr
encodeAssignment (AssignmentU var expr) = encodeExprU var expr

-- encodeRelation :: (GaloisField n, Integral n) => Relation n -> M n ()
-- encodeRelation (Relation bindings assignments assertions) = do
--   forM_ (IntMap.toList bindings) $ \(var, val) -> add $ cadd val [(var, -1)]
--   forM_ (IntMap.toList assignments) $ uncurry encode
--   forM_ assertions $ \expr -> do
--       out <- freshVar
--       encode out expr
--       add $ cadd 1 [(out, -1)] -- 1 = expr

encodeValueBindings :: (GaloisField n, Integral n) => Bindings n -> M n ()
encodeValueBindings bindings = do
  forM_ (IntMap.toList (bindingsN bindings)) $ \(var, val) -> add $ cadd val [(var, -1)]
  forM_ (IntMap.toList (bindingsB bindings)) $ \(var, val) -> add $ cadd val [(var, -1)]
  forM_ (IntMap.toList (bindingsUs bindings)) $ \(_, bindings') ->
    forM_ (IntMap.toList bindings') $ \(var, val) -> add $ cadd val [(var, -1)]

encodeExprBindings :: (GaloisField n, Integral n) => Bindings (Expr n) -> M n ()
encodeExprBindings bindings = do
  forM_ (IntMap.toList (bindingsN bindings)) $ uncurry encode
  forM_ (IntMap.toList (bindingsB bindings)) $ uncurry encode
  forM_ (IntMap.toList (bindingsUs bindings)) $ \(_, bindings') ->
    forM_ (IntMap.toList bindings') $ uncurry encode

encodeRelations :: (GaloisField n, Integral n) => Relations n -> M n ()
encodeRelations (Relations vbs ebs) = do
  encodeValueBindings vbs
  encodeExprBindings ebs

--------------------------------------------------------------------------------

-- | Monad for compilation
data Env n = Env
  { envVarCounters :: VarCounters,
    envConstraints :: Set (Constraint n),
    envExtraBinReps :: BinReps
  }

type M n = State (Env n)

runM :: GaloisField n => VarCounters -> M n a -> a
runM varCounters program = evalState program (Env varCounters mempty mempty)

add :: GaloisField n => [Constraint n] -> M n ()
add cs =
  modify (\env -> env {envConstraints = Set.union (Set.fromList cs) (envConstraints env)})

-- | Adds a new view of binary representation of a variable after rotation.
addRotatedBinRep :: Var -> Width -> Var -> Int -> M n ()
addRotatedBinRep out width var rotate = do
  index <- lookupBinRepIndex width var
  addBinRep $ BinRep out width index rotate

addBinRep :: BinRep -> M n ()
addBinRep binRep = modify (\env -> env {envExtraBinReps = BinRep.insert binRep (envExtraBinReps env)})

freshVar :: M n Var
freshVar = do
  n <- gets (totalVarSize . envVarCounters)
  modify' (\ctx -> ctx {envVarCounters = bumpIntermediateVar (envVarCounters ctx)})
  return n

freshBinRep :: Var -> Int -> M n ()
freshBinRep var width
  | width < 1 = error $ "[ panic ] Cannot create a binary representation of width " <> show width
  | otherwise = do
    vars <- replicateM width freshVar
    addBinRep $ BinRep var width (head vars) 0

-- | Locate the binary representations of some variable
lookupBinRepIndex :: Int -> Var -> M n Var
lookupBinRepIndex width var = do
  counters <- gets envVarCounters
  extraBinReps <- gets envExtraBinReps
  case lookupBinRepStart counters var of
    Nothing -> do
      case BinRep.lookup width var extraBinReps of
        Nothing -> error $ "lookupBinRep: could not find binary representation of " ++ show var
        Just binRep -> return (binRepBitsIndex binRep)
    Just index -> return index

getNumberBitWidth :: M n Width
getNumberBitWidth = gets (getNumBitWidth . envVarCounters)

----------------------------------------------------------------

encodeExprB :: (GaloisField n, Integral n) => Var -> ExprB n -> M n ()
encodeExprB out expr = case expr of
  ValB val -> add $ cadd val [(out, -1)] -- out = val
  VarB var -> do
    counters <- gets envVarCounters
    let var' = blendIntermediateVar counters var
    add $ cadd 0 [(out, 1), (var', -1)] -- out = var
  InputVarB var -> do
    counters <- gets envVarCounters
    let var' = blendInputVarB counters var
    add $ cadd 0 [(out, 1), (var', -1)] -- out = var
  AndB x0 x1 xs -> do
    a <- wireAsVar (ExprB x0)
    b <- wireAsVar (ExprB x1)
    vars <- mapM (wireAsVar . ExprB) xs
    case vars of
      Empty -> add [CMul (Poly.singleVar a) (Poly.singleVar b) (Right (Poly.singleVar out))] -- out = a * b
      (c :<| Empty) -> do
        aAndb <- freshVar
        add [CMul (Poly.singleVar a) (Poly.singleVar b) (Right (Poly.singleVar aAndb))] -- x = a * b
        add [CMul (Poly.singleVar aAndb) (Poly.singleVar c) (Right (Poly.singleVar out))] -- out = x * c
      _ -> do
        -- the number of operands
        let n = 2 + fromIntegral (length vars)
        -- polynomial = n - sum of operands
        let polynomial = case Poly.buildMaybe n (IntMap.fromList ((a, -1) : (b, -1) : [(v, -1) | v <- toList vars])) of
              Just p -> p
              Nothing -> error "encode: And: impossible"
        -- if the answer is 1 then all operands must be 1
        --    (n - sum of operands) * out = 0
        add [CMul polynomial (Poly.singleVar out) (Left 0)]
        -- if the answer is 0 then not all operands must be 1:
        --    (n - sum of operands) * inv = 1 - out
        inv <- freshVar
        add [CMul polynomial (Poly.singleVar inv) (Poly.buildEither 1 [(out, -1)])]
  OrB x0 x1 xs -> do
    a <- wireAsVar (ExprB x0)
    b <- wireAsVar (ExprB x1)
    vars <- mapM (wireAsVar . ExprB) xs
    case vars of
      Empty -> add [COr a b out]
      (c :<| Empty) -> do
        -- only 3 operands
        aOrb <- freshVar
        add [COr a b aOrb]
        add [COr aOrb c out]
      _ -> do
        -- more than 3 operands, rewrite it as an inequality instead:
        --      if all operands are 0           then 0 else 1
        --  =>  if the sum of operands is 0     then 0 else 1
        --  =>  if the sum of operands is not 0 then 1 else 0
        --  =>  the sum of operands is not 0
        numBitWidth <- getNumberBitWidth
        encodeExprB
          out
          ( NEqN
              (ValN numBitWidth 0)
              ( AddN
                  numBitWidth
                  (BtoN numBitWidth x0)
                  (BtoN numBitWidth x1)
                  (fmap (BtoN numBitWidth) xs)
              )
          )
  XorB x y -> do
    x' <- wireAsVar (ExprB x)
    y' <- wireAsVar (ExprB y)
    add [CXor x' y' out]
  IfB p x y -> do
    p' <- wireAsVar (ExprB p)
    x' <- wireAsVar (ExprB x)
    y' <- wireAsVar (ExprB y)
    encodeIf out p' x' y'
  NEqB x y -> encodeExprB out (XorB x y)
  NEqN x y -> do
    x' <- wireAsVar (ExprN x)
    y' <- wireAsVar (ExprN y)
    encodeEquality False out x' y'
  NEqU x y -> do
    x' <- wireAsVar (ExprU x)
    y' <- wireAsVar (ExprU y)
    encodeEquality False out x' y'
  EqB x y -> do
    x' <- wireAsVar (ExprB x)
    y' <- wireAsVar (ExprB y)
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    --     x * y + (1 - x) * (1 - y) = out
    -- =>
    --    (1 - x) * (1 - 2y) = (out - y)

    -- (1 - x)
    let polynomial1 = case Poly.buildEither 1 [(x', -1)] of
          Left _ -> error "encode: EqB: impossible"
          Right xs -> xs
    -- (1 - 2y)
    let polynomial2 = case Poly.buildEither 1 [(y', -2)] of
          Left _ -> error "encode: EqB: impossible"
          Right xs -> xs
    -- (out - y)
    let polynomial3 = Poly.buildEither 0 [(y', -1), (out, 1)]
    add [CMul polynomial1 polynomial2 polynomial3]
  EqN x y -> do
    x' <- wireAsVar (ExprN x)
    y' <- wireAsVar (ExprN y)
    encodeEquality True out x' y'
  EqU x y -> do
    x' <- wireAsVar (ExprU x)
    y' <- wireAsVar (ExprU y)
    encodeEquality True out x' y'
  BitU x i -> error "[ panic ] Dunnot how to compile BitU"

encodeExprN :: (GaloisField n, Integral n) => Var -> ExprN n -> M n ()
encodeExprN out expr = case expr of
  ValN _ val -> add $ cadd val [(out, -1)] -- out = val
  VarN _ var -> do
    counters <- gets envVarCounters
    let var' = blendIntermediateVar counters var
    add $ cadd 0 [(out, 1), (var', -1)] -- out = var
  InputVarN _ var -> do
    counters <- gets envVarCounters
    let var' = blendInputVarN counters var
    add $ cadd 0 [(out, 1), (var', -1)] -- out = var
  SubN _ x y -> do
    x' <- toTermN x
    y' <- toTermN y
    encodeTerms out (x' :<| negateTerm y' :<| Empty)
  AddN _ x y rest -> do
    terms <- mapM toTermN (x :<| y :<| rest)
    encodeTerms out terms
  MulN _ x y -> do
    x' <- wireAsVar (ExprN x)
    y' <- wireAsVar (ExprN y)
    add [CMul (Poly.singleVar x') (Poly.singleVar y') (Right $ Poly.singleVar out)]
  DivN _ x y -> do
    x' <- wireAsVar (ExprN x)
    y' <- wireAsVar (ExprN y)
    add [CMul (Poly.singleVar y') (Poly.singleVar out) (Right $ Poly.singleVar x')]
  IfN _ p x y -> do
    p' <- wireAsVar (ExprB p)
    x' <- wireAsVar (ExprN x)
    y' <- wireAsVar (ExprN y)
    encodeIf out p' x' y'
  BtoN _ x -> encodeExprB out x

encodeExprU :: (GaloisField n, Integral n) => Var -> ExprU n -> M n ()
encodeExprU out expr = case expr of
  ValU _ val -> add $ cadd val [(out, -1)] -- out = val
  VarU _ var -> do
    counters <- gets envVarCounters
    let var' = blendIntermediateVar counters var
    add $ cadd 0 [(out, 1), (var', -1)] -- out = var
  InputVarU w var -> do
    counters <- gets envVarCounters
    let var' = blendInputVarU counters w var
    add $ cadd 0 [(out, 1), (var', -1)] -- out = var
  SubU w x y -> encodeAndFoldExprs (encodeUIntSub w) out (ExprU x) (ExprU y) mempty
  AddU w x y -> do
    x' <- wireAsVar (ExprU x)
    y' <- wireAsVar (ExprU y)
    freshBinRep out w
    encodeUIntAdd w out x' y'
  MulU w x y -> do
    x' <- wireAsVar (ExprU x)
    y' <- wireAsVar (ExprU y)
    freshBinRep out w
    encodeUIntMul w out x' y'
  AndU {} -> error "encodeExprU: AndU: not implemented"
  OrU {} -> error "encodeExprU: OrU: not implemented"
  XorU {} -> error "encodeExprU: XorB: not implemented"
  NotU {} -> error "encodeExprU: NotU: not implemented"
  IfU _ p x y -> do
    p' <- wireAsVar (ExprB p)
    x' <- wireAsVar (ExprU x)
    y' <- wireAsVar (ExprU y)
    encodeIf out p' x' y'
  RoLU {} -> error "encodeExprU: RoLU: not implemented"
  BtoU _ x -> encodeExprB out x

encode :: (GaloisField n, Integral n) => Var -> Expr n -> M n ()
encode out expr = case expr of
  -- values
  ExprB x -> encodeExprB out x
  ExprN x -> encodeExprN out x
  ExprU x -> encodeExprU out x

--------------------------------------------------------------------------------

-- | Pushes the constructor of Rotate inwards
-- encodeRotate :: (GaloisField n, Integral n) => Var -> Int -> ExprU n -> M n ()
-- encodeRotate out i expr = case expr of
--   -- ExprB x -> encode out (ExprB x)
--   -- ExprN x -> case x of
--   --   ValN w n -> do
--   --     n' <- rotateField w n
--   --     encode out (ExprN (ValN w n'))
--   --   VarN w var -> addRotatedBinRep out w var i
--   --   SubN {} -> error "[ panic ] dunno how to compile ROTATE SubN"
--   --   AddN w _ _ _ -> do
--   --     result <- freshVar
--   --     encode result expr
--   --     addRotatedBinRep out w result i
--   --   MulN {} -> error "[ panic ] dunno how to compile ROTATE MulN"
--   --   DivN {} -> error "[ panic ] dunno how to compile ROTATE DivN"
--   --   IfN {} -> error "[ panic ] dunno how to compile ROTATE IfN"
--   --   RoLN {} -> error "[ panic ] dunno how to compile ROTATE RoLN"
--   -- ExprU x -> case x of
--   ValU w n -> do
--     n' <- rotateField w n
--     encode out (ExprU (ValU w n'))
--   VarU w var -> addRotatedBinRep out w var i
--   SubU {} -> error "[ panic ] dunno how to compile ROTATE SubU"
--   AddU w _ _ -> do
--     result <- freshVar
--     encodeExorU result expr
--     addRotatedBinRep out w result i
--   _ -> error "[ panic ] dunno how to compile ROTATE on UInt types"
--   -- Rotate _ n x -> encodeRotate out (i + n) x
--   -- -- NAryOp _ op _ _ _ -> error $ "[ panic ] dunno how to compile ROTATE NAryOp " <> show op
--   where
--     rotateField width n = do
--       let val = toInteger n
--       -- see if we are rotating right (positive) of left (negative)
--       case i `compare` 0 of
--         EQ -> return n -- no rotation
--         -- encode out expr -- no rotation
--         LT -> do
--           let rotateDistance = (-i) `mod` width
--           -- collect the bit values of lower bits that will be rotated to higher bits
--           let lowerBits = [Data.Bits.testBit val j | j <- [0 .. rotateDistance - 1]]
--           -- shift the higher bits left by the rotate distance
--           let higherBits = Data.Bits.shiftR val rotateDistance
--           -- combine the lower bits and the higher bits
--           return $
--             fromInteger $
--               foldl'
--                 (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
--                 higherBits
--                 (zip lowerBits [width - rotateDistance .. width - 1])

--         -- encode out (Val bw (fromInteger rotatedVal))
--         GT -> do
--           let rotateDistance = i `mod` width
--           -- collect the bit values of higher bits that will be rotated to lower bits
--           let higherBits = [Data.Bits.testBit val j | j <- [width - rotateDistance .. width - 1]]
--           -- shift the lower bits right by the rotate distance
--           let lowerBits = Data.Bits.shiftL val rotateDistance `mod` 2 ^ width
--           -- combine the lower bits and the higher bits
--           return $
--             fromInteger $
--               foldl'
--                 (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
--                 lowerBits
--                 (zip higherBits [0 .. rotateDistance - 1])

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars Var n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTermN :: (GaloisField n, Integral n) => ExprN n -> M n (Term n)
toTermN (MulN _ (ValN _ m) (ValN _ n)) = return $ Constant (m * n)
toTermN (MulN _ (VarN _ var) (ValN _ n)) = return $ WithVars var n
toTermN (MulN _ (ValN _ n) (VarN _ var)) = return $ WithVars var n
toTermN (MulN _ (ValN _ n) expr) = do
  out <- freshVar
  encodeExprN out expr
  return $ WithVars out n
toTermN (MulN _ expr (ValN _ n)) = do
  out <- freshVar
  encodeExprN out expr
  return $ WithVars out n
toTermN (ValN _ n) =
  return $ Constant n
toTermN (VarN _ var) =
  return $ WithVars var 1
toTermN expr = do
  out <- freshVar
  encodeExprN out expr
  return $ WithVars out 1

-- | Negate a Term
negateTerm :: Num n => Term n -> Term n
negateTerm (WithVars var c) = WithVars var (negate c)
negateTerm (Constant c) = Constant (negate c)

encodeTerms :: GaloisField n => Var -> Seq (Term n) -> M n ()
encodeTerms out terms =
  let (constant, varsWithCoeffs) = foldl' go (0, []) terms
   in add $ cadd constant $ (out, -1) : varsWithCoeffs
  where
    go :: Num n => (n, [(Var, n)]) -> Term n -> (n, [(Var, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (var, coeff) : pairs)

-- Given a binary function 'f' that knows how to encode '_⊗_'
-- This functions replaces the occurences of '_⊗_' with 'f' in the following manner:
--      E₀ ⊗ E₁ ⊗ ... ⊗ Eₙ
--  =>
--      E₀ `f` (E₁ `f` ... `f` Eₙ)
encodeAndFoldExprs :: (GaloisField n, Integral n) => (Var -> Var -> Var -> M n ()) -> Var -> Expr n -> Expr n -> Seq (Expr n) -> M n ()
encodeAndFoldExprs f out x0 x1 xs = do
  x0' <- wireAsVar x0
  x1' <- wireAsVar x1
  vars <- mapM wireAsVar xs
  go x0' x1' vars
  where
    go x y Empty = f out x y
    go x y (v :<| vs) = do
      out' <- freshVar
      go out' v vs
      f out' x y

-- | If the expression is not already a variable, create a new variable
wireAsVar :: (GaloisField n, Integral n) => Expr n -> M n Var
wireAsVar (ExprB (VarB var)) = return var
wireAsVar (ExprN (VarN _ var)) = return var
wireAsVar (ExprU (VarU _ var)) = return var
wireAsVar expr = do
  out <- freshVar
  encode out expr
  return out

--------------------------------------------------------------------------------

-- | Equalities are encoded with inequalities and inequalities with CNEQ constraints.
--    Constraint 'x != y = out'
--    The encoding is, for some 'm':
--        1. (x - y) * m = out
--        2. (x - y) * (1 - out) = 0
encodeEquality :: (GaloisField n, Integral n) => Bool -> Var -> Var -> Var -> M n ()
encodeEquality isEq out x y = case Poly.buildEither 0 [(x, 1), (y, -1)] of
  Left _ -> do
    -- in this case, the variable x and y happend to be the same
    if isEq
      then encode out (ExprB (ValB 1))
      else encode out (ExprB (ValB 0))
  Right diff -> do
    -- introduce a new variable m
    -- if diff = 0 then m = 0 else m = recip diff
    m <- freshVar

    let notOut = case Poly.buildMaybe 1 (IntMap.fromList [(out, -1)]) of
          Nothing -> error "encodeBinaryOp: NEq: impossible"
          Just p -> p

    if isEq
      then do
        --  1. (x - y) * m = 1 - out
        --  2. (x - y) * out = 0
        add [CMul diff (Poly.singleVar m) (Right notOut)]
        add [CMul diff (Poly.singleVar out) (Left 0)]
      else do
        --  1. (x - y) * m = out
        --  2. (x - y) * (1 - out) = 0
        add [CMul diff (Poly.singleVar m) (Right (Poly.singleVar out))]
        add [CMul diff notOut (Left 0)]

    --  keep track of the relation between (x - y) and m
    add [CNEq (CNEQ (Left x) (Left y) m)]

--------------------------------------------------------------------------------

-- | Encoding addition on UInts with multiple operands: O(1)
--    C = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
encodeUIntAddOrSub :: (GaloisField n, Integral n) => Bool -> Int -> Var -> Var -> Var -> M n ()
encodeUIntAddOrSub isSub width out x y = do
  -- locate the binary representations of the operands
  xBinRepStart <- lookupBinRepIndex width x
  yBinRepStart <- lookupBinRepIndex width y

  let multiplier = 2 ^ width
  -- We can refactor
  --    out = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
  -- into the form of
  --    (2ⁿ * Aₙ₋₁) * (Bₙ₋₁) = (out - A - B)
  add $
    cmul
      [(xBinRepStart + width - 1, multiplier)]
      [(yBinRepStart + width - 1, 1)]
      (0, [(out, 1), (x, -1), (y, if isSub then 1 else -1)])

encodeUIntAdd :: (GaloisField n, Integral n) => Int -> Var -> Var -> Var -> M n ()
encodeUIntAdd = encodeUIntAddOrSub False

encodeUIntSub :: (GaloisField n, Integral n) => Int -> Var -> Var -> Var -> M n ()
encodeUIntSub = encodeUIntAddOrSub True

-- | Encoding addition on UInts with multiple operands: O(2)
--    C + 2ⁿ * Q = A * B
encodeUIntMul :: (GaloisField n, Integral n) => Int -> Var -> Var -> Var -> M n ()
encodeUIntMul width out a b = do
  -- rawProduct = a * b
  rawProduct <- freshVar
  encode rawProduct $ ExprN $ VarN width a * VarN width b
  -- result = rawProduct - 2ⁿ * quotient
  quotient <- freshVar
  add $ cadd 0 [(out, 1), (rawProduct, -1), (quotient, 2 ^ width)]

-- | An universal way of compiling a conditional
encodeIf :: (GaloisField n, Integral n) => Var -> Var -> Var -> Var -> M n ()
encodeIf out p x y = do
  --  out = p * x + (1 - p) * y
  --      =>
  --  (out - x) = (1 - p) * (y - x)
  let polynomial1 = case Poly.buildEither 1 [(p, -1)] of
        Left _ -> error "encode: IfB: impossible"
        Right xs -> xs
  let polynomial2 = case Poly.buildEither 0 [(x, -1), (y, 1)] of
        Left _ -> error "encode: IfB: impossible"
        Right xs -> xs
  let polynomial3 = Poly.buildEither 0 [(x, -1), (out, 1)]
  add [CMul polynomial1 polynomial2 polynomial3]
