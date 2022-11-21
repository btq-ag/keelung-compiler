{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Monad
import Control.Monad.State
import qualified Data.Bits
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
encodeAssignment (Assignment var expr) = encode var expr

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
  VarB var -> add $ cadd 0 [(out, 1), (var, -1)] -- out = var

encodeExprN :: (GaloisField n, Integral n) => Var -> ExprN n -> M n ()
encodeExprN out expr = case expr of
  ValN _ val -> add $ cadd val [(out, -1)] -- out = val
  VarN _ var -> add $ cadd 0 [(out, 1), (var, -1)] -- out = var

encodeExprU :: (GaloisField n, Integral n) => Var -> ExprU n -> M n ()
encodeExprU out expr = case expr of
  ValU _ val -> add $ cadd val [(out, -1)] -- out = val
  VarU _ var -> add $ cadd 0 [(out, 1), (var, -1)] -- out = var

encode :: (GaloisField n, Integral n) => Var -> Expr n -> M n ()
encode out expr = case expr of
  -- values
  ExprB x -> encodeExprB out x
  ExprN x -> encodeExprN out x
  ExprU x -> encodeExprU out x
  -- operators
  Rotate _ n x -> encodeRotate out n x
  NAryOp bw op x y rest ->
    case op of
      AddN -> case bw of
        BWNumber _ -> do
          terms <- mapM toTerm (x :<| y :<| rest)
          encodeTerms out terms
        BWUInt _ -> error "[ panic ] AddN on UInt"
        BWBoolean -> error "[ panic ] Addition on Booleans"
        BWUnit -> error "[ panic ] Addition on Units"
        BWArray _ _ -> error "[ panic ] Addition on Arrays"
      AddU -> case bw of
        BWNumber _ -> error "[ panic ] AddU on Number"
        BWUInt n -> encodeAndFoldExprsBinRep (encodeUIntAdd n) n out x y rest
        BWBoolean -> error "[ panic ] Addition on Booleans"
        BWUnit -> error "[ panic ] Addition on Units"
        BWArray _ _ -> error "[ panic ] Addition on Arrays"
      And -> do
        a <- wireAsVar x
        b <- wireAsVar y
        vars <- mapM wireAsVar rest
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
      Or -> do
        a <- wireAsVar x
        b <- wireAsVar y
        vars <- mapM wireAsVar rest
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
            encode
              out
              ( NAryOp
                  (BWNumber numBitWidth)
                  NEq
                  (ExprN (ValN numBitWidth 0))
                  ( NAryOp
                      (BWNumber numBitWidth)
                      AddN
                      (castToNumber numBitWidth x)
                      (castToNumber numBitWidth y)
                      (fmap (castToNumber numBitWidth) rest)
                  )
                  Empty
              )
      _ -> encodeAndFoldExprs (encodeBinaryOp bw op) out x y rest
  Sub bw x y -> do
    case bw of
      BWNumber _ -> do
        x' <- toTerm x
        y' <- toTerm y
        encodeTerms out (x' :<| negateTerm y' :<| Empty)
      BWUInt n -> encodeAndFoldExprs (encodeUIntSub n) out x y mempty
      BWBoolean -> error "[ panic ] Subtraction on Booleans"
      BWUnit -> error "[ panic ] Addition on Units"
      BWArray _ _ -> error "[ panic ] Addition on Arrays"
  Div _ x y -> do
    x' <- wireAsVar x
    y' <- wireAsVar y
    add [CMul (Poly.singleVar y') (Poly.singleVar out) (Right $ Poly.singleVar x')]
  If _ b x y -> do
    b' <- wireAsVar b
    -- treating these variables like they are Numbers
    numBitWidth <- getNumberBitWidth
    -- out = b * x + (1 - b) * y
    encode out $
      ExprN (VarN numBitWidth b') * castToNumber numBitWidth x
        + (ExprN (ValN numBitWidth 1) - ExprN (VarN numBitWidth b')) * castToNumber numBitWidth y

--------------------------------------------------------------------------------

-- | Pushes the constructor of Rotate inwards
encodeRotate :: (GaloisField n, Integral n) => Var -> Int -> Expr n -> M n ()
encodeRotate out i expr = case expr of
  ExprB x -> encode out (ExprB x)
  ExprN x -> case x of
    ValN w n -> do
      n' <- rotateField w n
      encode out (ExprN (ValN w n'))
    VarN w var -> addRotatedBinRep out w var i
  ExprU x -> case x of
    ValU w n -> do
      n' <- rotateField w n
      encode out (ExprU (ValU w n'))
    VarU w var -> addRotatedBinRep out w var i
  Rotate _ n x -> encodeRotate out (i + n) x
  Sub {} -> error "[ panic ] dunno how to compile ROTATE Sub"
  Div {} -> error "[ panic ] dunno how to compile ROTATE Div"
  NAryOp bw op _ _ _ -> case op of
    AddN -> do
      result <- freshVar
      encode result expr
      addRotatedBinRep out (getWidth bw) result i
    AddU -> do
      result <- freshVar
      encode result expr
      addRotatedBinRep out (getWidth bw) result i
    _ -> error $ "[ panic ] dunno how to compile ROTATE NAryOp " <> show op
  If {} -> error "[ panic ] dunno how to compile ROTATE If"
  where
    -- rotateField :: (GaloisField n, Integral n) => Width -> n -> M n ()
    rotateField width n = do
      let val = toInteger n
      -- see if we are rotating right (positive) of left (negative)
      case i `compare` 0 of
        EQ -> return n -- no rotation
        -- encode out expr -- no rotation
        LT -> do
          let rotateDistance = (-i) `mod` width
          -- collect the bit values of lower bits that will be rotated to higher bits
          let lowerBits = [Data.Bits.testBit val j | j <- [0 .. rotateDistance - 1]]
          -- shift the higher bits left by the rotate distance
          let higherBits = Data.Bits.shiftR val rotateDistance
          -- combine the lower bits and the higher bits
          return $
            fromInteger $
              foldl'
                (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
                higherBits
                (zip lowerBits [width - rotateDistance .. width - 1])

        -- encode out (Val bw (fromInteger rotatedVal))
        GT -> do
          let rotateDistance = i `mod` width
          -- collect the bit values of higher bits that will be rotated to lower bits
          let higherBits = [Data.Bits.testBit val j | j <- [width - rotateDistance .. width - 1]]
          -- shift the lower bits right by the rotate distance
          let lowerBits = Data.Bits.shiftL val rotateDistance `mod` 2 ^ width
          -- combine the lower bits and the higher bits
          return $
            fromInteger $
              foldl'
                (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
                lowerBits
                (zip higherBits [0 .. rotateDistance - 1])

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars Var n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: (GaloisField n, Integral n) => Expr n -> M n (Term n)
toTerm (NAryOp _ Mul (ExprN (VarN _ var)) (ExprN (ValN _ n)) Empty) =
  return $ WithVars var n
toTerm (NAryOp _ Mul (ExprB (VarB _)) (ExprN (ValN _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add Boolean variable with Number value"
toTerm (NAryOp _ Mul (ExprU (VarU _ _)) (ExprN (ValN _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add UInt variable with Number value"
toTerm (NAryOp _ Mul (ExprN (VarN _ _)) (ExprB (ValB _)) Empty) =
  error "[ panic ] toTerm: Trying to add Number variable with Boolean value"
toTerm (NAryOp _ Mul (ExprB (VarB _)) (ExprB (ValB _)) Empty) =
  error "[ panic ] toTerm: Trying to add Boolean variable with Boolean value"
toTerm (NAryOp _ Mul (ExprU (VarU _ _)) (ExprB (ValB _)) Empty) =
  error "[ panic ] toTerm: Trying to add UInt variable with Boolean value"
toTerm (NAryOp _ Mul (ExprN (VarN _ _)) (ExprU (ValU _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add Number variable with UInt value"
toTerm (NAryOp _ Mul (ExprB (VarB _)) (ExprU (ValU _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add Boolean variable with UInt value"
toTerm (NAryOp _ Mul (ExprU (VarU _ var)) (ExprU (ValU _ n)) Empty) =
  return $ WithVars var n
toTerm (NAryOp _ Mul (ExprN (ValN _ n)) (ExprN (VarN _ var)) Empty) =
  return $ WithVars var n
toTerm (NAryOp _ Mul (ExprN (ValN _ _)) (ExprB (VarB _)) Empty) =
  error "[ panic ] toTerm: Trying to add Number value with Boolean variable"
toTerm (NAryOp _ Mul (ExprN (ValN _ _)) (ExprU (VarU _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add Number value with UInt variable"
toTerm (NAryOp _ Mul (ExprB (ValB _)) (ExprN (VarN _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add Boolean value with Number variable"
toTerm (NAryOp _ Mul (ExprB (ValB _)) (ExprB (VarB _)) Empty) =
  error "[ panic ] toTerm: Trying to add Boolean value with Boolean variable"
toTerm (NAryOp _ Mul (ExprB (ValB _)) (ExprU (VarU _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add Boolean value with UInt variable"
toTerm (NAryOp _ Mul (ExprU (ValU _ _)) (ExprN (VarN _ _)) Empty) =
  error "[ panic ] toTerm: Trying to add UInt value with Number variable"
toTerm (NAryOp _ Mul (ExprU (ValU _ _)) (ExprB (VarB _)) Empty) =
  error "[ panic ] toTerm: Trying to add UInt value with Boolean variable"
toTerm (NAryOp _ Mul (ExprU (ValU _ n)) (ExprU (VarU _ var)) Empty) =
  return $ WithVars var n
toTerm (NAryOp _ Mul expr (ExprN (ValN _ n)) Empty) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (NAryOp _ Mul (ExprN (ValN _ n)) expr Empty) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (ExprN (ValN _ n)) =
  return $ Constant n
toTerm (ExprB _) =
  error "[ panic ] toTerm on Boolean expression"
toTerm (ExprN (VarN _ var)) =
  return $ WithVars var 1
toTerm (ExprU (VarU _ var)) =
  return $ WithVars var 1
toTerm (ExprU (ValU _ n)) =
  return $ Constant n
toTerm expr = do
  out <- freshVar
  encode out expr
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

-- | Like 'encodeAndFoldExprs' but allocates a BinRep for the result
encodeAndFoldExprsBinRep :: (GaloisField n, Integral n) => (Var -> Var -> Var -> M n ()) -> Int -> Var -> Expr n -> Expr n -> Seq (Expr n) -> M n ()
encodeAndFoldExprsBinRep f width out x0 x1 xs = do
  x0' <- wireAsVar x0
  x1' <- wireAsVar x1
  vars <- mapM wireAsVar xs
  go x0' x1' vars
  where
    go x y Empty = do
      freshBinRep out width
      f out x y
    go x y (v :<| vs) = do
      out' <- freshVar
      freshBinRep out' width
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

-- | Encode the constraint 'x op y = out'.
encodeBinaryOp :: (GaloisField n, Integral n) => BitWidth -> Op -> Var -> Var -> Var -> M n ()
encodeBinaryOp bw op out x y = case op of
  AddN -> error "encodeBinaryOp: AddN"
  AddU -> error "encodeBinaryOp: AddU"
  Mul -> case bw of
    BWNumber _ -> add [CMul (Poly.singleVar x) (Poly.singleVar y) (Right $ Poly.singleVar out)]
    BWUInt w -> do
      freshBinRep out w
      encodeUIntMul w out x y
    BWBoolean -> add [CMul (Poly.singleVar x) (Poly.singleVar y) (Right $ Poly.singleVar out)]
    BWUnit -> error "[ panic ] Multiplication on Units"
    BWArray _ _ -> error "[ panic ] Addition on Arrays"
  And -> error "encodeBinaryOp: And"
  Or -> error "encodeBinaryOp: Or"
  Xor -> add [CXor x y out]
  NEq -> encodeEquality False out x y
  Eq -> encodeEquality True out x y
  BEq -> do
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    -- The encoding is: x*y + (1-x)*(1-y) = out.
    numBitWidth <- getNumberBitWidth
    encode out $
      ExprN (VarN numBitWidth x)
        * ExprN (VarN numBitWidth y)
        + (ExprN (ValN numBitWidth 1) - ExprN (VarN numBitWidth x))
        * (ExprN (ValN numBitWidth 1) - ExprN (VarN numBitWidth y))

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
  encode rawProduct $ ExprN (VarN width a) * ExprN (VarN width b)
  -- result = rawProduct - 2ⁿ * quotient
  quotient <- freshVar
  add $ cadd 0 [(out, 1), (rawProduct, -1), (quotient, 2 ^ width)]
