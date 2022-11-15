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
import Debug.Trace
import Keelung.Compiler.Constraint
import Keelung.Compiler.Syntax.Untyped
import Keelung.Constraint.Polynomial (Poly)
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))
import qualified Keelung.Constraint.R1C as R1C
import Keelung.Constraint.R1CS (CNEQ (..))
import Keelung.Syntax.BinRep (BinRep (..), BinReps)
import qualified Keelung.Syntax.BinRep as BinRep
import Keelung.Syntax.VarCounters
import Keelung.Types

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: (GaloisField n, Integral n) => TypeErased n -> ConstraintSystem n
run (TypeErased untypedExprs counters assertions assignments numBinReps customBinReps) = runM counters $ do
  -- we need to encode `untypedExprs` to constriants and wire them to 'outputVars'
  forM_ (zip (outputVars counters) untypedExprs) $ \(var, expr) -> do
    encode var expr

  -- Compile assignments to constraints
  mapM_ encodeAssignment assignments

  -- Compile assertions to constraints
  mapM_ encodeAssertion assertions

  constraints <- gets envConstraints

  shiftedBinReps <- gets envShiftedBinReps

  return
    ( ConstraintSystem
        constraints
        numBinReps
        (customBinReps <> shiftedBinReps)
        counters
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

--------------------------------------------------------------------------------

-- | Monad for compilation
data Env n = Env
  { envVarCounters :: VarCounters,
    envConstraints :: Set (Constraint n),
    envShiftedBinReps :: BinReps
  }

type M n = State (Env n)

runM :: GaloisField n => VarCounters -> M n a -> a
runM varCounters program = evalState program (Env varCounters mempty mempty)

add :: GaloisField n => [Constraint n] -> M n ()
add cs =
  modify (\env -> env {envConstraints = Set.union (Set.fromList cs) (envConstraints env)})

addPoly :: GaloisField n => Maybe (Poly n) -> M n ()
addPoly Nothing = return ()
addPoly (Just c) = add [CAdd c]

-- | Adding a raw R1C constraint (TODO: eliminate all usage of this function)
addR1C :: GaloisField n => R1C n -> M n ()
addR1C (R1C.R1C (Left _) (Left _) (Left _)) = return ()
addR1C (R1C.R1C (Left a) (Left b) (Right c)) = addPoly $ Poly.buildMaybe (Poly.constant c - a * b) (Poly.coeffs c)
addR1C (R1C.R1C (Left a) (Right b) (Left c)) = addPoly $ Poly.buildMaybe (a * Poly.constant b - c) (fmap (* a) (Poly.coeffs b))
addR1C (R1C.R1C (Left a) (Right b) (Right c)) = addPoly $ Poly.buildMaybe (a * Poly.constant b - Poly.constant c) (fmap (* a) (Poly.coeffs b) <> fmap negate (Poly.coeffs c))
addR1C (R1C.R1C (Right a) (Left b) (Left c)) = addPoly $ Poly.buildMaybe (Poly.constant a * b - c) (fmap (* b) (Poly.coeffs a))
addR1C (R1C.R1C (Right a) (Left b) (Right c)) = addPoly $ Poly.buildMaybe (Poly.constant a * b - Poly.constant c) (fmap (* b) (Poly.coeffs a) <> fmap negate (Poly.coeffs c))
addR1C (R1C.R1C (Right a) (Right b) c) = add [CMul a b c]

-- | Adds a new view of binary representation of a variable after rotation.
addRotatedBinRep :: Var -> BitWidth -> Var -> Int -> M n ()
addRotatedBinRep out bitWidth var rotate = do
  counters <- gets envVarCounters
  case lookupBinRepStart counters var of
    Nothing -> error $ "[ panic ] Cannot find the start of the binary representation of the variable $" <> show var
    Just index -> addBinRep $ BinRep out (getWidth bitWidth) index rotate

addBinRep :: BinRep -> M n ()
addBinRep binRep = modify (\env -> env {envShiftedBinReps = BinRep.insert binRep (envShiftedBinReps env)})

freshVar :: M n Var
freshVar = do
  n <- gets (totalVarSize . envVarCounters)
  modify' (\ctx -> ctx {envVarCounters = bumpIntermediateVar (envVarCounters ctx)})
  return n

freshBinRep :: Var -> Int -> M n BinRep
freshBinRep var width
  | width < 1 = error $ "[ panic ] Cannot create a binary representation of width " <> show width
  | otherwise = do
    vars <- replicateM width freshVar
    let binRep = BinRep var width (head vars) 0
    addBinRep binRep
    return binRep

----------------------------------------------------------------

encode :: (GaloisField n, Integral n) => Var -> Expr n -> M n ()
encode out expr = case expr of
  Val _ val -> add $ cadd val [(out, -1)] -- out = val
  Var _ var -> add $ cadd 0 [(out, 1), (var, -1)] -- out = var
  Rotate _ n x -> encodeRotate out n x
  NAryOp bw op x y rest ->
    case op of
      Add -> case bw of
        Number _ -> do
          terms <- mapM toTerm (x :<| y :<| rest)
          encodeTerms out terms
        UInt n -> encodeAndFoldExprs (encodeUIntAdd n) out x y rest
        Boolean -> error "[ panic ] Addition on Booleans"
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
          Empty -> do
            -- only 2 operands
            add [COr a b out]
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
            encode out (NAryOp Boolean NEq 0 (NAryOp Boolean Add x y rest) Empty)
      _ -> encodeAndFoldExprs (encodeBinaryOp op) out x y rest
  BinaryOp _ Sub x y -> do
    x' <- toTerm x
    y' <- toTerm y
    encodeTerms out (x' :<| negateTerm y' :<| Empty)
  BinaryOp _ Div x y -> do
    x' <- wireAsVar x
    y' <- wireAsVar y
    add [CMul (Poly.singleVar y') (Poly.singleVar out) (Right $ Poly.singleVar x')]
  If _ b x y -> do
    b' <- wireAsVar b
    encode out ((Var Boolean b' * x) + ((1 - Var Boolean b') * y))
  EmbedR1C _ r1c -> addR1C r1c

--------------------------------------------------------------------------------

-- | Pushes the constructor of Rotate inwards
encodeRotate :: (GaloisField n, Integral n) => Var -> Int -> Expr n -> M n ()
encodeRotate out i expr = case expr of
  Val bw n -> do
    let width = getWidth bw
    let val = toInteger n
    -- see if we are rotating right (positive) of left (negative)
    case i `compare` 0 of
      EQ -> encode out expr -- no rotation
      LT -> do
        let rotateDistance = (-i) `mod` width
        -- collect the bit values of lower bits that will be rotated to higher bits
        let lowerBits = [Data.Bits.testBit val j | j <- [0 .. rotateDistance - 1]]
        -- shift the higher bits left by the rotate distance
        let higherBits = Data.Bits.shiftR val rotateDistance
        -- combine the lower bits and the higher bits
        let rotatedVal =
              foldl'
                (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
                higherBits
                (zip lowerBits [width - rotateDistance .. width - 1])
        encode out (Val bw (fromInteger rotatedVal))
      GT -> do
        let rotateDistance = i `mod` width
        -- collect the bit values of higher bits that will be rotated to lower bits
        let higherBits = [Data.Bits.testBit val j | j <- [width - rotateDistance .. width - 1]]
        -- shift the lower bits right by the rotate distance
        let lowerBits = Data.Bits.shiftL val rotateDistance `mod` (2 ^ width)
        traceShowM (val, rotateDistance, higherBits, lowerBits)
        -- combine the lower bits and the higher bits
        let rotatedVal =
              foldl'
                (\acc (bit, j) -> if bit then Data.Bits.setBit acc j else acc)
                lowerBits
                (zip higherBits [0 .. rotateDistance - 1])
        encode out (Val bw (fromInteger rotatedVal))
  Var bw var -> addRotatedBinRep out bw var i
  Rotate _ n x -> encodeRotate out (i + n) x
  BinaryOp {} -> error "[ panic ] dunno how to compile ROTATE BinaryOp"
  NAryOp {} -> error "[ panic ] dunno how to compile ROTATE NAryOp "
  If {} -> error "[ panic ] dunno how to compile ROTATE If"
  EmbedR1C {} -> error "[ panic ] dunno how to compile ROTATE EmbedR1C"

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars Var n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: (GaloisField n, Integral n) => Expr n -> M n (Term n)
toTerm (NAryOp _ Mul (Var _ var) (Val _ n) Empty) =
  return $ WithVars var n
toTerm (NAryOp _ Mul (Val _ n) (Var _ var) Empty) =
  return $ WithVars var n
toTerm (NAryOp _ Mul expr (Val _ n) Empty) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (NAryOp _ Mul (Val _ n) expr Empty) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (Val _ n) =
  return $ Constant n
toTerm (Var _ var) =
  return $ WithVars var 1
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
wireAsVar (Var _ var) = return var
wireAsVar expr = do
  out <- freshVar
  encode out expr
  return out

-- | Encode the constraint 'x op y = out'.
encodeBinaryOp :: (GaloisField n, Integral n) => Op -> Var -> Var -> Var -> M n ()
encodeBinaryOp op out x y = case op of
  Add -> error "encodeBinaryOp: Add"
  Mul -> add [CMul (Poly.singleVar x) (Poly.singleVar y) (Right $ Poly.singleVar out)]
  And -> error "encodeBinaryOp: And"
  Or -> error "encodeBinaryOp: Or"
  Xor -> add [CXor x y out]
  NEq -> encodeEquality False out x y
  Eq -> encodeEquality True out x y
  BEq -> do
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    -- The encoding is: x*y + (1-x)*(1-y) = out.
    encode out $
      Var Boolean x * Var Boolean y + ((1 - Var Boolean x) * (1 - Var Boolean y))

--------------------------------------------------------------------------------

-- | Equalities are encoded with inequalities and inequalities with CNEQ constraints.
--    Constraint 'x != y = out'
--    The encoding is, for some 'm':
--        1. (x - y) * m = out
--        2. (x - y) * (1 - out) = 0
encodeEquality :: (GaloisField n, Integral n) => Bool -> Var -> Var -> Var -> M n ()
encodeEquality isEq out x y = do
  -- lets build the polynomial for (x - y) first:
  case Poly.buildEither 0 [(x, 1), (y, -1)] of
    Left _ -> do
      -- in this case, the variable x and y happend to be the same
      if isEq
        then encode out (Val Boolean 1)
        else encode out (Val Boolean 0)
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

-- | Encoding addition on UInts with multiple operands: O(2)
--    Sum = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)

-- encodeOtherNAryOp :: (GaloisField n, Integral n) => Op -> Var -> Expr n -> Expr n -> Seq (Expr n) -> M n ()
-- encodeOtherNAryOp op out x0 x1 xs = do
--   x0' <- wireAsVar x0
--   x1' <- wireAsVar x1
--   vars <- mapM wireAsVar xs
--   encodeVars x0' x1' vars
--   where
--     encodeVars :: (GaloisField n, Integral n) => Var -> Var -> Seq Var -> M n ()
--     encodeVars x y Empty = encodeBinaryOp op out x y
--     encodeVars x y (v :<| vs) = do
--       out' <- freshVar
--       encodeVars out' v vs
--       encodeBinaryOp op out' x y
-- encodeUIntAdds :: (GaloisField n, Integral n) => Int -> Var -> Expr n -> Expr n -> Seq (Expr n) -> M n ()
-- encodeUIntAdds width out x y rest = do
--   x' <- wireAsVar x
--   y' <- wireAsVar y
--   rest' <- mapM wireAsVar rest
--   encodeVars x' y' rest'
--   where
--     encodeVars :: (GaloisField n, Integral n) => Var -> Var -> Seq Var -> M n ()
--     encodeVars x y Empty = encodeBinaryOp op out x y
--     encodeVars x y (v :<| vs) = do
--       out' <- freshVar
--       encodeVars out' v vs
--       encodeBinaryOp op out' x y

--   where
encodeUIntAdd :: (GaloisField n, Integral n) => Int -> Var -> Var -> Var -> M n ()
encodeUIntAdd width out x y = traceShow (out, x, y) $ do
  -- allocate a fresh BinRep for the output
  _outBinRep <- freshBinRep out width

  -- locate the binary representations of the operands
  counters <- gets envVarCounters
  let locateBinRep var = case lookupBinRepStart counters var of
        Nothing -> error $ "[ panic ] encodeUIntAddBinRep: cannot locate binary representation of $" <> show var
        Just index -> index
  let xBinRepStart = locateBinRep x
  let yBinRepStart = locateBinRep y

  let multiplier = 2 ^ width
  -- We can refactor
  --    out = A + B - 2ⁿ * (Aₙ₋₁ * Bₙ₋₁)
  -- into the form of
  --    (2ⁿ * Aₙ₋₁) * (Bₙ₋₁) = (out - A - B)
  let polynomial1 = Poly.buildEither 0 [(xBinRepStart + width - 1, multiplier)]
  let polynomial2 = Poly.singleVar (yBinRepStart + width - 1)
  let polynomial3 = Poly.buildEither 0 [(out, 1), (x, -1), (y, -1)]

  numBitWidth <- gets (Number . getNumBitWidth . envVarCounters)
  encode out $ EmbedR1C numBitWidth $ R1C polynomial1 (Right polynomial2) polynomial3

