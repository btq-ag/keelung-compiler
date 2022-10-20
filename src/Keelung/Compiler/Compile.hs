{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Monad
import Control.Monad.State (State, evalState, gets, modify)
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
import Keelung.Syntax.VarCounters
import Keelung.Types

--------------------------------------------------------------------------------

-- | Compile an untyped expression to a constraint system
run :: GaloisField n => TypeErased n -> ConstraintSystem n
run (TypeErased untypedExprs counters assertions assignments boolVars) = runM (totalVarSize counters) $ do
  -- we need to encode `untypedExprs` to constriants and wire them to 'outputVars'
  let outputVars = [inputVarSize counters .. inputVarSize counters + outputVarSize counters - 1]
  forM_ (zip outputVars untypedExprs) $ \(var, expr) -> do
    encode var expr

  -- Compile assignments to constraints
  mapM_ encodeAssignment assignments

  -- Compile assertions to constraints
  mapM_ encodeAssertion assertions

  constraints <- gets envConstraints
  return
    ( ConstraintSystem
        constraints
        boolVars
        counters
    )

-- | Encode the constraint 'out = x'.
encodeAssertion :: GaloisField n => Expr n -> M n ()
encodeAssertion expr = do
  out <- freshVar
  encode out expr
  add $ cadd 1 [(out, -1)] -- 1 = expr

-- | Encode the constraint 'out = expr'.
encodeAssignment :: GaloisField n => Assignment n -> M n ()
encodeAssignment (Assignment var expr) = encode var expr

--------------------------------------------------------------------------------

-- | Monad for compilation
data Env n = Env
  { envConstraints :: Set (Constraint n),
    envNextVar :: Var
  }

type M n = State (Env n)

runM :: Var -> M n a -> a
runM allVarSize program = evalState program (Env Set.empty (allVarSize + 1))

add :: GaloisField n => [Constraint n] -> M n ()
add cs =
  modify (\env -> env {envConstraints = Set.union (Set.fromList cs) (envConstraints env)})

freshVar :: M n Var
freshVar = do
  next <- gets envNextVar
  modify (\st -> st {envNextVar = next + 1})
  return next

----------------------------------------------------------------

encode :: GaloisField n => Var -> Expr n -> M n ()
encode out expr = case expr of
  Val val -> add $ cadd val [(out, -1)] -- out = val
  Var var -> add $ cadd 0 [(out, 1), (var, -1)] -- out = var
  VarBit {} -> error "dunno how to encode VarBit"
  NAryOp op x y rest ->
    case op of
      Add -> do
        terms <- mapM toTerm (x :<| y :<| rest)
        encodeTerms out terms
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
            encode out (NAryOp NEq 0 (NAryOp Add x y rest) Empty)
      _ -> encodeOtherNAryOp op out x y rest
  BinaryOp Sub x y -> do
    x' <- toTerm x
    y' <- toTerm y
    encodeTerms out (x' :<| negateTerm y' :<| Empty)
  BinaryOp Div x y -> do
    x' <- wireAsVar x
    y' <- wireAsVar y
    add [CMul (Poly.singleVar y') (Poly.singleVar out) (Right $ Poly.singleVar x')]
  If b x y -> do
    b' <- wireAsVar b
    encode out ((Var b' * x) + ((1 - Var b') * y))

--------------------------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars Var n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: GaloisField n => Expr n -> M n (Term n)
toTerm (NAryOp Mul (Var var) (Val n) Empty) =
  return $ WithVars var n
toTerm (NAryOp Mul (Val n) (Var var) Empty) =
  return $ WithVars var n
toTerm (NAryOp Mul expr (Val n) Empty) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (NAryOp Mul (Val n) expr Empty) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (Val n) =
  return $ Constant n
toTerm (Var var) =
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
   in add $ cadd constant $ (out, - 1) : varsWithCoeffs
  where
    go :: Num n => (n, [(Var, n)]) -> Term n -> (n, [(Var, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (var, coeff) : pairs)

encodeOtherNAryOp :: GaloisField n => Op -> Var -> Expr n -> Expr n -> Seq (Expr n) -> M n ()
encodeOtherNAryOp op out x0 x1 xs = do
  x0' <- wireAsVar x0
  x1' <- wireAsVar x1
  vars <- mapM wireAsVar xs
  encodeVars x0' x1' vars
  where
    encodeVars :: GaloisField n => Var -> Var -> Seq Var -> M n ()
    encodeVars x y Empty = encodeBinaryOp op out x y
    encodeVars x y (v :<| vs) = do
      out' <- freshVar
      encodeVars out' v vs
      encodeBinaryOp op out' x y

-- | If the expression is not already a variable, create a new variable
wireAsVar :: GaloisField n => Expr n -> M n Var
wireAsVar (Var var) = return var
wireAsVar expr = do
  out <- freshVar
  encode out expr
  return out

-- | Encode the constraint 'x op y = out'.
encodeBinaryOp :: GaloisField n => Op -> Var -> Var -> Var -> M n ()
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
      Var x * Var y + ((1 - Var x) * (1 - Var y))

--------------------------------------------------------------------------------

-- | Equalities are encoded with inequalities and inequalities with CNEQ constraints.
--    Constraint 'x != y = out'
--    The encoding is, for some 'm':
--        1. (x - y) * m = out
--        2. (x - y) * (1 - out) = 0
encodeEquality :: GaloisField n => Bool -> Var -> Var -> Var -> M n ()
encodeEquality isEq out x y = do
  -- lets build the polynomial for (x - y) first:
  case Poly.buildEither 0 [(x, 1), (y, -1)] of
    Left _ -> do
      -- in this case, the variable x and y happend to be the same
      if isEq
        then encode out (Val 1)
        else encode out (Val 0)
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