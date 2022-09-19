{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compiler.Compile (run) where

import Control.Monad (forM)
import Control.Monad.State (State, evalState, gets, modify)
import Data.Field.Galois (GaloisField)
import Data.Foldable (Foldable (foldl'))
import qualified Data.IntSet as IntSet
import Data.Sequence (Seq (..))
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Compiler.Constraint
import Keelung.Compiler.Syntax.Untyped
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Types (Var)

----------------------------------------------------------------

----------------------------------------------------------------

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
  BinOp op operands -> case op of
    Add -> do
      terms <- {-# SCC "mapMtoTerm" #-} mapM toTerm operands
      {-# SCC "encodeTerms" #-} encodeTerms out terms
    Sub -> do
      terms <- mapM toTerm operands
      encodeTerms out (negateTailTerms terms)
    _ -> encodeOtherBinOp op out operands
  If b x y -> encode out e -- out = b * x + (1-b) * y
    where
      e =
        BinOp
          Add
          ( Seq.fromList
              [ BinOp Mul (Seq.fromList [b, x]),
                BinOp Mul (Seq.fromList [BinOp Sub (Seq.fromList [Val 1, b]), y])
              ]
          )

encodeAssignment :: GaloisField n => Assignment n -> M n ()
encodeAssignment (Assignment var expr) = encode var expr

----------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars Var n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: GaloisField n => Expr n -> M n (Term n)
toTerm (BinOp Mul (Var var :<| Val n :<| Empty)) =
  return $ WithVars var n
toTerm (BinOp Mul (Val n :<| Var var :<| Empty)) =
  return $ WithVars var n
toTerm (BinOp Mul (expr :<| Val n :<| Empty)) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (BinOp Mul (Val n :<| expr :<| Empty)) = do
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

negateTailTerms :: Num n => Seq (Term n) -> Seq (Term n)
negateTailTerms Empty = Empty
negateTailTerms (x :<| xs) = x :<| fmap negateConstant xs -- don't negate the first element
  where
    negateConstant (WithVars var c) = WithVars var (negate c)
    negateConstant (Constant c) = Constant (negate c)

encodeTerms :: GaloisField n => Var -> Seq (Term n) -> M n ()
encodeTerms out terms =
  let (constant, varsWithCoeffs) = foldl' go (0, []) terms
   in add $ cadd constant $ (out, - 1) : varsWithCoeffs
  where
    go :: Num n => (n, [(Var, n)]) -> Term n -> (n, [(Var, n)])
    go (constant, pairs) (Constant n) = (constant + n, pairs)
    go (constant, pairs) (WithVars var coeff) = (constant, (var, coeff) : pairs)

encodeOtherBinOp :: GaloisField n => Op -> Var -> Seq (Expr n) -> M n ()
encodeOtherBinOp op out exprs = do
  vars <- mapM wireAsVar exprs
  encodeVars vars
  where
    wireAsVar :: GaloisField n => Expr n -> M n Var
    wireAsVar (Var var) = return var
    wireAsVar expr = do
      out' <- freshVar
      encode out' expr
      return out'

    encodeVars :: GaloisField n => Seq Var -> M n ()
    encodeVars vars = case vars of
      Empty -> return ()
      _ :<| Empty -> return ()
      x :<| y :<| Empty -> encodeBinaryOp op out x y
      x :<| y :<| xs -> do
        out' <- freshVar
        encodeVars (out' :<| xs)
        encodeBinaryOp op out' x y

-- | Encode the constraint 'x op y = out'.
encodeBinaryOp :: GaloisField n => Op -> Var -> Var -> Var -> M n ()
encodeBinaryOp op out x y = case op of
  Add -> add $ cadd 0 [(x, 1), (y, 1), (out, -1)]
  Sub -> add $ cadd 0 [(x, 1), (y, negate 1), (out, negate 1)]
  Mul -> add [CMul2 (Poly.singleVar x) (Poly.singleVar y) (Right $ Poly.singleVar out)]
  Div -> add [CMul2 (Poly.singleVar y) (Poly.singleVar out) (Right $ Poly.singleVar x)]
  And -> encodeBinaryOp Mul out x y
  Or -> do
    -- Constraint 'x \/ y = out'.
    -- The encoding is: x+y - out = x*y; assumes x and y are boolean.
    xy <- freshVar
    encode xy (Var x * Var y)
    encode xy (Var x + Var y - Var out)
  Xor -> add [CXor x y out]
  -- -- Constraint 'x xor y = out'.
  -- -- The encoding is: x+y - out = 2(x*y); assumes x and y are boolean.
  -- xy <- freshVar
  -- encodeBinaryOp Mul xy x y
  -- add $
  --   cadd
  --     0
  --     [ (x, 1),
  --       (y, 1),
  --       (out, - 1),
  --       (xy, -2)
  --     ]
  NEq -> do
    -- Constraint 'x != y = out'
    -- The encoding is, for some 'm':
    --  1. (x - y) * m = out
    --  2. (x - y) * (1 - out) = 0

    -- diff = (x - y)
    diff <- freshVar
    encode diff (Var x - Var y)

    -- introduce a new variable m
    -- if diff = 0 then m = 0 else m = recip diff
    m <- freshVar
    encode out (Var diff * Var m)
    add [CNQZ diff m]

    -- notOut = 1 - out
    notOut <- freshVar
    encode notOut (1 - Var out)
    add [CMul2 (Poly.singleVar diff) (Poly.singleVar notOut) (Left 0)]
  Eq -> do
    -- Constraint 'x == y = out'.
    -- The encoding is: out = 1 - (x-y != 0).
    result <- freshVar
    encodeBinaryOp NEq result x y
    encode out (BinOp Sub (1 :<| Var result :<| Empty))
  BEq -> do
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    -- The encoding is: x*y + (1-x)*(1-y) = out.
    encode out $
      Var x * Var y + ((1 - Var x) * (1 - Var y))

-- | Ensure that boolean variables have constraint 'b^2 = b'
-- convertBooleanVars :: GaloisField n => IntSet -> [Constraint n]
-- convertBooleanVars booleanInputVars =
--   map (\b -> CMul2 (Poly.singleVar b) (Poly.singleVar b) (Right $ Poly.singleVar b)) $
--     IntSet.toList booleanInputVars

-- | Encode the constraint 'x = out'.
encodeAssertion :: GaloisField n => Expr n -> M n ()
encodeAssertion expr = do
  out <- freshVar
  encode out expr
  add $ cadd 1 [(out, -1)] -- 1 = expr

-- | Compile an untyped expression to a constraint system
run :: GaloisField n => TypeErased n -> ConstraintSystem n
run (TypeErased untypedExprs assertions assignments allVarSize inputVarSize _outputVarSize boolInputVars) = runM allVarSize $ do
  -- we need to encode `untypedExprs` to constriants and wire them to 'outputVars'
  outputVars <- forM untypedExprs $ \expr -> do
    var <- freshVar
    encode var expr
    return var

  -- Compile assignments to constraints
  mapM_ encodeAssignment assignments

  -- Compile assertions to constraints
  mapM_ encodeAssertion assertions

  constraints <- gets envConstraints
  let vars = varsInConstraints constraints
  return
    ( ConstraintSystem
        constraints
        boolInputVars
        vars
        inputVarSize
        (IntSet.fromList outputVars)
    )
