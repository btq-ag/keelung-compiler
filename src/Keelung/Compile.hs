{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Keelung.Compile (compile) where

import Control.Monad.State (State, evalState, gets, modify)
import Data.Field.Galois (GaloisField)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Keelung.Constraint
import qualified Keelung.Constraint.CoeffMap as CoeffMap
import Keelung.Syntax.Common (Var)
import Keelung.Syntax.Untyped

----------------------------------------------------------------

-- | Monad for compilation
data Env n = Env
  { envConstraints :: Set (Constraint n),
    envNextVar :: Var
  }

type M n = State (Env n)

runM :: Var -> M n a -> a
runM outVar program = evalState program (Env Set.empty (outVar + 1))

addConstraint :: Ord n => Constraint n -> M n ()
addConstraint c =
  modify (\env -> env {envConstraints = Set.insert c $ envConstraints env})

freshVar :: M n Var
freshVar = do
  next <- gets envNextVar
  modify (\st -> st {envNextVar = next + 1})
  return next

----------------------------------------------------------------

-- | Helper for adding CAdd constraint
cadd :: GaloisField n => n -> [(Var, n)] -> M n ()
cadd !c !xs = addConstraint $ CAdd c (CoeffMap.fromList xs)

-- | Helper for adding CMul constraint
cmult :: GaloisField n => (n, Var) -> (n, Var) -> (n, Maybe Var) -> M n ()
cmult (a, x) (b, y) (c, z) = addConstraint $ CMul (a, x) (b, y) (c, z)

-- | Helper for adding CMul constraint
cnqz :: GaloisField n => Var -> Var -> M n ()
cnqz x m = addConstraint $ CNQZ x m

----------------------------------------------------------------

-- class Encode n a where
--   encode :: Var -> a -> M n ()

encode :: GaloisField n => Var -> Expr n -> M n ()
encode out expr = case expr of
  Val val -> cadd val [(out, -1)] -- out = val
  Var var -> cadd 0 [(out, 1), (var, -1)] -- out = var
  BinOp op operands -> case op of
    Add -> do
      terms <- mapM toTerm operands
      encodeTerms out terms
    Sub -> do
      terms <- mapM toTerm operands
      encodeTerms out (negateTailTerms terms)
    _ -> encodeOtherBinOp op out operands
  IfThenElse b x y -> encode out e -- out = b * x + (1-b) * y
    where
      e =
        BinOp
          Add
          [ BinOp Mul [b, x],
            BinOp Mul [BinOp Sub [Val 1, b], y]
          ]

encodeAssignment :: GaloisField n => Assignment n -> M n ()
encodeAssignment (Assignment var expr) = encode var expr

----------------------------------------------------------------

data Term n
  = Constant n -- c
  | WithVars Var n -- cx

-- Avoid having to introduce new multiplication gates
-- for multiplication by constant scalars.
toTerm :: GaloisField n => Expr n -> M n (Term n)
toTerm (BinOp Mul [Var var, Val n]) =
  return $ WithVars var n
toTerm (BinOp Mul [Val n, Var var]) =
  return $ WithVars var n
toTerm (BinOp Mul [expr, Val n]) = do
  out <- freshVar
  encode out expr
  return $ WithVars out n
toTerm (BinOp Mul [Val n, expr]) = do
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

negateTailTerms :: Num n => [Term n] -> [Term n]
negateTailTerms [] = []
negateTailTerms (x : xs) = x : map negateConstant xs
  where
    negateConstant (WithVars var c) = WithVars var (negate c)
    negateConstant (Constant c) = Constant (negate c)

encodeTerms :: GaloisField n => Var -> [Term n] -> M n ()
encodeTerms out terms =
  let c = sum $ map extractConstant terms
   in cadd c $ (out, - 1) : mapMaybe extractVarWithCoeff terms
  where
    extractConstant :: Num n => Term n -> n
    extractConstant (Constant n) = n
    extractConstant (WithVars _ _) = 0

    extractVarWithCoeff :: Term n -> Maybe (Var, n)
    extractVarWithCoeff (Constant _) = Nothing
    extractVarWithCoeff (WithVars var coeff) = Just (var, coeff)

encodeOtherBinOp :: GaloisField n => Op -> Var -> [Expr n] -> M n ()
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

    encodeVars :: GaloisField n => [Var] -> M n ()
    encodeVars vars = case vars of
      [] -> return ()
      [_] -> return ()
      [x, y] -> encodeBinaryOp op out x y
      (x : y : xs) -> do
        out' <- freshVar
        encodeVars (out' : xs)
        encodeBinaryOp op out' x y

-- | Encode the constraint 'x op y = out'.
encodeBinaryOp :: GaloisField n => Op -> Var -> Var -> Var -> M n ()
encodeBinaryOp op out x y = case op of
  Add -> cadd 0 [(x, 1), (y, 1), (out, -1)]
  Sub -> cadd 0 [(x, 1), (y, negate 1), (out, negate 1)]
  Mul -> cmult (1, x) (1, y) (1, Just out)
  Div -> cmult (1, y) (1, out) (1, Just x)
  And -> encodeBinaryOp Mul out x y
  Or -> do
    -- Constraint 'x \/ y = out'.
    -- The encoding is: x+y - out = x*y; assumes x and y are boolean.
    xy <- freshVar
    encode xy (Var x * Var y)
    encode xy (Var x + Var y - Var out)
  Xor -> do
    -- Constraint 'x xor y = out'.
    -- The encoding is: x+y - out = 2(x*y); assumes x and y are boolean.
    xy <- freshVar
    encodeBinaryOp Mul xy x y
    cadd
      0
      [ (x, 1),
        (y, 1),
        (out, - 1),
        (xy, -2)
      ]
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
    cnqz diff m

    -- notOut = 1 - out
    notOut <- freshVar
    encode notOut (1 - Var out)
    cmult (1, diff) (1, notOut) (0, Nothing)
  Eq -> do
    -- Constraint 'x == y = out'.
    -- The encoding is: out = 1 - (x-y != 0).
    result <- freshVar
    encodeBinaryOp NEq result x y
    encode out (BinOp Sub [1, Var result])
  BEq -> do
    -- Constraint 'x == y = out' ASSUMING x, y are boolean.
    -- The encoding is: x*y + (1-x)*(1-y) = out.
    encode out $
      Var x * Var y + ((1 - Var x) * (1 - Var y))

-- | Ensure that boolean variables have constraint 'b^2 = b'
encodeBooleanVars :: GaloisField n => IntSet -> M n ()
encodeBooleanVars booleanInputVars = mapM_ (\b -> encodeBinaryOp Mul b b b) $ IntSet.toList booleanInputVars

-- | Encode the constraint 'x = out'.
encodeAssertion :: GaloisField n => Expr n -> M n ()
encodeAssertion expr = do
  out <- freshVar
  encode out expr
  cadd 1 [(out, -1)] -- 1 = expr

-- | Compile an untyped expression to a constraint system
compile :: (GaloisField n, Bounded n, Integral n) => TypeErased n -> ConstraintSystem n
compile (TypeErased untypedExpr assertions assignments numOfVars inputVars booleanVars) = runM numOfVars $ do
  -- Compile `untypedExpr'` to constraints with output wire 'outputVar'.
  outputVar <- case untypedExpr of
    Nothing -> return Nothing
    Just expr -> do
      encode numOfVars expr
      return $ Just numOfVars

  -- Compile assignments to constraints
  mapM_ encodeAssignment assignments
  -- Compile assertions to constraints
  mapM_ encodeAssertion assertions

  -- ensure that boolean input variables are boolean
  encodeBooleanVars (booleanVars `IntSet.intersection` inputVars)

  constraints <- gets envConstraints
  let vars = varsInConstraints constraints

  return $
    ConstraintSystem
      constraints
      (IntSet.size vars)
      inputVars
      outputVar
