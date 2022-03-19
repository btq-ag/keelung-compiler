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
import Keelung.Monad (Elaborated (Elaborated))
import Keelung.Syntax.Common
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

----------------------------------------------------------------

-- class Encode n a where
--   encode :: Var -> a -> M n ()

-- instance GaloisField n => Encode n (Expr n) where
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

-- | Encode the constraint 'x op y = z'.
encodeBinaryOp :: GaloisField n => Op -> Var -> Var -> Var -> M n ()
encodeBinaryOp op out x y = case op of
  Add -> cadd 0 [(x, 1), (y, 1), (out, -1)]
  Sub -> cadd 0 [(x, 1), (y, negate 1), (out, negate 1)]
  Mul -> cmult (1, x) (1, y) (1, Just out)
  Div -> cmult (1, y) (1, out) (1, Just x)
  And -> encodeBinaryOp Mul out x y
  Or -> do
    -- Constraint 'x \/ y = z'.
    -- The encoding is: x+y - z = x*y; assumes x and y are boolean.
    xy <- freshVar
    encode xy (Var x * Var y)
    encode
      xy
      (Var x + Var y - Var out)
  Xor -> do
    -- Constraint 'x xor y = z'.
    -- The encoding is: x+y - z = 2(x*y); assumes x and y are boolean.
    xy <- freshVar
    encodeBinaryOp Mul xy x y
    cadd
      0
      [ (x, 1),
        (y, 1),
        (out, - 1),
        (xy, -2)
      ]
  Eq -> do
    -- Constraint 'x == y = z'.
    -- The encoding is: z = (x-y == 0).
    encode out (BinOp Eq [Var x - Var y, 0])
  BEq -> do
    -- Constraint 'x == y = z' ASSUMING x, y are boolean.
    -- The encoding is: x*y + (1-x)*(1-y) = z.
    encode out $
      Var x * Var y + ((1 - Var x) * (1 - Var y))

-- | Ensure that boolean variables have constraint 'b^2 = b'
encodeBooleanVars :: GaloisField n => IntSet -> M n ()
encodeBooleanVars booleanInputVars = mapM_ (\b -> encodeBinaryOp Mul b b b) $ IntSet.toList booleanInputVars

-- | Return the list of variables occurring in constraints 'cs'.
varsInConstraint :: Constraint a -> IntSet
varsInConstraint (CAdd _ m) = CoeffMap.keysSet m
varsInConstraint (CMul (_, x) (_, y) (_, Nothing)) = IntSet.fromList [x, y]
varsInConstraint (CMul (_, x) (_, y) (_, Just z)) = IntSet.fromList [x, y, z]

-- | Compile an expression to a constraint system.  Takes as input the
-- expression, the expression's input variables, and the name of the
-- output variable.
compile ::
  (GaloisField n, Erase ty) =>
  Elaborated n ty ->
  ConstraintSystem n
compile (Elaborated outputVar inputVars typedExpr numAssignments boolAssignments) = runM outputVar $ do
  let (untypedExpr, booleanVarsInExpr) = eraseType typedExpr
  let (numAssignments', booleanVarsInNumAssignments) = eraseTypeFromAssignments numAssignments
  let (boolAssignments', booleanVarsInBoolAssignments) = eraseTypeFromAssignments boolAssignments

  -- optimization: constant propogation
  -- e = propogateConstant e0

  -- Compile `untypedExpr` to constraints with output wire 'outputVar'.
  encode outputVar untypedExpr
  -- Compile assignments to constraints with output wire 'outputVar'.
  let assignments = numAssignments' <> boolAssignments'
  mapM_ encodeAssignment assignments

  -- ensure that boolean variables are boolean
  let booleanVarsInProgram = booleanVarsInExpr <> booleanVarsInNumAssignments <> booleanVarsInBoolAssignments
  encodeBooleanVars (booleanVarsInProgram `IntSet.intersection` inputVars)

  constraints <- gets envConstraints

  --
  let vars = IntSet.unions $ map varsInConstraint $ Set.toList constraints

  return $
    ConstraintSystem
      constraints
      (IntSet.size vars)
      inputVars
      (IntSet.singleton outputVar)
