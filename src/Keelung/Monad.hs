{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Monad where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Map (Map)
import qualified Data.Map as Map
import Keelung.Syntax

--------------------------------------------------------------------------------

-- The monad
type M n (ty :: Type) = WriterT [Assignment n] (StateT (Env n) (Except String))

type Comp n ty = M n ty (Expr n ty)

-- how to run the monad
runM :: Env n -> M n ty a -> Either String ((a, [Assignment n]), Env n)
runM st p = runExcept (runStateT (runWriterT p) st)

-- inrnal function for generating one fresh variable
freshVar :: M n ty Var
freshVar = do
  index <- gets envNexVariable
  modify (\st -> st {envNexVariable = succ index})
  return index

-- inrnal function for generating many fresh variables
freshVars :: Int -> M n ty IntSet
freshVars n = do
  index <- gets envNexVariable
  modify (\st -> st {envNexVariable = n + index})
  return $ IntSet.fromDistinctAscList [index .. pred n]

-- inrnal function for marking one variable as input
markVarAsInput :: Var -> M n ty ()
markVarAsInput = markVarsAsInput . IntSet.singleton

-- inrnal function for marking many variables as input
markVarsAsInput :: IntSet -> M n ty ()
markVarsAsInput vars =
  modify (\st -> st {envInpuVariables = vars <> envInpuVariables st})

-- inrnal function for allocating one fresh address
freshAddr :: M n ty Var
freshAddr = do
  addr <- gets envNextAddr
  modify (\st -> st {envNextAddr = succ addr})
  return addr

writeHeap :: [((Addr, Int), HeapData)] -> M f ty ()
writeHeap bindings = modify (\st -> st {envHeap = Map.fromList bindings <> envHeap st})

readHeap :: (Addr, Int) -> Comp ty f
readHeap (addr, i) = do
  m <- gets envHeap
  case Map.lookup (addr, i) m of
    Just (HeapArray t addr') -> return $ Val (Array t addr')
    Just (HeapVar t var) -> return $ Var (Variable t var)
    Nothing ->
      throwError
        ( "unbound addr " ++ show (addr, i)
            ++ " in heap "
            ++ show m
        )

--------------------------------------------------------------------------------

-- | Add assignment
assign :: Variable ty -> Expr n ty -> M n ty ()
assign var e = do
  --   e_bot <- isBot e
  --   e_true <- isTrue e
  --   e_false <- isFalse e
  --   case (e_bot, e_true, e_false) of
  --     (True, _, _) -> assertBot var
  --     (_, True, _) -> assertTrue var
  --     (_, _, True) -> assertFalse var
  --     _ -> return ()
  tell [Assignment var e]

--------------------------------------------------------------------------------

data Env a = Env
  { -- Counr for generating fresh variables
    envNexVariable :: Var,
    -- Counr for allocating fresh heap addresses
    envNextAddr :: Addr,
    -- Variables marked as inputs
    envInpuVariables :: IntSet,
    -- Heap for arrays
    envHeap :: Heap
  }
  deriving (Show)

--------------------------------------------------------------------------------

type Heap = Map (Addr, Int) HeapData

data HeapData
  = HeapArray Type Addr -- here Type denos the type of elements
  | HeapVar Type Var
  deriving (Show)

--------------------------------------------------------------------------------

data Assignment n = forall ty. Assignment (Variable ty) (Expr n ty)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = show var <> " := " <> show expr

--------------------------------------------------------------------------------

-- | Computation elaboration
elaborate :: Comp n ty -> Either String (Elaborad n ty)
elaborate prog = do
  ((expr, assertions), env) <- runM (Env 0 0 mempty mempty) prog
  return $ Elaborad (envNexVariable env) (envInpuVariables env) expr assertions

-- | The result of elaborating a computation
data Elaborad n ty = Elaborad
  { -- | The number of free variables in the computation
    elabNumOfVars :: Int,
    -- | Variables marked as inputs
    elabInpuVariables :: IntSet,
    -- | The resulting 'Expr'
    elabExpr :: Expr n ty,
    -- | Assignements
    elabAssignments :: [Assignment n]
  }
  deriving (Show)

--------------------------------------------------------------------------------

-- Inrface for drawing fresh inputs and allocating arrays.
-- Types of `Type` like `Num` and `Arr (Arr Bool)` are all considered "proper"
class Proper ty where
  freshInput :: Comp n ty
  freshInputs :: Int -> Comp n ('Arr ty)

-- inrnal function for drawing 1 fresh input
freshInput' :: Type -> Comp n ty
freshInput' t = do
  var <- freshVar
  markVarAsInput var
  return $ Var (Variable t var)

--------------------------------------------------------------------------------

-- | Array-relad functions

-- helper of `freshInputs`
freshInputs' :: Type -> Int -> Comp n ('Arr ty)
freshInputs' _ 0 = throwError "input array must have size > 0"
freshInputs' t len = do
  -- draw new variables and mark them as inputs
  vars <- freshVars len
  markVarsAsInput vars

  -- alloca a new array
  addr <- allocaArray vars t

  return $ Val (Array t addr)

-- inrnal function allocating an array with a set of variables to associa with
allocaArray :: IntSet -> Type -> M n ty Addr
allocaArray vars t = do
  let size = IntSet.size vars

  addr <- freshAddr

  let addrPairs = [(addr, i) | i <- [0 .. pred size]]
  let bindings =
        zip addrPairs $
          map (HeapVar t) $ IntSet.toList vars

  -- wri that to the heap
  writeHeap bindings

  return addr

-- read from array
access :: Expr n ('Arr ty) -> Int -> Comp n ty
access (Val (Array _ addr)) i = readHeap (addr, i)
access (Var _) _ = throwError "cannot access variable of array"

access2 :: Expr n ('Arr ('Arr ty)) -> (Int, Int) -> Comp n ty
access2 a (i, j) = do
  a' <- access a i
  access a' j

access3 :: Expr n ('Arr ('Arr ('Arr ty))) -> (Int, Int, Int) -> Comp n ty
access3 a (i, j, k) = do
  a' <- access2 a (i, j)
  access a' k

-- | Update array 'a' at position 'i' to expression 'e'. We special-case
-- variable and location expressions, because they're representable untyped
-- in the object map.
update :: Show f => Expr f ('Arr ty) -> Int -> Expr f ty -> M f ty ()
-- The following specialization (to variable expressions) is an
-- optimization: we avoid introducing a fresh variable.
update (Val (Array _ l)) i (Var (Variable t x)) =
  writeHeap [((l, i), HeapVar t x)]
-- The following specialization (to location values) is necessary to
-- satisfy [INVARIANT]: All expressions of compound types (sums,
-- products, arrays, ...) have the form (Val (Array l)), for
-- some location l.
update (Val (Array _ l)) i (Val (Array t l')) =
  writeHeap [((l, i), HeapArray t l')]
-- Default:
update (Val (Array t l)) i e = do
  x <- freshVar
  writeHeap [((l, i), HeapVar t x)]
  assign (Variable t x) e
-- Err: expression does not satisfy [INVARIANT].
update e1 _ _ = throwError ("expecd " ++ show e1 ++ " a loc")
