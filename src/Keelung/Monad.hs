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

-- internal function for generating one fresh variable
freshVar :: M n ty Var
freshVar = do
  index <- gets envNextVar
  modify (\st -> st {envNextVar = succ index})
  return index

-- internal function for generating many fresh variables
freshVars :: Int -> M n ty IntSet
freshVars n = do
  index <- gets envNextVar
  modify (\st -> st {envNextVar = n + index})
  return $ IntSet.fromDistinctAscList [index .. pred n]

-- internal function for marking one variable as input
markVarAsInput :: Var -> M n ty ()
markVarAsInput = markVarsAsInput . IntSet.singleton

-- internal function for marking many variables as input
markVarsAsInput :: IntSet -> M n ty ()
markVarsAsInput vars =
  modify (\st -> st {envInputVars = vars <> envInputVars st})

-- internal function allocating an array with a set of variables to associate with
allocateArray :: IntSet -> Type -> M n ty Addr
allocateArray vars t = do
  let size = IntSet.size vars

  addr <- gets envNextAddr

  let addrPairs = [(addr, i) | i <- [0 .. pred size]]
  let bindings =
        Map.fromList $
          zip addrPairs $
            map (HeapVar t) $ IntSet.toList vars
  modify
    ( \st ->
        st
          { envNextAddr = succ addr,
            envHeap = bindings <> envHeap st
          }
    )
  return addr

--------------------------------------------------------------------------------

data Env a = Env
  { -- Counter for generating fresh variables
    envNextVar :: Var,
    -- Counter for allocating fresh heap addresses
    envNextAddr :: Addr,
    -- Variables marked as inputs
    envInputVars :: IntSet,
    -- Heap for arrays
    envHeap :: Heap
  }
  deriving (Show)

--------------------------------------------------------------------------------

type Addr = Int

type Var = Int

type Heap = Map (Addr, Int) HeapData

data HeapData
  = HeapArray Type Addr -- here Type denotes the type of elements
  | HeapVar Type Var
  deriving (Show)

--------------------------------------------------------------------------------

data Assignment n = forall ty. Assignment (Variable ty) (Expr n ty)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = show var <> " := " <> show expr

--------------------------------------------------------------------------------

-- | Computation elaboration
elaborate :: Comp n ty -> Either String (Elaborated n ty)
elaborate prog = do
  ((expr, assertions), env) <- runM (Env 0 0 mempty mempty) prog
  return $ Elaborated (envNextVar env) (envInputVars env) expr assertions

-- | The result of elaborating a computation
data Elaborated n ty = Elaborated
  { -- | The number of free variables in the computation
    elabNumOfVars :: Int,
    -- | Variables marked as inputs
    elabInputVars :: IntSet,
    -- | The resulting 'Expr'
    elabTExpr :: Expr n ty,
    -- | Assignements
    elabAssignments :: [Assignment n]
  }
  deriving (Show)

--------------------------------------------------------------------------------

-- Interface for drawing fresh inputs and allocating arrays.
-- Types of `Type` like `Num` and `Arr (Arr Bool)` are all considered "proper"
class Proper ty where
  freshInput :: Comp n ty
  freshInputs :: Int -> Comp n ('Arr ty)

-- internal function for drawing 1 fresh input
freshInput' :: Type -> Comp n ty
freshInput' t = do
  var <- freshVar
  markVarAsInput var
  return $ Var (Variable t var)

freshInputs' :: Type -> Int -> Comp n ('Arr ty)
freshInputs' _ 0 = throwError "input array must have size > 0"
freshInputs' t len = do
  -- draw new variables and mark them as inputs
  vars <- freshVars len
  markVarsAsInput vars

  -- allocate a new array
  addr <- allocateArray vars t

  return $ Val (Array t addr)
