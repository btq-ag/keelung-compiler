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
type M n = WriterT [Assignment n] (StateT (Env n) (Except String))

type Comp n ty = M n (Expr n ty)

type RefM n ty = M n (Reference ty)

-- how to run the monad
runM :: Env n -> M n a -> Either String ((a, [Assignment n]), Env n)
runM st p = runExcept (runStateT (runWriterT p) st)

-- inrnal function for generating one fresh variable
freshVar :: M n Int
freshVar = do
  index <- gets envNexVariable
  modify (\st -> st {envNexVariable = succ index})
  return index

-- inrnal function for generating many fresh variables
freshVars :: Int -> M n IntSet
freshVars n = do
  index <- gets envNexVariable
  modify (\st -> st {envNexVariable = n + index})
  return $ IntSet.fromDistinctAscList [index .. pred n]

-- inrnal function for marking one variable as input
markVarAsInput :: Int -> M n ()
markVarAsInput = markVarsAsInput . IntSet.singleton

-- inrnal function for marking many variables as input
markVarsAsInput :: IntSet -> M n ()
markVarsAsInput vars =
  modify (\st -> st {envInpuVariables = vars <> envInpuVariables st})

-- inrnal function for allocating one fresh address
freshAddr :: M n Int
freshAddr = do
  addr <- gets envNextAddr
  modify (\st -> st {envNextAddr = succ addr})
  return addr

-- readHeap ((AddrOfAddr n), i) = _wd

-- readHeap (addr, i) = do
--   m <- gets envHeap
--   case Map.lookup (addr, i) m of
--     Just (HeapArr t addr') -> return $ Array addr'
--     Just (HeapVar t var) -> return _
--     Nothing ->
--       throwError
--         ( "unbound addr " ++ show (addr, i)
--             ++ " in heap "
--             ++ show m
--         )

--------------------------------------------------------------------------------

-- | Add assignment
assign :: Reference ('V val) -> Expr n val -> M n ()
assign var e = tell [Assignment var e]

--------------------------------------------------------------------------------

data Env a = Env
  { -- Counr for generating fresh variables
    envNexVariable :: Int,
    -- Counr for allocating fresh heap addresses
    envNextAddr :: Int,
    -- Variables marked as inputs
    envInpuVariables :: IntSet,
    -- Heap for arrays
    envHeap :: Heap
  }
  deriving (Show)

--------------------------------------------------------------------------------

type Heap = Map (Int, Int) Int

-- data HeapData :: * where
--   HeapVar :: Int -> HeapData
--   HeapArr :: Addr -> HeapData

-- instance Show HeapData where
--   show (HeapArr n) = "HeapArr" <> show n
--   show (HeapVar n) = "HeapVar" <> show n

-- data HeapData
--   = HeapArr Ref Addr -- here Type denotes the type of elements
--   | HeapVar Type Int
--   deriving (Show)

--------------------------------------------------------------------------------

data Assignment n = forall ty. Assignment (Reference ('V ty)) (Expr n ty)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = show var <> " := " <> show expr

--------------------------------------------------------------------------------

-- | Computation elaboration
elaborate :: Comp n ty -> Either String (Elaborated n ty)
elaborate prog = do
  ((expr, assertions), env) <- runM (Env 0 0 mempty mempty) prog
  return $ Elaborated (envNexVariable env) (envInpuVariables env) expr assertions

-- | The result of elaborating a computation
data Elaborated n ty = Elaborated
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
-- class Proper val where
--   freshInput :: M n (Reference ('V val))

-- -- freshInputs :: Int -> Comp n ('Ref ('Arr ('Var val)))

-- instance Proper 'Num where
--   freshInput = freshInput'

-- -- freshInputs = freshInputs' Num

-- instance Proper 'Bool where
--   freshInput = freshInput'

-- freshInputs = freshInputs' Bool

-- inrnal function for drawing 1 fresh input
freshInput :: M n (Reference ('V ty))
freshInput = do
  var <- freshVar
  markVarAsInput var
  return (Variable var)

--------------------------------------------------------------------------------

-- | Array-relad functions

-- helper of `freshInputs`
freshInputs' :: Type -> Int -> RefM n ('A ty)
freshInputs' _ 0 = throwError "input array must have size > 0"
freshInputs' _ len = do
  -- draw new variables and mark them as inputs
  vars <- freshVars len
  markVarsAsInput vars

  -- allocate a new array
  addr <- allocateArray vars

  return $ Array addr

writeHeap :: [((Int, Int), Int)] -> M n ()
writeHeap bindings = modify (\st -> st {envHeap = Map.fromList bindings <> envHeap st})

readHeap :: (Int, Int) -> M n Int
readHeap (addr, i) = do
  heap <- gets envHeap
  case Map.lookup (addr, i) heap of
    Nothing ->
      throwError $
        "unbound addr " ++ show (addr, i)
          ++ " in heap "
          ++ show heap
    Just n -> return n

-- inrnal function allocating an array with a set of variables to associate with
allocateArray :: IntSet -> M n Addr
allocateArray vars = do
  let size = IntSet.size vars

  addr <- freshAddr

  let addrPairs = [(addr, i) | i <- [0 .. pred size]]
  let bindings =
        zip addrPairs $ IntSet.toList vars

  -- write that to the heap
  writeHeap bindings

  return addr

-- 1-d array access
access :: Reference ('A ('V ty)) -> Int -> M n (Reference ('V ty))
access (Array addr) i = Variable <$> readHeap (addr, i)

access2 :: Reference ('A ('A ('V ty))) -> (Int, Int) -> M n (Reference ('V ty))
access2 addr (i, j) = do
  array <- accessArr addr i
  access array j

access3 :: Reference ('A ('A ('A ('V ty)))) -> (Int, Int, Int) -> M n (Reference ('V ty))
access3 addr (i, j, k) = do
  addr' <- accessArr addr i
  array <- accessArr addr' j
  access array k

accessArr :: Reference ('A ('A ty)) -> Int -> M n (Reference ('A ty))
accessArr (Array addr) i = Array <$> readHeap (addr, i)

-- | Update array 'addr' at position 'i' to expression 'expr'
update :: Reference ('A ('V ty)) -> Int -> Expr n ty -> M n ()
update (Array addr) i (Var (Variable n)) = writeHeap [((addr, i), n)]
update (Array addr) i expr = do
  ref <- freshVar
  writeHeap [((addr, i), ref)]
  assign (Variable ref) expr

--------------------------------------------------------------------------------

reduce :: Expr n ty -> [a] -> (Expr n ty -> a -> Comp n ty) -> Comp n ty
reduce a xs f = foldM f a xs

everyM :: (Foldable t, Monad m) => t a -> (a -> m (Expr n 'Bool)) -> m (Expr n 'Bool)
everyM xs f =
  foldM
    ( \accum x -> do
        result <- f x
        return (accum `And` result)
    )
    true
    xs
