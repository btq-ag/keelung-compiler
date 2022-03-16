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
freshAddr :: M n Addr
freshAddr = do
  addr <- gets envNextAddr
  modify (\st -> st {envNextAddr = succ addr})
  return addr

writeHeap :: [((Addr, Int), HeapData)] -> M n ()
writeHeap bindings = modify (\st -> st {envHeap = Map.fromList bindings <> envHeap st})

-- readHeap :: (Addr, Int) -> RefM n ty
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
  = HeapArr Ref Addr -- here Type denotes the type of elements
  | HeapVar Type Int
  deriving (Show)

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

-- --------------------------------------------------------------------------------

-- -- | Array-relad functions

-- helper of `freshInputs`
freshInputs' :: Type -> Int -> RefM n ('A ty)
freshInputs' _ 0 = throwError "input array must have size > 0"
freshInputs' t len = do
  -- draw new variables and mark them as inputs
  vars <- freshVars len
  markVarsAsInput vars

  -- allocate a new array
  addr <- allocateArray vars t

  return $ Array addr

-- inrnal function allocating an array with a set of variables to associa with
allocateArray :: IntSet -> Type -> M n Addr
allocateArray vars t = do
  let size = IntSet.size vars

  addr <- freshAddr

  let addrPairs = [(addr, i) | i <- [0 .. pred size]]
  let bindings =
        zip addrPairs $
          map (HeapVar t) $ IntSet.toList vars

  -- write that to the heap
  writeHeap bindings

  return addr

-- -- read from array
-- access :: Expr n ('Arr ty) -> Int -> Comp n ty
-- access (Val (Array _ addr)) i = readHeap (addr, i)
-- access (Var _) _ = throwError "cannot access variable of array"

-- access2 :: Expr n ('Arr ('Arr ty)) -> (Int, Int) -> Comp n ty
-- access2 a (i, j) = do
--   a' <- access a i
--   access a' j

-- access3 :: Expr n ('Arr ('Arr ('Arr ty))) -> (Int, Int, Int) -> Comp n ty
-- access3 a (i, j, k) = do
--   a' <- access2 a (i, j)
--   access a' k

-- -- | Update array 'a' at position 'i' to expression 'e'. We special-case
-- -- variable and location expressions, because they're representable untyped
-- -- in the object map.
-- update :: Show f => Expr f ('Arr ty) -> Int -> Expr f ty -> M n ()
-- -- The following specialization (to variable expressions) is an
-- -- optimization: we avoid introducing a fresh variable.
-- update (Val (Array _ l)) i (Var (Variable t x)) =
--   writeHeap [((l, i), HeapVar t x)]
-- -- The following specialization (to location values) is necessary to
-- -- satisfy [INVARIANT]: All expressions of compound types (sums,
-- -- products, arrays, ...) have the form (Val (Array l)), for
-- -- some location l.
-- update (Val (Array _ l)) i (Val (Array t l')) =
--   writeHeap [((l, i), HeapRef t l')]
-- -- Default:
-- update (Val (Array t l)) i e = do
--   x <- freshVar
--   writeHeap [((l, i), HeapVar t x)]
--   assign (Variable t x) e
-- -- Err: expression does not satisfy [INVARIANT].
-- update e1 _ _ = throwError ("expecd " ++ show e1 ++ " a loc")

-- --------------------------------------------------------------------------------

-- reduce :: Expr n ty -> [a] -> (Expr n ty -> a -> Comp n ty) -> Comp n ty
-- reduce a xs f = foldM f a xs

-- everyM :: (Foldable t, Monad m) => t a -> (a -> m (Expr n 'Bool)) -> m (Expr n 'Bool)
-- everyM xs f =
--   foldM
--     ( \accum x -> do
--         result <- f x
--         return (accum `And` result)
--     )
--     true
--     xs
