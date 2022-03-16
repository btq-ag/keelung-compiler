{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Monad
  ( M,
    Comp,
    elaborate,
    -- creates an assignment
    assign,
    -- declare input vars
    freshInput,
    freshInputs,
    freshInputs2,
    freshInputs3,
    -- declare array of vars
    allocate,
    --
    access,
    access2,
    access3,
    update,
    --
    reduce,
    every,
    everyM,
    loop,
    arrayEq,
    --
    ifThenElse,
  )
where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Keelung.Syntax

--------------------------------------------------------------------------------

-- The monad
type M n = WriterT [Assignment n] (StateT (Env n) (Except String))

type Comp n ty = M n (Expr n ty)

-- how to run the monad
runM :: Env n -> M n a -> Either String ((a, [Assignment n]), Env n)
runM st p = runExcept (runStateT (runWriterT p) st)

-- internal function for generating one fresh variable
freshVar :: M n Int
freshVar = do
  index <- gets envNexVariable
  modify (\st -> st {envNexVariable = succ index})
  return index

-- internal function for generating many fresh variables
freshVars :: Int -> M n IntSet
freshVars n = do
  index <- gets envNexVariable
  modify (\st -> st {envNexVariable = n + index})
  return $ IntSet.fromDistinctAscList [index .. pred n]

-- internal function for marking one variable as input
markVarAsInput :: Int -> M n ()
markVarAsInput = markVarsAsInput . IntSet.singleton

-- internal function for marking many variables as input
markVarsAsInput :: IntSet -> M n ()
markVarsAsInput vars =
  modify (\st -> st {envInpuVariables = vars <> envInpuVariables st})

-- internal function for allocating one fresh address
freshAddr :: M n Int
freshAddr = do
  addr <- gets envNextAddr
  modify (\st -> st {envNextAddr = succ addr})
  return addr

--------------------------------------------------------------------------------

-- | Add assignment
assign :: Ref ('V val) -> Expr n val -> M n ()
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

-- A Heap is an mapping of mappings of variables
type Heap = IntMap (IntMap Int)

--------------------------------------------------------------------------------

data Assignment n = forall ty. Assignment (Ref ('V ty)) (Expr n ty)

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

freshInput :: M n (Ref ('V ty))
freshInput = do
  var <- freshVar
  markVarAsInput var
  return (Variable var)

--------------------------------------------------------------------------------

-- | Array-relad functions
freshInputs :: Int -> M n (Ref ('A ty))
freshInputs 0 = throwError "input array must have size > 0"
freshInputs size = do
  -- draw new variables and mark them as inputs
  vars <- freshVars size
  markVarsAsInput vars
  -- allocate a new array and associate it's content with the new variables
  allocateArray' vars

freshInputs2 :: Int -> Int -> M n (Ref ('A ('A ty)))
freshInputs2 0 _ = throwError "input array must have size > 0"
freshInputs2 sizeM sizeN = do
  -- allocate `sizeM` input arrays each of size `sizeN`
  innerArrays <- replicateM sizeM (freshInputs sizeN)
  -- collect references of these arrays
  vars <- forM innerArrays $ \array -> do
    case array of Array addr -> return addr
  -- and allocate a new array with these references
  allocateArray' $ IntSet.fromList vars

freshInputs3 :: Int -> Int -> Int -> M n (Ref ('A ('A ('A ty))))
freshInputs3 0 _ _ = throwError "input array must have size > 0"
freshInputs3 sizeM sizeN sizeO = do
  -- allocate `sizeM` input arrays each of size `sizeN * sizeO`
  innerArrays <- replicateM sizeM (freshInputs2 sizeN sizeO)
  -- collect references of these arrays
  vars <- forM innerArrays $ \array -> do
    case array of Array addr -> return addr
  -- and allocate a new array with these references
  allocateArray' $ IntSet.fromList vars

writeHeap :: Int -> [(Int, Int)] -> M n ()
writeHeap i array = do
  let bindings = map (\(j, n) -> (i, IntMap.fromList [(j, n)])) array
  modify (\st -> st {envHeap = IntMap.fromList bindings <> envHeap st})

readHeap :: (Int, Int) -> M n Int
readHeap (addr, i) = do
  heap <- gets envHeap
  case IntMap.lookup addr heap of
    Nothing ->
      throwError $
        "unbound addr " ++ show (addr, i)
          ++ " in heap "
          ++ show heap
    Just array -> case IntMap.lookup i array of
      Nothing ->
        throwError $
          "unbound addr " ++ show (addr, i)
            ++ " in heap "
            ++ show heap
      Just n -> return n

-- internal function allocating an array with a set of variables to associate with
allocateArray' :: IntSet -> M n (Ref ('A ty))
allocateArray' vars = do
  let size = IntSet.size vars

  addr <- freshAddr

  let array = zip [0 .. pred size] $ IntSet.toList vars
  -- write that to the heap
  writeHeap addr array

  return $ Array addr

allocate :: Int -> M n (Ref ('A ty))
allocate 0 = throwError "array must have size > 0"
allocate size = do
  -- declare new variables
  vars <- freshVars size
  -- allocate a new array and associate it's content with the new variables
  allocateArray' vars

-- 1-d array access
access :: Ref ('A ('V ty)) -> Int -> M n (Ref ('V ty))
access (Array addr) i = Variable <$> readHeap (addr, i)

access2 :: Ref ('A ('A ('V ty))) -> (Int, Int) -> M n (Ref ('V ty))
access2 addr (i, j) = do
  array <- accessArr addr i
  access array j

access3 :: Ref ('A ('A ('A ('V ty)))) -> (Int, Int, Int) -> M n (Ref ('V ty))
access3 addr (i, j, k) = do
  addr' <- accessArr addr i
  array <- accessArr addr' j
  access array k

accessArr :: Ref ('A ('A ty)) -> Int -> M n (Ref ('A ty))
accessArr (Array addr) i = Array <$> readHeap (addr, i)

-- | Update array 'addr' at position 'i' to expression 'expr'
update :: Ref ('A ('V ty)) -> Int -> Expr n ty -> M n ()
update (Array addr) i (Var (Variable n)) = writeHeap addr [(i, n)]
update (Array addr) i expr = do
  ref <- freshVar
  writeHeap addr [(i, ref)]
  assign (Variable ref) expr

--------------------------------------------------------------------------------

reduce :: Foldable t => Expr n ty -> t a -> (Expr n ty -> a -> Comp n ty) -> Comp n ty
reduce a xs f = foldM f a xs

every :: Foldable t => (a -> Expr n 'Bool) -> t a -> Comp n 'Bool
every f xs = reduce true xs $ \accum x -> return (accum `And` f x)

everyM :: Foldable t => t a -> (a -> Comp n 'Bool) -> Comp n 'Bool
everyM xs f =
  foldM
    ( \accum x -> do
        result <- f x
        return (accum `And` result)
    )
    true
    xs

loop :: Foldable t => t a -> (a -> M n b) -> M n ()
loop = forM_

arrayEq :: Int -> Ref ('A ('V 'Num)) -> Ref ('A ('V 'Num)) -> Comp n 'Bool
arrayEq len xs ys = everyM [0 .. len - 1] $ \i -> do
  a <- access xs i
  b <- access ys i
  return (Var a `Eq` Var b)

--------------------------------------------------------------------------------

ifThenElse :: Expr n 'Bool -> Comp n ty -> Comp n ty -> Comp n ty
ifThenElse p x y = IfThenElse p <$> x <*> y
