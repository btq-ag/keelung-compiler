{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Monad
  ( M,
    Comp,
    Elaborated (..),
    Assignment (..),
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
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Keelung.Syntax
import Keelung.Syntax.Common
import Keelung.Util

--------------------------------------------------------------------------------

-- The monad
type M n =
  WriterT
    [Assignment 'Num n]
    (WriterT [Assignment 'Bool n] (StateT (Env n) (Except String)))

type Comp n ty = M n (Expr ty n)

-- how to run the monad
runM :: Env n -> M n a -> Either String (((a, [Assignment 'Num n]), [Assignment 'Bool n]), Env n)
runM st p = runExcept (runStateT (runWriterT (runWriterT p)) st)

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
  return $ IntSet.fromDistinctAscList [index .. index + n - 1]

-- internal function for marking one variable as input
markVarAsInput :: Var -> M n ()
markVarAsInput = markVarsAsInput . IntSet.singleton

-- internal function for marking many variables as input
markVarsAsInput :: IntSet -> M n ()
markVarsAsInput vars =
  modify (\st -> st {envInpuVariables = vars <> envInpuVariables st})

-- internal function for allocating one fresh address
freshAddr :: M n Addr
freshAddr = do
  addr <- gets envNextAddr
  modify (\st -> st {envNextAddr = succ addr})
  return addr

--------------------------------------------------------------------------------

-- | Add assignment
class Proper ty where
  assign :: Ref ('V ty) -> Expr ty n -> M n ()
  arrayEq :: Int -> Ref ('A ('V ty)) -> Ref ('A ('V ty)) -> Comp n 'Bool

instance Proper 'Num where
  assign var e = tell [Assignment var e]
  arrayEq len xs ys = everyM [0 .. len - 1] $ \i -> do
    a <- access xs i
    b <- access ys i
    return (Var Num a `Eq` Var Num b)

instance Proper 'Bool where
  assign var e = lift $ tell [Assignment var e]
  arrayEq len xs ys = everyM [0 .. len - 1] $ \i -> do
    a <- access xs i
    b <- access ys i
    return (Var Bool a `BEq` Var Bool b)

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

data Assignment ty n = Assignment (Ref ('V ty)) (Expr ty n)

instance Show n => Show (Assignment ty n) where
  show (Assignment var expr) = show var <> " := " <> show expr

instance Functor (Assignment ty) where
  fmap f (Assignment var expr) = Assignment var (fmap f expr)

--------------------------------------------------------------------------------

-- | Computation elaboration
elaborate :: Comp n ty -> Either String (Elaborated n ty)
elaborate prog = do
  (((expr, numAssignments), boolAssignments), env) <- runM (Env 0 0 mempty mempty) prog
  return $ Elaborated (envNexVariable env) (envInpuVariables env) expr numAssignments boolAssignments

-- | The result of elaborating a computation
data Elaborated n ty = Elaborated
  { -- | The number of free variables in the computation
    elabNumOfVars :: Int,
    -- | Variables marked as inputs
    elabInpuVariables :: IntSet,
    -- | The resulting 'Expr'
    elabExpr :: Expr ty n,
    -- | Assignements
    elabNumAssignments :: [Assignment 'Num n],
    elabBoolAssignments :: [Assignment 'Bool n]
  }

instance (Show n, GaloisField n, Bounded n, Integral n) => Show (Elaborated n ty) where
  show (Elaborated n inputs expr numAssignments boolAssignments) =
    "{\n\
    \  number of variables: "
      ++ show n
      ++ "\n\
         \  input variables: "
      ++ show (IntSet.toList inputs)
      ++ "\n\
         \  expression: "
      ++ show (fmap DebugGF expr)
      ++ "\n  num assignments: "
      ++ show (map (fmap DebugGF) numAssignments)
      ++ "\n  bool assignments: "
      ++ show (map (fmap DebugGF) boolAssignments)
      ++ "\n\
         \}"

--------------------------------------------------------------------------------

freshInput :: M n (Ref ('V ty))
freshInput = do
  var <- freshVar
  markVarAsInput var
  return $ Variable var

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

writeHeap :: Addr -> [(Int, Var)] -> M n ()
writeHeap addr array = do
  let bindings = IntMap.fromList array
  heap <- gets envHeap
  let heap' = IntMap.insertWith (<>) addr bindings heap
  modify (\st -> st {envHeap = heap'})

readHeap :: (Addr, Int) -> M n Int
readHeap (addr, i) = do
  heap <- gets envHeap
  case IntMap.lookup addr heap of
    Nothing ->
      throwError $
        "unbound array " ++ show (addr, i)
          ++ " in heap "
          ++ show heap
    Just array -> case IntMap.lookup i array of
      Nothing ->
        throwError $
          "unbound addr " ++ show (addr, i)
            ++ " in heap "
            ++ show heap
      Just n -> return n

-- internal function for allocating an array with a set of variables to associate with
allocateArray' :: IntSet -> M n (Ref ('A ty))
allocateArray' vars = do
  let size = IntSet.size vars
  addr <- freshAddr
  writeHeap addr $ zip [0 .. pred size] $ IntSet.toList vars
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
update :: Proper ty => Ref ('A ('V ty)) -> Int -> Expr ty n -> M n ()
update (Array addr) i (Var _ (Variable n)) = writeHeap addr [(i, n)]
update (Array addr) i expr = do
  ref <- freshVar
  writeHeap addr [(i, ref)]
  assign (Variable ref) expr

--------------------------------------------------------------------------------

reduce :: Foldable t => Expr ty n -> t a -> (Expr ty n -> a -> Comp n ty) -> Comp n ty
reduce a xs f = foldM f a xs

every :: Foldable t => (a -> Expr 'Bool n) -> t a -> Comp n 'Bool
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

--------------------------------------------------------------------------------

ifThenElse :: Expr 'Bool n -> Comp n ty -> Comp n ty -> Comp n ty
ifThenElse p x y = IfThenElse p <$> x <*> y
