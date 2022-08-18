{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Keelung.Compiler.Interpret.Kinded (run) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor (first)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semiring (Semiring (..))
import Keelung hiding (inputs, interpret)
import Keelung.Types

--------------------------------------------------------------------------------

run :: (GaloisField n, Bounded n, Integral n) => Elaborated t n -> [n] -> Either (InterpretError n) [n]
run elab inputs = runM (bindings, heap) $ do
  -- interpret the assignments first
  -- reverse the list assignments so that "simple values" are binded first
  -- see issue#3: https://github.com/btq-ag/keelung-compiler/issues/3
  let numAssignments = reverse (compNumAsgns comp)
  forM_ numAssignments $ \(Assignment var e) -> do
    values <- interpret e
    addBinding var values

  let boolAssignments = reverse (compBoolAsgns comp)
  forM_ boolAssignments $ \(Assignment var e) -> do
    values <- interpret e
    addBinding var values

  -- interpret the assertions next
  -- throw error if any assertion fails
  forM_ (compAssertions comp) $ \e -> do
    values <- interpret e
    when (values /= [1]) $ do
      -- collect variables and their bindings in the expression
      vars <- freeVars e
      bindings' <- mapM (\var -> (var,) <$> lookupVar var) $ IntSet.toList vars
      throwError $ InterpretAssertionError e (IntMap.fromList bindings')

  -- lastly interpret the expression and return the result
  interpret (elabVal elab)
  where
    comp = elabComp elab
    bindings = IntMap.fromAscList $ zip (IntSet.toAscList (compInputVars comp)) inputs
    heap = compHeap comp

--------------------------------------------------------------------------------

-- collect free variables of an expression
freeVars :: Val t n -> M n IntSet
freeVars expr = case expr of
  Number _ -> return mempty
  Boolean _ -> return mempty
  UnitVal -> return mempty
  Ref (NumVar n) -> return $ IntSet.singleton n
  Ref (BoolVar n) -> return $ IntSet.singleton n
  Ref (Array _ _ addr) -> freeVarsOfArray addr
  Add x y -> (<>) <$> freeVars x <*> freeVars y
  Sub x y -> (<>) <$> freeVars x <*> freeVars y
  Mul x y -> (<>) <$> freeVars x <*> freeVars y
  Div x y -> (<>) <$> freeVars x <*> freeVars y
  Eq x y -> (<>) <$> freeVars x <*> freeVars y
  And x y -> (<>) <$> freeVars x <*> freeVars y
  Or x y -> (<>) <$> freeVars x <*> freeVars y
  Xor x y -> (<>) <$> freeVars x <*> freeVars y
  BEq x y -> (<>) <$> freeVars x <*> freeVars y
  IfNum x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
  IfBool x y z -> (<>) <$> freeVars x <*> ((<>) <$> freeVars y <*> freeVars z)
  ToBool x -> freeVars x
  ToNum x -> freeVars x
  where
    freeVarsOfArray :: Addr -> M n IntSet
    freeVarsOfArray addr = do
      heap <- gets snd
      case IntMap.lookup addr heap of
        Nothing -> throwError $ InterpretUnboundAddrError addr heap
        Just (elemType, array) -> case elemType of
          NumElem -> return $ IntSet.fromList (IntMap.elems array)
          BoolElem -> return $ IntSet.fromList (IntMap.elems array)
          (ArrElem _ _) -> IntSet.unions <$> mapM freeVarsOfArray (IntMap.elems array)

--------------------------------------------------------------------------------

-- | The interpreter typeclass
class Interpret a n where
  interpret :: a -> M n [n]

instance GaloisField n => Interpret n n where
  interpret x = return [x]

instance GaloisField n => Interpret Bool n where
  interpret True = return [one]
  interpret False = return [zero]

instance GaloisField n => Interpret (Ref t) n where
  interpret (BoolVar var) = pure <$> lookupVar var
  interpret (NumVar var) = pure <$> lookupVar var
  interpret (Array _ _ addr) = lookupAddr addr

instance GaloisField n => Interpret (Val t n) n where
  interpret val = case val of
    Number n -> interpret n
    Boolean b -> interpret b
    UnitVal -> return []
    Ref ref -> interpret ref
    Add x y -> zipWith (+) <$> interpret x <*> interpret y
    Sub x y -> zipWith (-) <$> interpret x <*> interpret y
    Mul x y -> zipWith (*) <$> interpret x <*> interpret y
    Div x y -> zipWith (/) <$> interpret x <*> interpret y
    Eq x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    And x y -> zipWith (*) <$> interpret x <*> interpret y
    Or x y -> zipWith (+) <$> interpret x <*> interpret y
    Xor x y -> zipWith (\x' y' -> x' + y' - 2 * (x' * y')) <$> interpret x <*> interpret y
    BEq x y -> do
      x' <- interpret x
      y' <- interpret y
      interpret (x' == y')
    IfNum p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    IfBool p x y -> do
      p' <- interpret p
      case p' of
        [0] -> interpret y
        _ -> interpret x
    ToBool x -> interpret x
    ToNum x -> interpret x

--------------------------------------------------------------------------------

-- | The interpreter monad
type M n = StateT (IntMap n, Heap) (Except (InterpretError n))

runM :: (IntMap n, Heap) -> M n a -> Either (InterpretError n) a
runM st p = runExcept (evalStateT p st)

lookupVar :: Show n => Int -> M n n
lookupVar var = do
  bindings <- gets fst
  case IntMap.lookup var bindings of
    Nothing -> throwError $ InterpretUnboundVarError var bindings
    Just val -> return val

lookupAddr :: Show n => Int -> M n [n]
lookupAddr addr = do
  heap <- gets snd
  case IntMap.lookup addr heap of
    Nothing -> throwError $ InterpretUnboundAddrError addr heap
    Just (elemType, array) -> case elemType of
      NumElem -> mapM lookupVar (IntMap.elems array)
      BoolElem -> mapM lookupVar (IntMap.elems array)
      (ArrElem _ _) -> concat <$> mapM lookupAddr (IntMap.elems array)

addBinding :: Ref t -> [n] -> M n ()
addBinding _ [] = error "addBinding: empty list"
addBinding (BoolVar var) [val] = modify (first (IntMap.insert var val))
addBinding (NumVar var) [val] = modify (first (IntMap.insert var val))
addBinding (Array _ _ addr) vals = do
  vars <- collectVarsFromAddr addr
  mapM_
    (modify . first . uncurry IntMap.insert)
    (zip vars vals)
  where
    collectVarsFromAddr :: Addr -> M n [Var]
    collectVarsFromAddr address = do
      heap <- gets snd
      case IntMap.lookup address heap of
        Nothing -> throwError $ InterpretUnboundAddrError addr heap
        Just (elemType, array) -> case elemType of
          NumElem -> return $ IntMap.elems array
          BoolElem -> return $ IntMap.elems array
          (ArrElem _ _) -> concat <$> mapM collectVarsFromAddr (IntMap.elems array)
addBinding _ _ = error "addBinding: too many values"

--------------------------------------------------------------------------------

data InterpretError n
  = InterpretUnboundVarError Var (IntMap n)
  | InterpretUnboundAddrError Addr Heap
  | InterpretAssertionError (Val 'Bool n) (IntMap n)
  deriving (Eq)

instance (Show n, Bounded n, Integral n, Fractional n) => Show (InterpretError n) where
  show (InterpretUnboundVarError var bindings) =
    "unbound variable " ++ show var
      ++ " in bindings "
      ++ show (fmap N bindings)
  show (InterpretUnboundAddrError var heap) =
    "unbound address " ++ show var
      ++ " in heap "
      ++ show heap
  show (InterpretAssertionError val bindings) =
    "assertion failed: " ++ show val
      ++ "\nbindings of variables: "
      ++ show (fmap N bindings)
