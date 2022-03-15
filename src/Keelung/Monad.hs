{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Keelung.Monad where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Data.Set (Set)
import Keelung.Syntax

--------------------------------------------------------------------------------

-- The monad
type M n (ty :: Type) = WriterT [Assignment n] (StateT (Env n) (Except String))

-- how to run the monad
runM :: Env n -> M n ty a -> Either String ((a, [Assignment n]), Env n)
runM st p = runExcept (runStateT (runWriterT p) st)

--------------------------------------------------------------------------------

data Env a = Env
  { -- Counter for generating fresh variables
    envNextVar :: Int,
    -- Counter for allocating fresh address
    envNextAddr :: Int,
    -- Variables marked as inputs
    envInputVars :: Set Int
  }
  deriving (Show)

--------------------------------------------------------------------------------

data Assignment n = forall ty. Assignment (Variable ty) (Expr n ty)

instance Show n => Show (Assignment n) where
  show (Assignment var expr) = show var <> " := " <> show expr

--------------------------------------------------------------------------------

-- | Computation elaboration
elaborate :: M n ty (Expr n ty) -> Either String (Elaborated n ty)
elaborate prog = do
  ((expr, assertions), env) <- runM (Env 0 0 mempty) prog
  return $ Elaborated (envNextVar env) (envInputVars env) expr assertions

-- | The result of elaborating a computation
data Elaborated n ty = Elaborated
  { -- | The number of free variables in the computation
    elabNumOfVars :: Int,
    -- | Variables marked as inputs
    elabInputVars :: Set Int,
    -- | The resulting 'Expr'
    elabTExpr :: Expr n ty,
    -- | Assignements
    elabAssignments :: [Assignment n]
  }
  deriving (Show)