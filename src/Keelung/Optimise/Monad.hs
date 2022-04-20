module Keelung.Optimise.Monad
  ( unifyVars,
    bindVar,
    rootOfVar,
    lookupVar,
    assignmentOfVars,
    OptiM,
    Lookup(..),
    runOptiM,
    runOptiM'
  )
where

import Control.Monad.State
import Data.Field.Galois (GaloisField)
import Data.IntMap (IntMap)
import qualified Data.IntMap.Lazy as Map
import Keelung.Optimise.UnionFind (UnionFind (..))
import qualified Keelung.Optimise.UnionFind as UnionFind
import Keelung.Syntax.Common

----------------------------------------------------------------
--                  Simplifier State Monad                    --
----------------------------------------------------------------

-- | Equalities among variables,
-- together with a partial map from variables
-- to constants (hidden inside the "UnionFind"
-- data structure).
type OptiM n = State (UnionFind n)

runOptiM :: IntMap n -> OptiM n a -> a
runOptiM xs f = evalState f (UnionFind.new xs)

runOptiM' :: IntMap Var -> IntMap Int -> IntMap f -> State (UnionFind f) a -> a
runOptiM' xs ys zs f = evalState f (UnionFind xs ys zs)

-- | Unify variables 'x' and 'y'.
unifyVars :: GaloisField n => Var -> Var -> OptiM n ()
unifyVars x y = modify (\xs -> UnionFind.union xs x y)

-- | Bind variable 'x' to 'c'.
bindVar :: GaloisField n => Var -> n -> OptiM n ()
bindVar x val = do
  root <- rootOfVar x
  modify $ \xs -> UnionFind.bindVar xs root val

-- | Return 'x''s root (the representative of its equivalence class).
rootOfVar :: GaloisField n => Var -> OptiM n Var
rootOfVar x = do
  xs <- get
  let (root, xs') = UnionFind.find xs x
  put xs'
  return root

data Lookup n = Root Var | Value n deriving (Eq, Show)

-- | Return the binding associated with variable 'x', or 'x''s root
-- if no binding exists.
lookupVar :: GaloisField n => Var -> OptiM n (Lookup n)
lookupVar x = do
  root <- rootOfVar x
  xs <- get
  case UnionFind.lookupVar xs root of
    Nothing -> return $ Root root
    Just c -> return $ Value c

-- | Construct a partial assignment from 'vars' to field elements.
assignmentOfVars :: GaloisField n => [Var] -> OptiM n (Witness n)
assignmentOfVars vars = do
  binds <- mapM lookupVar vars
  return $
    Map.fromList $
      concatMap
        ( \(x, ec) -> case ec of
            Root _ -> []
            Value c -> [(x, c)]
        )
        $ zip vars binds
