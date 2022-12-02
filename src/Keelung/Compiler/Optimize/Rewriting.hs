{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Keelung.Compiler.Optimize.Rewriting
  ( run,
  )
where

import Control.Arrow (left)
import Control.Monad
import Control.Monad.State
import Keelung.Error (Error (ElabError))
import Keelung.Syntax.Typed

--------------------------------------------------------------------------------

run :: Elaborated -> Either Error Elaborated
run (Elaborated expr comp) = do
  ((), comp') <- left ElabError $
    runComp comp $ do
      let assertions = compAssertions comp
      assertions' <- filterM rewriteAssertEq assertions
      modify' $ \st -> st {compAssertions = assertions'}
  return $ Elaborated expr comp'

-- assert X `Eq` Y => X = Y
-- rewrite assertion as assignments, returns False if rewriting was made
rewriteAssertEq :: Expr -> Comp Bool
rewriteAssertEq expr = case expr of
  Boolean (EqB (VarB ref) y) -> do
    assignB ref y
    return False
  Boolean (EqB (InputVarB ref) y) -> do
    assignBI ref y
    return False
  Boolean (EqF (VarF ref) y) -> do
    assignF ref y
    return False
  Boolean (EqF (VarFI ref) y) -> do
    assignFI ref y
    return False
  Boolean (EqU _ (VarU w ref) y) -> do
    assignU w ref y
    return False
  Boolean (EqU _ (InputVarU w ref) y) -> do
    assignUI w ref y
    return False
  Boolean (EqB x (VarB ref)) -> do
    assignB ref x
    return False
  Boolean (EqB x (InputVarB ref)) -> do
    assignBI ref x
    return False
  Boolean (EqF x (VarF ref)) -> do
    assignF ref x
    return False
  Boolean (EqF x (VarFI ref)) -> do
    assignFI ref x
    return False
  Boolean (EqU _ x (VarU w ref)) -> do
    assignU w ref x
    return False
  Boolean (EqU _ x (InputVarU w ref)) -> do
    assignUI w ref x
    return False
  Boolean (EqB x y) -> do
    -- introduce a fresh variable
    -- and assign both expressions to it
    var <- allocVarB
    assignB var x
    assignB var y
    return False
  Boolean (EqF x y) -> do
    -- introduce a fresh variable
    -- and assign both expressions to it
    var <- allocVarN
    assignF var x
    assignF var y
    return False
  Boolean (EqU w x y) -> do
    -- introduce a fresh variable
    -- and assign both expressions to it
    var <- allocVarU w
    assignU w var x
    assignU w var y
    return False
  -- BEq (Var ref) y -> do
  --   assignBool ref y
  --   return False
  -- BEq x (Var ref) -> do
  --   assignBool ref x
  --   return False
  -- BEq x y -> do
  --   -- introduce a fresh variable
  --   -- and assign both expressions to it
  --   var <- allocVar
  --   let ref = VarB var
  --   assignBool ref x
  --   assignBool ref y
  --   return False
  _ -> return True
