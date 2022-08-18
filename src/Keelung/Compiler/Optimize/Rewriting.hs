{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Keelung.Compiler.Optimize.Rewriting
  ( run,
  )
where

import Keelung.Syntax.Typed
import Control.Monad
import Control.Monad.State
import Keelung.Error (ElabError)

--------------------------------------------------------------------------------

run :: Elaborated -> Either ElabError Elaborated
run (Elaborated expr comp) = do
  ((), comp') <- runComp comp $ do 
    let assertions = compAssertions comp 
    assertions' <- filterM rewriteAssertEq assertions
    modify' $ \st -> st { compAssertions = assertions' }
  return $ Elaborated expr comp'

-- assert X `Eq` Y => X = Y
-- rewrite assertion as assignments, returns False if rewriting was made
rewriteAssertEq :: Expr -> Comp Bool 
rewriteAssertEq expr = case expr of 
  Eq (Var ref) y -> do 
    assignNum ref y
    return False 
  Eq x (Var ref) -> do 
    assignNum ref x 
    return False 
  Eq x y -> do 
    -- introduce a fresh variable 
    -- and assign both expressions to it
    var <- allocVar
    let ref = NumVar var 
    assignNum ref x 
    assignNum ref y
    return False 
  BEq (Var ref) y -> do 
    assignBool ref y
    return False 
  BEq x (Var ref) -> do 
    assignBool ref x 
    return False 
  BEq x y -> do 
    -- introduce a fresh variable 
    -- and assign both expressions to it
    var <- allocVar
    let ref = BoolVar var 
    assignBool ref x 
    assignBool ref y
    return False 
  _ -> return True
