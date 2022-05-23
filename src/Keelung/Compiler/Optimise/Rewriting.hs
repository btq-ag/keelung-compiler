{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Keelung.Compiler.Optimise.Rewriting
  ( run,
  )
where

import Keelung.Monad
import Keelung.Syntax
import Control.Monad
import Control.Monad.State
import Control.Arrow (left)


--------------------------------------------------------------------------------

run :: Elaborated ty n -> Either String (Elaborated ty n)
run (Elaborated expr comp) = left show $ do
  ((), comp') <- runComp comp $ do 
    let assertions = compAssertions comp 
    assertions' <- filterM rewriteAssertEq assertions
    modify' $ \st -> st { compAssertions = assertions' }
  return $ Elaborated expr comp'

-- assert X `Eq` Y => X = Y
-- rewrite assertion as assignments, returns False if rewriting was made
rewriteAssertEq :: Expr ty n -> Comp n Bool 
rewriteAssertEq expr = case expr of 
  Eq (Var ref) y -> do 
    assign ref y
    return False 
  Eq x (Var ref) -> do 
    assign ref x 
    return False 
  Eq x y -> do 
    -- introduce a fresh variable 
    -- and assign both expressions to it
    var <- allocVar
    let ref = Variable var 
    assign ref x 
    assign ref y
    return False 
  BEq (Var ref) y -> do 
    assign ref y
    return False 
  BEq x (Var ref) -> do 
    assign ref x 
    return False 
  BEq x y -> do 
    -- introduce a fresh variable 
    -- and assign both expressions to it
    var <- allocVar
    let ref = Variable var 
    assign ref x 
    assign ref y
    return False 
  _ -> return True
