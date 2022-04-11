{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Keelung.Optimiser.Rewriting
  ( run,
  )
where

import Keelung.Monad
-- import Keelung.Syntax

--------------------------------------------------------------------------------

run :: Elaborated ty n -> Elaborated ty n
run (Elaborated expr comp) =
--   let assertions' = map rewriteAssertEq assertions
   Elaborated expr comp

-- -- assert X `Eq` Y => X = Y
-- rewriteAssertEq :: Expr 'Bool n -> Expr 'Bool n
-- rewriteAssertEq expr = case expr of 
--   Eq (Var ref) y -> _ 
--   Eq x (Var ref) -> _ 
--   Eq x y ->
--   _ -> expr 

--   Val val -> _
--   Var ref -> _
--   And x y -> _
--   Or x y -> _
--   Xor x y -> _
--   BEq x y -> _
--   IfThenElse x y z -> _
--   ToBool x -> _
