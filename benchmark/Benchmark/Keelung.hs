{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Benchmark.Keelung where

-- import Control.Monad ((<=<))
-- import Data.Foldable (toList)
-- import qualified Data.IntMap.Lazy as IntMap
-- import qualified Data.Set as Set
-- import GHC.IO.Exception
import Keelung
import qualified Keelung.Syntax.Untyped as Untyped
-- import Snarkl.Constraints (ConstraintSystem (..))
-- import Snarkl.Serialize (Serialize (serialize))
-- import Snarkl.Toplevel (Result (resultResult), serializeInputs, simplifyConstrantSystem)

benchElaborate :: Comp ty a -> Int
benchElaborate prog = case elaborate prog of
  Left _ -> -1
  Right elab -> toNumber $ elabExpr elab
  where
    toNumber :: Expr ty a -> Int
    toNumber !te = case te of
      Val _ -> 0
      Var _ -> 1
      Add _ _-> 2
      Sub _ _-> 3
      Mul _ _-> 4
      Div _ _-> 5
      Eq _ _-> 6
      And _ _-> 7
      Or _ _-> 8
      Xor _ _-> 9
      BEq _ _-> 10
      IfThenElse {} -> 11
      ToBool _ -> 12
      ToNum _ -> 13

benchEraseType :: (Erase ty, Num a) => Comp ty a -> Int
benchEraseType prog = case elaborate prog of
  Left _ -> -1
  Right elab -> toNumber $ erasedExpr $  eraseType elab
  where
    toNumber :: Untyped.Expr a -> Int
    toNumber !te = case te of
      Untyped.Var _ -> 0
      Untyped.Val _ -> 1
      Untyped.BinOp _ _ -> 2
      Untyped.IfThenElse {} -> 3
      -- Val _ -> 0
      -- Var _ -> 1
      -- Add _ _-> 2
      -- Sub _ _-> 3
      -- Mul _ _-> 4
      -- Div _ _-> 5
      -- Eq _ _-> 6
      -- And _ _-> 7
      -- Or _ _-> 8
      -- Xor _ _-> 9
      -- BEq _ _-> 10
      -- IfThenElse {} -> 11
      -- ToBool _ -> 12
      -- ToNum _ -> 13

-- -- Just compile to constraints (no simplification yet).
-- benchCompile :: (Typeable ty, GaloisField a, Serialize a) => Comp ty a -> IO [String]
-- benchCompile prog = case elaborate prog of
--   Left err -> do
--     print err
--     return []
--   Right elab -> do
--     let constraints = cs_constraints $ compile elab
--     putStrLn $ "Number of constraints: " ++ show (Set.size constraints)
--     return $ map serialize $ toList constraints

-- -- Compile to constraints and simplify.
-- benchSimplify :: (Typeable ty, GaloisField a, Serialize a) => Comp ty a -> [String]
-- benchSimplify prog = case elaborate prog of
--   Left err -> [show err]
--   Right elab ->
--     ( map serialize . toList
--         . cs_constraints
--         . snd
--         . simplifyConstrantSystem False IntMap.empty
--         . compile
--     )
--       elab

-- -- Same as 'r1cs', but also generates and serializes
-- -- a satisfying assignment, as well as serializing the given inputs.
-- benchWitGen ::
--   (Typeable ty, Serialize a, GaloisField a, Bounded a, Integral a) => SimplParam -> Comp ty a -> [a] -> String
-- benchWitGen flag prog inputs = case compileToR1CS flag prog of
--   Left err -> show err
--   Right r1cs -> serializeInputs inputs r1cs

-- -- This function "executes" the comp two ways, once by interpreting
-- -- the resulting TExp and second by interpreting the resulting circuit
-- -- on the inputs provided. Both results are checked to match 'res'.
-- -- The function outputs a 'Result' that details number of variables and
-- -- constraints in the resulting constraint system.
-- compareWithResult ::
--   (Typeable ty, GaloisField a, Serialize a, Bounded a, Integral a) => SimplParam -> Comp ty a -> [a] -> a -> Bool
-- compareWithResult flag prog inputs output =
--   case execute flag prog inputs of
--     Left _ -> False
--     Right result -> resultResult result == output
