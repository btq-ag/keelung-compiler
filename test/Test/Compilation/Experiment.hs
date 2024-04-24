{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Test.Compilation.Experiment (run, tests) where

import Control.Monad (forM_)
import Data.Either qualified as Either
import Data.Field.Galois (Prime)
import Data.Word (Word8)
import Keelung hiding (MulU, VarUI)
import Keelung.Compiler (Error (..))
import Keelung.Compiler.Compile.Error (Error)
import Keelung.Data.U (U)
import Keelung.Data.U qualified as U
import Keelung.Interpreter qualified as Interpreter
import Keelung.Solver qualified as Solver
import Test.Arbitrary (arbitraryUOfWidth)
import Test.Hspec
import Test.QuickCheck
import Test.Util
import qualified Keelung.Data.SlicePolynomial as SlicePolynomial
import Keelung.Data.SlicePolynomial (SlicePoly)
import Keelung.Data.Slice (Slice(Slice))
import Keelung.Data.Reference
import qualified Keelung.Data.LC as LC
import qualified Keelung.Data.PolyL as PolyL

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- it "failure" $ do
  --     let program divisor = do
  --           dividend <- input Public :: Comp (UInt 8)
  --           performDivMod dividend divisor
  --     let (dividend, divisor) = (12, 1) :: (Word8, Word8)
  --     let expected = map fromIntegral [dividend `div` divisor, dividend `mod` divisor]
  --     -- debug gf181 (program (fromIntegral divisor))
  --     --     forM_ [gf181, Prime 17, Binary 7] $ \field -> do
  --     check gf181 (program (fromIntegral divisor)) [fromIntegral dividend] [] expected
  --     check (Prime 17) (program (fromIntegral divisor)) [fromIntegral dividend] [] expected
  --     check (Binary 7) (program (fromIntegral divisor)) [fromIntegral dividend] [] expected

  it "Prime 2" $ do
    let program bound = do
          x <- input Public :: Comp (UInt 4)
          assertLTE x bound
    debug (Prime 2) (program 8)
    -- forAll (choose (0, 14)) $ \bound -> do
    -- let bound = 11
    -- check (Prime 2) (program bound) [0] [] []
    -- forM_ [0 .. 15] $ \x -> do
    --   if x <= bound
    --     then check (Prime 2) (program bound) [fromInteger x] [] []
    --     else
    --       throwErrors
    --         (Prime 2)
    --         (program bound)
    --         [fromInteger x]
    --         []
    --         (InterpreterError (Interpreter.AssertLTEError (fromInteger x) bound))
    --         (SolverError (Solver.ConflictingValues "at eliminateIfHold") :: Keelung.Compiler.Error (Prime 2))

  -- it "variable dividend / variable divisor" $ do
  --   let program = do
  --         dividend <- input Public :: Comp (UInt 8)
  --         divisor <- input Public
  --         performDivMod dividend divisor

  --   let (dividend, divisor) = (4, 3)
  --   let expected = [dividend `div` divisor, dividend `mod` divisor]
  --   check gf181 program [dividend, divisor] [] expected