{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
import Test.Compilation.Util
import Test.Hspec
import Keelung.Compiler.Options
import Control.Monad (forM_, replicateM)
-- import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- describe "pack" $ do
  --   it "from Field element" $ do
  --     let program = do
  --           x' <- input Public
  --           x <- toUInt 2 x' :: Comp (UInt 2)
  --           pack [x !!! 0, x !!! 1] :: Comp (UInt 3)
  --     property $ \(x :: Word) -> do
  --       testCompiler gf181 program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
  --       testCompiler (Prime 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
  --       testCompiler (Prime 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]
  --       testCompiler (Binary 7) program [fromIntegral (x `mod` 4)] [] [fromIntegral (x `mod` 4)]
  --       testCompiler (Binary 2) program [fromIntegral (x `mod` 2)] [] [fromIntegral (x `mod` 2)]

    -- it "from Field element" $ do
    --   -- let program = do
    --   --       x' <- input Public
    --   --       x <- toUInt 8 x' :: Comp (UInt 8)
    --   --       pack [x !!! 0, x !!! 1] :: Comp (UInt 3)
    --   -- property $ \(x :: Word) -> do
    --   --   testCompiler gf181 program [fromIntegral x] [] [fromIntegral x]


  -- it "should reveal variable layout" $ do
  --     let program = do
  --           x <- input Public :: Comp (UInt 8)
  --           y <- input Public :: Comp (UInt 8)
  --           return $ x + y
  --     let options = defaultOptions { optUseNewLinker = True }
  --     debugWithOpts options (Binary 283) program
  --     -- testCompilerWithOpts options (Binary 7) program [2, 2] [] [4]
  --     -- testCompiler (Prime 257) program [2, 2] [] [4]
  --     -- runSolver (Prime 257) program [2, 2] []

  let options = defaultOptions { optUseNewLinker = True }

  it "more than 4 variables + constant" $ do
    let program constant n = do
          xs <- replicateM n (inputBool Public)
          return $ foldl (.^.) (if constant then true else false) xs
    let inputs = [1,0,1,1,1,1,1,1,1,1,0,1,0,0,1,1,0]
    let expected = [1]
    -- forM_ [Prime 11] $ \field -> do
    forM_ [gf181, Prime 2, Prime 13, Prime 257, Binary 7] $ \field -> do
      -- debugWithOpts options field (program True 17)
      testCompilerWithOpts options field (program True 17) inputs [] expected

  -- it "or 2" $ do
  --   let program = do
  --         x <- inputUInt Public :: Comp (UInt 4)
  --         return $ (x .|. 3) !!! 2
  --   debugWithOpts options gf181 program
  --   testCompilerWithOpts options gf181 program [3] [] [0]
    -- testCompilerWithOpts options gf181 program [5] [] [1]


  -- it "should reveal variable layout" $ do
  --   let program = do
  --         u <- inputUInt Public :: Comp (UInt 4)
  --         -- b <- inputBool Public
  --         -- f <- inputField Public
  --         -- return $ cond (f `eq` 0 .|. b) u (u + 1)
  --         return (u' !!! 0)
  --   debug gf181 program