{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
import Test.Compilation.Util
import Test.Hspec
import Keelung.Compiler.Options
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
  it "2 positive variables / Byte" $ do
        let program = do
              x <- inputUInt Public :: Comp (UInt 1)
              y <- inputUInt Public
              return $ x + y
        debugWithOpts options (Binary 7) program
        -- testCompilerWithOpts options (Binary 7) program [0, 0] [] [0]

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