{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
import Keelung.Compiler.Options
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

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

  -- let options = defaultOptions {optUseNewLinker = True}
  -- it "2 positive variables / Byte" $ do
  --   let program = do
  --         x <- inputUInt Public :: Comp (UInt 1)
  --         y <- inputUInt Public
  --         return $ x + y
  --   debugWithOpts options (Binary 7) program
  --   testCompilerWithOpts options (Binary 7) program [0, 0] [] [0]

  -- it "variable dividend / constant divisor" $ do
  --   let program divisor = do
  --         dividend <- input Public :: Comp (UInt 2)
  --         performDivMod dividend divisor

  --   let dividend = 3
  --   let divisor = 3
  --   let expected = [dividend `div` divisor, dividend `mod` divisor]
  --   let options = defaultOptions { optOptimize = False }

  --   forM_ [Binary 7] $ \field -> do
  --   -- forM_ [gf181, Prime 17, Binary 7] $ \field -> do
  --     -- debug field (program (fromIntegral divisor))
  --     -- testCompiler field (program (fromIntegral divisor)) [dividend] [] expected
  --     debugWithOpts options field (program (fromIntegral divisor))
  --     testCompilerWithOpts options field (program (fromIntegral divisor)) [dividend] [] expected

  -- it "variable dividend / constant divisor" $ do
  --   let program divisor = do
  --         dividend <- input Public :: Comp (UInt 4)
  --         performDivMod dividend divisor

  --   let dividend = 4
  --   let divisor = 4
  --   let expected = [dividend `div` divisor, dividend `mod` divisor]
  --   let options = defaultOptions { optOptimize = True }

  --   forM_ [Prime 17] $ \field -> do
  --     debugWithOpts options field (program (fromIntegral divisor))
  --     testCompilerWithOpts options field (program (fromIntegral divisor)) [dividend] [] expected

  -- it "variable dividend / variable divisor" $ do
  --   let program = do
  --         dividend <- input Public :: Comp (UInt 4)
  --         divisor <- input Public
  --         performDivMod dividend divisor

  --   -- debug (Prime 17) program
  --   let genPair = do
  --         dividend <- choose (0, 15)
  --         divisor <- choose (1, 15)
  --         return (dividend, divisor)

  --   forAll genPair $ \(dividend, divisor) -> do
  --     let expected = [dividend `div` divisor, dividend `mod` divisor]
  --     forM_ [gf181, Prime 17] $ \field -> do
  --       let options = defaultOptions { optDisableTestingOnO0 = True }
  --       testCompilerWithOpts options field program [dividend, divisor] [] expected
  --     forM_ [Binary 7] $ \field -> do
  --       let options = defaultOptions { optUseNewLinker = False }
  --       testCompilerWithOpts options field program [dividend, divisor] [] expected

  -- it "constant dividend / variable divisor" $ do
  --   let program dividend = do
  --         divisor <- input Public :: Comp (UInt 8)
  --         performDivMod dividend divisor

  --   let genPair = do
  --         dividend <- choose (0, 255)
  --         divisor <- choose (1, 255)
  --         return (dividend, divisor)

  --   forAll genPair $ \(dividend, divisor) -> do
  --     let expected = [dividend `div` divisor, dividend `mod` divisor]
  --     forM_ [gf181, Prime 17] $ \field -> do
  --       let options = defaultOptions { optUseNewLinker = False, optDisableTestingOnO0 = True }
  --       testCompilerWithOpts options field (program (fromIntegral dividend)) [divisor] [] expected
  --     forM_ [Binary 7] $ \field -> do
  --       let options = defaultOptions { optUseNewLinker = False }
  --       testCompilerWithOpts options field (program (fromIntegral dividend)) [divisor] [] expected

  -- it "variable dividend / constant divisor" $ do
  --   let program divisor = do
  --         dividend <- input Public :: Comp (UInt 8)
  --         performDivMod dividend divisor

  --   let genPair = do
  --         dividend <- choose (0, 255)
  --         divisor <- choose (1, 255)
  --         return (dividend, divisor)

  --   forAll genPair $ \(dividend, divisor) -> do
  --     let expected = [dividend `div` divisor, dividend `mod` divisor]
  --     forM_ [gf181, Prime 17] $ \field -> do
  --       let options = defaultOptions { optUseNewLinker = False, optDisableTestingOnO0 = True }
  --       testCompilerWithOpts options field (program (fromIntegral divisor)) [dividend] [] expected
  --     forM_ [Binary 7] $ \field -> do
  --       let options = defaultOptions { optUseNewLinker = False }
  --       testCompilerWithOpts options field (program (fromIntegral divisor)) [dividend] [] expected

  -- it "constant dividend / constant divisor" $ do
  --   let program dividend divisor = performDivMod (fromIntegral dividend) (fromIntegral divisor :: UInt 8)
  --   let genPair = do
  --         -- dividend <- choose (75, 75)
  --         -- divisor <- choose (4, 4)
  --         return (75, 4)
  --   forAll genPair $ \(dividend, divisor) -> do
  --     let expected = [dividend `div` divisor, dividend `mod` divisor]
  --     -- forM_ [Prime 257] $ \field -> do
  --     forM_ [Prime 17] $ \field -> do
  --       -- failing on 4, 16, 64
  --       let options = defaultOptions { optUseNewLinker = True, optDisableTestingOnO0 = False }
  --       -- debugWithOpts options field (program dividend divisor)
  --       testCompilerWithOpts options field (program dividend divisor) [] [] expected
  --     -- forM_ [gf181, Prime 17] $ \field -> do
  --     --   let options = defaultOptions { optUseNewLinker = False, optDisableTestingOnO0 = True }
  --     --   testCompilerWithOpts options field (program dividend divisor) [] [] expected
  --     -- forM_ [Binary 7] $ \field -> do
  --     --   let options = defaultOptions { optUseNewLinker = False }
  --     --   testCompilerWithOpts options field (program dividend divisor) [] [] expected
  --     -- forM_ [Binary 7] $ \field -> do
  --     --   let options = defaultOptions { optUseNewLinker = True }
  --     --   testCompilerWithOpts options field (program dividend divisor) [] [] expected

  -- it "variable * constant + 0 / Byte" $ do
  --   let program y = do
  --         x <- input Public
  --         return $ x * fromIntegral y + 0 :: Comp (UInt 8)
  --   let genPair = do
  --         x <- choose (0, 255)
  --         y <- choose (0, 0)
  --         return (x, y)
  --   forAll genPair $ \(x, y) -> do
  --     let expected = [(x * y) `mod` 256]
  --     forM_ [Prime 257] $ \field -> do
  --       let options = defaultOptions {optUseNewLinker = True}
  --       debugWithOpts options field (program y)
  --       testCompilerWithOpts options field (program y) [toInteger x] [] expected

  -- it "Issue #36" $ do
  --   let program = do
  --         x <- input Public
  --         return $ x * 0 + 0 :: Comp (UInt 8)
  --   debug (Prime 257) program
  --   testCompiler (Prime 257) program [100] [] [0]

  describe "Binary field" $ do
    it "2 positive variables / Nimble" $ do
      let program = do
            x <- input Public
            y <- input Public
            return $ x + y :: Comp (UInt 4)
      let genPair = do
            x <- choose (0, 15)
            y <- choose (0, 15)
            return (x, y)
      forAll genPair $ \(x, y) -> do
        let expected = [toInteger (x + y) `mod` 16]
        testCompilerWithOpts (defaultOptions {optUseNewLinker = False, optOptimize = False}) (Binary 7) program [x, y] [] expected
        testCompilerWithOpts (defaultOptions {optUseNewLinker = False, optOptimize = True}) (Binary 7) program [x, y] [] expected
        testCompilerWithOpts (defaultOptions {optUseNewLinker = True, optOptimize = False}) (Binary 7) program [x, y] [] expected
        testCompilerWithOpts (defaultOptions {optUseNewLinker = True, optOptimize = True}) (Binary 7) program [x, y] [] expected
