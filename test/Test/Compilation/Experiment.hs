{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Compilation.Experiment where

import Keelung
import Test.Compilation.Util
import Test.Hspec
import Test.QuickCheck

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Experiment" $ do
  
  describe "Conditionals" $ do
    it "variable / variable / variable" $ do
      let program = do
            p <- input Public
            x <- input Public :: Comp (UInt 4)
            y <- input Public
            return $ cond p x y
      let genParam = do 
                p <- arbitrary
                x <- chooseInt (0, 15)
                y <- chooseInt (0, 15)
                return (p, x, y)
      forAll genParam $ \(p, x, y) -> do
        let expected = [fromIntegral $ if p then x else y]
        testCompiler gf181 program [if p then 1 else 0, fromIntegral x , fromIntegral y] [] expected

    it "variable / variable / constant" $ do
          let program y = do
                p <- input Public
                x <- input Public :: Comp (UInt 4)
                return $ cond p x y
          let genParam = do 
                    p <- arbitrary
                    x <- chooseInt (0, 15)
                    y <- chooseInt (0, 15)
                    return (p, x, y)
          forAll genParam $ \(p, x, y) -> do
            let expected = [fromIntegral $ if p then x else y]
            testCompiler gf181 (program (fromIntegral y)) [if p then 1 else 0, fromIntegral x] [] expected

    it "variable / constant / variable" $ do
          let program x = do
                p <- input Public
                y <- input Public :: Comp (UInt 4)
                return $ cond p x y
          let genParam = do 
                    p <- arbitrary
                    x <- chooseInt (0, 15)
                    y <- chooseInt (0, 15)
                    return (p, x, y)
          forAll genParam $ \(p, x, y) -> do
            let expected = [fromIntegral $ if p then x else y]
            testCompiler gf181 (program (fromIntegral x)) [if p then 1 else 0, fromIntegral y] [] expected

    it "variable / constant / constant" $ do
          let program x y = do
                p <- input Public
                return $ cond p x y
          let genParam = do 
                    p <- arbitrary
                    x <- chooseInt (0, 15)
                    y <- chooseInt (0, 15)
                    return (p, x, y)
          forAll genParam $ \(p, x, y) -> do
            let expected = [fromIntegral $ if p then x else y]
            testCompiler gf181 (program (fromIntegral x :: UInt 4) (fromIntegral y)) [if p then 1 else 0] [] expected

    it "constant predicate" $ do
      let program = do
            return $ cond true (3 :: UInt 2) 2
      testCompiler gf181 program [] [] [3]