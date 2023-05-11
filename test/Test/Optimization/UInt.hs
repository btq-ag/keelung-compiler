{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Optimization.UInt (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util (execute, shouldHaveSize)


tests :: SpecWith ()
tests = do
  describe "UInt" $ do
    describe "Constants" $ do
      it "`return 0`" $ do
        (cs, cs') <- execute $ do
          return (0 :: UInt 4)
        cs `shouldHaveSize` 6
        cs' `shouldHaveSize` 6

    -- it "`return 0[3]`" $ do
    --   (cs, cs') <- execute $ do
    --     let a = 0  :: UInt 4
    --     return $ a !!! 3
    --   debug cs'
    --   cs `shouldHaveSize` 2
    --   cs' `shouldHaveSize` 2

    describe "Comparison" $ do
      it "compute LTE (variable / variable)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lte` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute LTE 1 (variable / constant)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ (0 :: UInt 4) `lte` x
        cs `shouldHaveSize` 7
        cs' `shouldHaveSize` 7

      it "compute LTE 2 (variable / constant)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ (1 :: UInt 4) `lte` x
        cs `shouldHaveSize` 10
        cs' `shouldHaveSize` 9

      it "compute LTE 1 (constant / variable)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ x `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 11
        cs' `shouldHaveSize` 9

      it "compute LTE 2 (constant / variable)" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          return $ x `lte` (1 :: UInt 4)
        cs `shouldHaveSize` 10
        cs' `shouldHaveSize` 8

      it "compute LTE (constant / constant)" $ do
        (cs, cs') <- execute $ do
          return $ 0 `lte` (0 :: UInt 4)
        cs `shouldHaveSize` 2
        cs' `shouldHaveSize` 2

      it "compute LT" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `lt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute GTE" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gte` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

      it "compute GT" $ do
        (cs, cs') <- execute $ do
          x <- inputUInt @4 Public
          y <- inputUInt @4 Private
          return $ x `gt` y
        cs `shouldHaveSize` 19
        cs' `shouldHaveSize` 18

run :: IO ()
run = hspec tests
