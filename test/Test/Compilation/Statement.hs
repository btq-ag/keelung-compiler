{-# LANGUAGE DataKinds #-}

module Test.Compilation.Statement where

import Control.Monad
import Keelung
import Test.Compilation.Util
import Test.Hspec

run :: IO ()
run = hspec tests

--------------------------------------------------------------------------------

tests :: SpecWith ()
tests = describe "Statement" $ do
  describe "toField" $ do
    it "from variable" $ do
      let program = do
            x <- input Public :: Comp (UInt 8)
            toField x
      forM_ [gf181] $ \field -> do
        --   forM_ [gf181, Prime 2, Binary 7] $ \field -> do
        runAll field program [100] [] [100]
      debug gf181 program
