{-# LANGUAGE DataKinds #-}

module Test.Optimization.UInt.Bitwise (tests, run) where

-- import Keelung.Compiler.Linker
import Test.Hspec

-- --
run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Bitwise" $ do
  return ()

-- describe "Shifts" $ do
--   it "left" $ do
--     let program =  do
--               x <- input Public :: Comp (UInt 8)
--               return $ x .<<. 1