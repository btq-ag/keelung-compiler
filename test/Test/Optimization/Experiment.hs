{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Optimization.Experiment (tests, run) where

import Keelung hiding (compileO0)
import Test.Hspec
import Test.Optimization.Util

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = describe "Experiment" $ do
  -- 8 * 3 for input / output
  -- 8 for carry bit
  -- 1 for multiplication
  it "2 variables / byte / GF181" $ do
    (cs, cs') <- executeGF181 $ do
      x <- inputUInt @8 Public
      y <- inputUInt @8 Public
      return $ x * y
    cs `shouldHaveSize` 42
    cs' `shouldHaveSize` 33
    -- cs' `shouldHaveSize` 42

  --   -- 8 * 3 for input / output
  --   -- 4 * 5 for intermediate limbs
  --   -- 2 for carry bit
  --   -- 3 for multiplication
  --   -- 1 for addition

  --   --                      #### ####
  --   --         x)           #### ####
  --   --    -------------------------------
  --   --                      #### ----
  --   --                 #### ####
  --   --         +)      #### ####
  --   --    -------------------------------
  --   --                   ## #### ####
  --   ------------------------------------------
  --   it "2 variables / byte / Prime 257" $ do
  --     (cs, cs') <- executePrime 257 $ do
  --       x <- inputUInt @8 Public
  --       y <- inputUInt @8 Public
  --       return $ x * y
  --     cs `shouldHaveSize` 55
  --     -- cs' `shouldHaveSize` 50
  --     cs' `shouldHaveSize` 55

  --   it "2 variables / byte / Prime 1031" $ do
  --     (cs, cs') <- executePrime 1031 $ do
  --       x <- inputUInt @8 Public
  --       y <- inputUInt @8 Public
  --       return $ x * y
  --     cs `shouldHaveSize` 55
  --     -- cs' `shouldHaveSize` 50
  --     cs' `shouldHaveSize` 55

  --   -- TODO: can be lower
  --   it "variable / constant" $ do
  --     (cs, cs') <- executeGF181 $ do
  --       x <- inputUInt @4 Public
  --       return $ x * 4
  --     cs `shouldHaveSize` 18
  --     -- cs' `shouldHaveSize` 13
  --     cs' `shouldHaveSize` 18

  --   -- TODO: should've been just 4
  --   it "constant / constant" $ do
  --     (cs, cs') <- executeGF181 $ do
  --       return $ 2 * (4 :: UInt 4)
  --     -- print $ linkConstraintModule cs'
  --     cs `shouldHaveSize` 5
  --     cs' `shouldHaveSize` 5

  -- describe "Carry-less Multiplication" $ do
  --   -- TODO: bring this down
  --   it "2 byte variables" $ do
  --     -- constraint breakdown:
  --     -- I/O: 24 = 2 * 8 + 8
  --     -- ANDs: 36 = 8 * 9 / 2
  --     -- XORs: 7
  --     (cs, cs') <- executeGF181 $ do
  --       x <- input Public :: Comp (UInt 8)
  --       y <- input Public :: Comp (UInt 8)
  --       return (x .*. y)
  --     -- print $ linkConstraintModule cs'
  --     cs `shouldHaveSize` 91
  --     cs' `shouldHaveSize` 87

  -- describe "Constants" $ do
  --   -- TODO: should be just 4
  --   it "`return 0`" $ do
  --     (cs, cs') <- executeGF181 $ do
  --       return (0 :: UInt 4)
  --     -- print $ linkConstraintModule cs'
  --     cs `shouldHaveSize` 5
  --     cs' `shouldHaveSize` 5

  -- -- describe "Bitwise Operators" $ do
  -- --   it "setBit twice" $ do
  -- --     (cs, cs') <- executeGF181 $ do
  -- --       x <- inputUInt @8 Public
  -- --       return $ setBit (setBit x 0 true) 1 true
  -- --     print cs
  -- --     -- print $ linkConstraintModule cs'
  -- --     cs `shouldHaveSize` 24
  -- --     cs' `shouldHaveSize` 24

  -- --     it "U8 -> U16" $ do
  -- --       (cs, cs') <- executeGF181 $ do
  -- --         x <- inputUInt @8 Public
  -- --         y <- inputUInt @8 Public
  -- --         return $ u8ToU16 x y
  -- --       print cs
  -- --       cs `shouldHaveSize` 528
  -- --       cs' `shouldHaveSize` 528
  -- -- where
  -- --   u8ToU16 :: UInt 8 -> UInt 8 -> UInt 16
  -- --   u8ToU16 x y =
  -- --     foldl (\n index -> setBit n (index + 8) (y !!! index)) (foldl (\n index -> setBit n index (x !!! index)) 0 [0 .. 7]) [0 .. 7]