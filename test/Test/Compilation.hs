{-# LANGUAGE DataKinds #-}

module Test.Compilation (run, tests) where

-- import qualified Basic

import Keelung
import Keelung.Compiler qualified as Compiler
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (toR1Cs)
import Keelung.Data.Polynomial qualified as Poly
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Compilation" $ do
    describe "Boolean Constraints" $ do
      it "echo / Boolean" $ do
        let program = inputBool Private
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, 1)])
                                  (Poly.buildEither 0 [(1, 1)])
                                  (Poly.buildEither 0 [(1, 1)])
                              ]
      it "echo / Field" $ do
        let program = inputField Private
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldNotContain` [ R1C
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                              ]
            toR1Cs r1cs
              `shouldNotContain` [ R1C
                                  (Poly.buildEither 0 [(1, 1)])
                                  (Poly.buildEither 0 [(1, 1)])
                                  (Poly.buildEither 0 [(1, 1)])
                              ]

    describe "Assertion" $ do
      it "Rewriting" $ do
        let program = do
              xs <- inputList Public 4
              ys <- inputList Public 4
              assert (sum xs `eq` sum (ys :: [Field]))
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, 1), (1, 1), (2, 1), (3, 1), (8, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(4, 1), (5, 1), (6, 1), (7, 1), (8, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

    -- describe "Unsigned Integer" $ do


      -- it "EQ 0" $ do
      --   -- output | input      | intermediate
      --   -- b        rrrrrrrruu   m
      --   -- 0        1234567890   1
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         return $ x `eq` y
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       --  (x - y) * m = 1 - out
      --       --  (x - y) * out = 0
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(9, 1), (10, -1)])
      --                             (Poly.buildEither 0 [(11, 1)])
      --                             (Poly.buildEither 1 [(0, -1)])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(9, 1), (10, -1)])
      --                             (Poly.buildEither 0 [(0, 1)])
      --                             (Poly.buildEither 0 [])
      --                         ]

      -- it "EQ 1" $ do
      --   -- output | input | intermediate
      --   -- b        rrrru   m
      --   -- 0        12345   6
      --   let program = do
      --         x <- inputUInt @4 Public
      --         return $ x `eq` 3
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       --  (x - 3) * m = 1 - out
      --       --  (x - 3) * out = 0
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither (-3) [(5, 1)])
      --                             (Poly.buildEither 0 [(6, 1)])
      --                             (Poly.buildEither 1 [(0, -1)])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither (-3) [(5, 1)])
      --                             (Poly.buildEither 0 [(0, 1)])
      --                             (Poly.buildEither 0 [])
      --                         ]

      -- it "NEQ 0" $ do
      --   -- output | input      | intermediate
      --   -- b        rrrrrrrruu   m
      --   -- 0        1234567890   1
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         return $ x `neq` y
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --         --  (x - y) * m = out
      --         --  (x - y) * (1 - out) = 0
      --         toR1Cs r1cs
      --           `shouldContain` [ R1C
      --                               (Poly.buildEither 0 [(9, 1), (10, -1)])
      --                               (Poly.buildEither 0 [(11, 1)])
      --                               (Poly.buildEither 0 [(0, 1)])
      --                           ]
      -- toR1Cs r1cs
      --   `shouldContain` [ R1C
      --                       (Poly.buildEither 0 [(9, 1), (10, -1)])
      --                       (Poly.buildEither 1 [(0, -1)])
      --                       (Poly.buildEither 0 [])
      --                   ]

      -- -- 1 - x[i] = out[i]
      -- forM_ [0 .. 3] $ \i ->
      --   toR1Cs r1cs
      --     `shouldContain` [ R1C
      --                         (Poly.buildEither 1 [(5 + i, -1), (0 + i, -1)])
      --                         (Poly.buildEither 1 [])
      --                         (Poly.buildEither 0 [])
      --                     ]

      -- it "ADD 0" $ do
      --   -- output | input
      --   -- rrrru    rrrrrrrruu
      --   -- 01234    5678901234
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         return (x + y)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (out - x - y)
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(8, 16)])
      --                             (Poly.buildEither 0 [(12, 1)])
      --                             (Poly.buildEither 0 [(4, 1), (13, -1), (14, -1)])
      --                         ]

      -- it "ADD 1" $ do
      --   -- output | input      | intermediate
      --   -- rrrru    rrrrrrrruu   rrrru
      --   -- 01234    5678901234   56789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         return (x + y + x)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (temp - x - y)
      --       -- NOTE: 'temp' will be moved from $19 to $16 after variable renumbering
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(8, 16)])
      --                             (Poly.buildEither 0 [(12, 1)])
      --                             (Poly.buildEither 0 [(16, 1), (13, -1), (14, -1)])
      --                         ]
      --       -- (2ⁿ * tempₙ₋₁) * (xₙ₋₁) = (out - temp - x)
      --       -- NOTE: 'tempₙ₋₁' will be moved from $18 to $15 after variable renumbering
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(15, 16)])
      --                             (Poly.buildEither 0 [(8, 1)])
      --                             (Poly.buildEither 0 [(4, 1), (16, -1), (13, -1)])
      --                         ]

      -- it "ADD 2" $ do
      --   -- output | input      | intermediate
      --   -- rrrru    rrrrrrrruu   rrrru
      --   -- 01234    5678901234   56789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         let z = 3
      --         return (x + y + z)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (temp - x - y)
      --       -- NOTE: 'temp' will be moved from $19 to $15 after variable renumbering
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(8, 16)])
      --                             (Poly.buildEither 0 [(12, 1)])
      --                             (Poly.buildEither 0 [(15, 1), (13, -1), (14, -1)])
      --                         ]
      --       -- (2ⁿ * tempₙ₋₁) * (3ₙ₋₁) = (out - temp - 3)
      --       -- => 0 = out - temp - 3
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither (-3) [(4, 1), (15, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]

      -- it "SUB 0" $ do
      --   -- output | input           | intermediate
      --   -- rrrru    rrrrrrrrrrrruuu   rrrru
      --   -- 01234    567890123456789   01234
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         z <- inputUInt @4 Public
      --         return (x - y - z)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (temp - x + y)
      --       -- NOTE: 'temp' will be moved from $24 to $21 after variable renumbering
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(8, 16)])
      --                             (Poly.buildEither 0 [(12, 1)])
      --                             (Poly.buildEither 0 [(21, 1), (17, -1), (18, 1)])
      --                         ]
      --       -- (2ⁿ * tempₙ₋₁) * (zₙ₋₁) = (out - temp + z)
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(20, 16)])
      --                             (Poly.buildEither 0 [(16, 1)])
      --                             (Poly.buildEither 0 [(4, 1), (21, -1), (19, 1)])
      --                         ]

      -- it "MUL 0" $ do
      --   -- output | input      | intermediate
      --   -- rrrru    rrrrrrrruu   u
      --   -- 01234    5678901234   5
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         return (x * y)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- x * y = out + 2ⁿ * quotient
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(13, 1)])
      --                             (Poly.buildEither 0 [(14, 1)])
      --                             (Poly.buildEither 0 [(4, 1), (15, 16)])
      --                         ]

      -- it "MUL 1" $ do
      --   -- output | input           | intermediate
      --   -- rrrru    rrrrrrrrrrrruuu   utqqq
      --   -- 01234    567890123456789   01234
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         z <- inputUInt @4 Public
      --         return (x * y * z * 3)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- x * y = temp1 + 2ⁿ * quotient1
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(17, 1)])
      --                             (Poly.buildEither 0 [(18, 1)])
      --                             (Poly.buildEither 0 [(21, 1), (22, 16)])
      --                         ]
      --       -- temp * z = temp2 + 2ⁿ * quotient2
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(21, 1)])
      --                             (Poly.buildEither 0 [(19, 1)])
      --                             (Poly.buildEither 0 [(20, 1), (23, 16)])
      --                         ]
      --       -- temp2 * 3 = out + 2ⁿ * quotient3
      --       -- => 0 = out + 2ⁿ * quotient3 - temp2 * 3
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(4, -1), (24, -16), (20, 3)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      -- it "ARITH 0" $ do
      --   -- output | input           | intermediate
      --   -- rrrru    rrrrrrrrrrrruuu   rutqr
      --   -- 01234    567890123456789   01234
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         z <- inputUInt @4 Public
      --         return (x * y + z - 3)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- x * y = temp1 + 2ⁿ * quotient
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(17, 1)])
      --                             (Poly.buildEither 0 [(18, 1)])
      --                             (Poly.buildEither 0 [(22, 1), (23, 16)])
      --                         ]
      --       -- (2ⁿ * temp1ₙ₋₁) * (zₙ₋₁) = (temp2 - temp1 - z)
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(20, 16)])
      --                             (Poly.buildEither 0 [(16, 1)])
      --                             (Poly.buildEither 0 [(21, 1), (22, -1), (19, -1)])
      --                         ]
      --       -- (2ⁿ * temp2ₙ₋₁) * (3ₙ₋₁) = (out - temp2 + 3)
      --       -- => (out - temp2 + 3) = 0
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither (-3) [(4, -1), (21, 1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]

      -- it "ROL 0" $ do
      --   -- output | input
      --   -- rrrru    rrrru
      --   -- 01234    56789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         return $ rotate x 1
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- x[i] = out[i + i]
      --       forM_ [0 .. 3] $ \i ->
      --         toR1Cs r1cs
      --           `shouldContain` [ R1C
      --                               (Poly.buildEither 0 [(i + 5, 1), ((i + 1) `mod` 4, -1)])
      --                               (Poly.buildEither 1 [])
      --                               (Poly.buildEither 0 [])
      --                           ]

      -- it "ROL 1" $ do
      --   -- output
      --   -- rrrru
      --   -- 01234
      --   let program = do
      --         let x = 3 :: UInt 4
      --         return $ rotate x (-1)
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 1 [(0, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(1, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(2, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 1 [(3, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      -- it "ROL 2" $ do
      --   -- output | input
      --   -- rrrru    rrrru
      --   -- 01234    56789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         return $ rotate (rotate x (-1)) 1
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- x[i] = out[i]
      --       forM_ [0 .. 3] $ \i ->
      --         toR1Cs r1cs
      --           `shouldContain` [ R1C
      --                               (Poly.buildEither 0 [(i + 5, 1), (i, -1)])
      --                               (Poly.buildEither 1 [])
      --                               (Poly.buildEither 0 [])
      --                           ]

      -- it "SHL 0" $ do
      --   -- output | input
      --   -- rrrru    rrrru
      --   -- 01234    56789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         return $ shift x 1
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- 0 = out[0]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(0, 1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       -- x[i] = out[i + i]
      --       forM_ [1 .. 3] $ \i ->
      --         toR1Cs r1cs
      --           `shouldContain` [ R1C
      --                               (Poly.buildEither 0 [(i + 5 - 1, 1), (i, -1)])
      --                               (Poly.buildEither 1 [])
      --                               (Poly.buildEither 0 [])
      --                           ]

      -- it "SHL 1" $ do
      --   -- output
      --   -- rrrrrrrrrrrruuu
      --   -- 012345678901234
      --   let program = do
      --         let x = 3 :: UInt 4
      --         return [shift x 1, shift x (-1), shift x 3]
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(0, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 1 [(1, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 1 [(2, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(3, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 1 [(4, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(5, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(6, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(7, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(8, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(9, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(10, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 1 [(11, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      -- it "DivMod 1" $ do
      --   -- output     | input
      --   -- rrrrrrrruu   rrrrrrrruu
      --   -- 0123456789   0123456789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         performDivMod x y
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- dividend = divisor * quotient + remainder
      --       -- \$18 = $19 * $8 + $9
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(19, 1)])
      --                             (Poly.buildEither 0 [(8, 1)])
      --                             (Poly.buildEither 0 [(18, 1), (9, -1)])
      --                         ]
      --       -- 0 ≤ remainder ($9) < divisor ($19)
      --       -- diff ($20) = $19 - $9
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(17, -16)])
      --                             (Poly.buildEither 0 [(7, 1)])
      --                             (Poly.buildEither 0 [(9, 1), (19, -1), (20, 1)])
      --                         ]
      --       -- diff != 0
      --       -- \$20 * $21 = 1
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(20, 1)])
      --                             (Poly.buildEither 0 [(21, 1)])
      --                             (Poly.buildEither 1 [])
      --                         ]
      --       -- divisor != 0
      --       -- \$22 * $19 = 1
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(22, 1)])
      --                             (Poly.buildEither 0 [(19, 1)])
      --                             (Poly.buildEither 1 [])
      --                         ]
      -- it "DivMod 2" $ do
      --   -- output     | input
      --   -- rrrrrrrruu   rrrrrrrruu
      --   -- 0123456789   0123456789
      --   let program = do
      --         x <- inputUInt @4 Public
      --         y <- inputUInt @4 Public
      --         assertDivMod x 2 7 y -- x = 2 * 7 + y
      --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
      --     Left err -> expectationFailure (show err)
      --     Right r1cs -> do
      --       -- dividend = 2 * 7 + remainder
      --       -- \$18 = 14 + $9
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 14 [(9, 1), (8, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       -- 0 ≤ remainder ($9) < 2
      --       -- diff ($10) = 2 - $9
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 2 [(9, -1), (10, -1)])
      --                             (Poly.buildEither 1 [])
      --                             (Poly.buildEither 0 [])
      --                         ]
      --       toR1Cs r1cs
      --         `shouldContain` [ R1C
      --                             (Poly.buildEither 0 [(10, 1)])
      --                             (Poly.buildEither 0 [(11, 1)])
      --                             (Poly.buildEither 1 [])
      --                         ]