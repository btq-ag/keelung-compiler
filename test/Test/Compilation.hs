{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation (run, tests) where

-- import qualified Basic

import Control.Monad
import Keelung hiding (run)
import Keelung.Compiler qualified as Compiler
import Keelung.Constraint.Polynomial qualified as Poly
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (toR1Cs)
import Test.Hspec

run :: IO ()
run = hspec tests

tests :: SpecWith ()
tests = do
  describe "Compilation" $ do
    describe "Assertion" $ do
        it "Rewriting" $ do
          let program = do
                xs <- inputs 4
                ys <- inputs 4
                assert (sum xs `eq` sum (ys :: Arr Field))
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

    describe "Unsigned Integer" $ do
      it "Bit test / Value" $ do
        -- 0011
        let program = do
              let c = 3 :: UInt 4
              return $ toArray [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- c !!! (-1)
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- c !!! 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- c !!! 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- c !!! 2
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- c !!! 3
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(4, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- c !!! 4
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(5, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
      it "Bit test / Input variable" $ do
        -- oooooobbbbi
        -- 01234567890
        let program = do
              x <- inputUInt @4
              return $ toArray [x !!! (-1), x !!! 0, x !!! 1, x !!! 2, x !!! 3, x !!! 4]
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x !!! (-1) == x !!! (-3)
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1), (4, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! (-1)
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1), (9, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 0 == x !!! 4
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, -1), (5, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, -1), (6, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(2, -1), (7, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 2
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, -1), (8, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "Bit test / AND" $ do
        -- output | input
        -- b        rrrrrrrruu
        -- 0        12345678901
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ (x .&. y) !!! 0
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, 1)])
                                  (Poly.buildEither 0 [(5, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                              ]

      it "Bit test / OR" $ do
        -- output | input
        -- b        rrrrrrrruu
        -- 0        12345678901
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ (x .|. y) !!! 0
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - x[0]) * y[0] = out[0] - x[0]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(1, -1)])
                                  (Poly.buildEither 0 [(5, 1)])
                                  (Poly.buildEither 0 [(0, 1), (1, -1)])
                              ]

      it "Bit test / BtoU" $ do
        -- output | input | intermediate
        -- bbbb     b       rrrrrrrrrrrrrrrruuuu
        -- 0123     4       56789012345678901234
        let program = do
              x <- input
              let u = BtoU x :: UInt 4
              return $ toArray [u !!! 0, u !!! 1, u !!! 2, u !!! 3]
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- u !!! 0 == x
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1), (4, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- u !!! i == 0
            forM_ [1 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(i, -1)])
                                    (Poly.buildEither 1 [])
                                    (Poly.buildEither 0 [])
                                ]

      it "AND 0" $ do
        -- output | input
        -- rrrru    rrrrrrrruu
        -- 01234    5678901234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .&. y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x[i] * y[i] = out[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(5 + i, 1)])
                                    (Poly.buildEither 0 [(9 + i, 1)])
                                    (Poly.buildEither 0 [(0 + i, 1)])
                                ]

      it "AND 1" $ do
        -- output | input      | intermediate
        -- rrrru    rrrrrrrruu   rrrru
        -- 01234    5678901234   56789
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .&. y .&. x
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x[i] * y[i] = temp[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(5 + i, 1)])
                                    (Poly.buildEither 0 [(9 + i, 1)])
                                    (Poly.buildEither 0 [(15 + i, 1)])
                                ]
            -- temp[i] * x[i] = out[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(15 + i, 1)])
                                    (Poly.buildEither 0 [(5 + i, 1)])
                                    (Poly.buildEither 0 [(0 + i, 1)])
                                ]

      it "AND 2" $ do
        -- output
        -- rrrru
        -- 01234
        let program = do
              let x = 3 :: UInt 4
              let y = 5 :: UInt 4
              return $ x .&. y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- out[0] = 1 * 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(0, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- out[1] = 1 * 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- out[2] = 0 * 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- out[3] = 0 * 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "OR 0" $ do
        -- output | input
        -- rrrru    rrrrrrrruu
        -- 01234    5678901234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .|. y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - x[i]) * y[i] = out[i] - x[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(5 + i, -1)])
                                    (Poly.buildEither 0 [(9 + i, 1)])
                                    (Poly.buildEither 0 [(0 + i, 1), (5 + i, -1)])
                                ]

      it "OR 1" $ do
        -- output | input      | intermediate
        -- rrrru    rrrrrrrruu   rrrru
        -- 01234    5678901234   56789
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .|. y .|. x
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - x[i]) * y[i] = temp[i] - x[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(5 + i, -1)])
                                    (Poly.buildEither 0 [(9 + i, 1)])
                                    (Poly.buildEither 0 [(15 + i, 1), (5 + i, -1)])
                                ]
            -- (1 - temp[i]) * x[i] = out[i] - temp[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(15 + i, -1)])
                                    (Poly.buildEither 0 [(5 + i, 1)])
                                    (Poly.buildEither 0 [(0 + i, 1), (15 + i, -1)])
                                ]

      it "OR 2" $ do
        -- output | input
        -- rrrru    rrrru
        -- 01234    56789
        let program = do
              x <- inputUInt @4
              let y = 3
              return $ x .|. y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - x[0]) * 1 = out[0] - x[0] => out[0] = 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(0, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- (1 - x[1]) * 1 = out[1] - x[1] => out[1] = 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- (1 - x[2]) * 0 = out[2] - x[2] => out[2] = x[2]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(2, -1), (7, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- (1 - x[3]) * 0 = out[3] - x[3] => out[3] = x[3]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, -1), (8, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "XOR 0" $ do
        -- output | input           | intermediate
        -- rrrru    rrrrrrrrrrrruuu   rrrru
        -- 01234    567890123456789   01234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              z <- inputUInt @4
              return $ x .^. y .^. z
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - 2x[i]) * (1 + y[i]) = (1 + temp[i] - 3x[i])
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(5 + i, -2)])
                                    (Poly.buildEither 1 [(9 + i, 1)])
                                    (Poly.buildEither 1 [(20 + i, 1), (5 + i, -3)])
                                ]
            -- (1 - 2temp[i]) * (1 + z[i]) = (1 + out[i] - 32temp[i])
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(20 + i, -2)])
                                    (Poly.buildEither 1 [(13 + i, 1)])
                                    (Poly.buildEither 1 [(0 + i, 1), (20 + i, -3)])
                                ]

      it "NOT 0" $ do
        -- output
        -- rrrru
        -- 01234
        let program = do
              let x = 3 :: UInt 4
              return $ complement x
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- 1 = out[i]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(3, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "NOT 1" $ do
        -- output | input
        -- rrrru    rrrru
        -- 01234    56789
        let program = do
              x <- inputUInt @4
              return $ complement x
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- 1 - x[i] = out[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(5 + i, -1), (0 + i, -1)])
                                    (Poly.buildEither 1 [])
                                    (Poly.buildEither 0 [])
                                ]

      it "EQ 0" $ do
        -- output | input      | intermediate
        -- b        rrrrrrrruu   m
        -- 0        1234567890   1
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x `eq` y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            --  (x - y) * m = 1 - out
            --  (x - y) * out = 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(9, 1), (10, -1)])
                                  (Poly.buildEither 0 [(11, 1)])
                                  (Poly.buildEither 1 [(0, -1)])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(9, 1), (10, -1)])
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 0 [])
                              ]

      it "EQ 1" $ do
        -- output | input | intermediate
        -- b        rrrru   m
        -- 0        12345   6
        let program = do
              x <- inputUInt @4
              return $ x `eq` 3
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            --  (x - 3) * m = 1 - out
            --  (x - 3) * out = 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither (-3) [(5, 1)])
                                  (Poly.buildEither 0 [(6, 1)])
                                  (Poly.buildEither 1 [(0, -1)])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither (-3) [(5, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 0 [])
                              ]

      -- it "NEQ 0" $ do
      --   -- output | input      | intermediate
      --   -- b        rrrrrrrruu   m
      --   -- 0        1234567890   1
      --   let program = do
      --         x <- inputUInt @4
      --         y <- inputUInt @4
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

      it "ADD 0" $ do
        -- output | input
        -- rrrru    rrrrrrrruu
        -- 01234    5678901234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return (x + y)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (out - x - y)
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(8, 16)])
                                  (Poly.buildEither 0 [(12, 1)])
                                  (Poly.buildEither 0 [(4, 1), (13, -1), (14, -1)])
                              ]

      it "ADD 1" $ do
        -- output | input      | intermediate
        -- rrrru    rrrrrrrruu   rrrru
        -- 01234    5678901234   56789
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return (x + y + x)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (temp - x - y)
            -- NOTE: 'temp' will be moved from $19 to $16 after variable renumbering
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(8, 16)])
                                  (Poly.buildEither 0 [(12, 1)])
                                  (Poly.buildEither 0 [(16, 1), (13, -1), (14, -1)])
                              ]
            -- (2ⁿ * tempₙ₋₁) * (xₙ₋₁) = (out - temp - x)
            -- NOTE: 'tempₙ₋₁' will be moved from $18 to $15 after variable renumbering
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(15, 16)])
                                  (Poly.buildEither 0 [(8, 1)])
                                  (Poly.buildEither 0 [(4, 1), (16, -1), (13, -1)])
                              ]

      it "ADD 2" $ do
        -- output | input      | intermediate
        -- rrrru    rrrrrrrruu   rrrru
        -- 01234    5678901234   56789
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              let z = 3
              return (x + y + z)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (temp - x - y)
            -- NOTE: 'temp' will be moved from $19 to $15 after variable renumbering
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(8, 16)])
                                  (Poly.buildEither 0 [(12, 1)])
                                  (Poly.buildEither 0 [(15, 1), (13, -1), (14, -1)])
                              ]
            -- (2ⁿ * tempₙ₋₁) * (3ₙ₋₁) = (out - temp - 3)
            -- => 0 = out - temp - 3
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither (-3) [(4, 1), (15, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "SUB 0" $ do
        -- output | input           | intermediate
        -- rrrru    rrrrrrrrrrrruuu   rrrru
        -- 01234    567890123456789   01234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              z <- inputUInt @4
              return (x - y - z)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (2ⁿ * xₙ₋₁) * (yₙ₋₁) = (temp - x + y)
            -- NOTE: 'temp' will be moved from $24 to $21 after variable renumbering
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(8, 16)])
                                  (Poly.buildEither 0 [(12, 1)])
                                  (Poly.buildEither 0 [(21, 1), (17, -1), (18, 1)])
                              ]
            -- (2ⁿ * tempₙ₋₁) * (zₙ₋₁) = (out - temp + z)
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(20, 16)])
                                  (Poly.buildEither 0 [(16, 1)])
                                  (Poly.buildEither 0 [(4, 1), (21, -1), (19, 1)])
                              ]

      it "MUL 0" $ do
        -- output | input      | intermediate
        -- rrrru    rrrrrrrruu   u
        -- 01234    5678901234   5
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return (x * y)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x * y = out + 2ⁿ * quotient
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(13, 1)])
                                  (Poly.buildEither 0 [(14, 1)])
                                  (Poly.buildEither 0 [(4, 1), (15, 16)])
                              ]

      it "MUL 1" $ do
        -- output | input           | intermediate
        -- rrrru    rrrrrrrrrrrruuu   utqqq
        -- 01234    567890123456789   01234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              z <- inputUInt @4
              return (x * y * z * 3)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x * y = temp1 + 2ⁿ * quotient1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(17, 1)])
                                  (Poly.buildEither 0 [(18, 1)])
                                  (Poly.buildEither 0 [(21, 1), (22, 16)])
                              ]
            -- temp * z = temp2 + 2ⁿ * quotient2
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(21, 1)])
                                  (Poly.buildEither 0 [(19, 1)])
                                  (Poly.buildEither 0 [(20, 1), (23, 16)])
                              ]
            -- temp2 * 3 = out + 2ⁿ * quotient3
            -- => 0 = out + 2ⁿ * quotient3 - temp2 * 3
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(4, -1), (24, -16), (20, 3)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
      it "ARITH 0" $ do
        -- output | input           | intermediate
        -- rrrru    rrrrrrrrrrrruuu   rutqr
        -- 01234    567890123456789   01234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              z <- inputUInt @4
              return (x * y + z - 3)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x * y = temp1 + 2ⁿ * quotient
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(17, 1)])
                                  (Poly.buildEither 0 [(18, 1)])
                                  (Poly.buildEither 0 [(22, 1), (23, 16)])
                              ]
            -- (2ⁿ * temp1ₙ₋₁) * (zₙ₋₁) = (temp2 - temp1 - z)
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(20, 16)])
                                  (Poly.buildEither 0 [(16, 1)])
                                  (Poly.buildEither 0 [(21, 1), (22, -1), (19, -1)])
                              ]
            -- (2ⁿ * temp2ₙ₋₁) * (3ₙ₋₁) = (out - temp2 + 3)
            -- => (out - temp2 + 3) = 0
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither (-3) [(4, -1), (21, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "ROL 0" $ do
        -- output | input
        -- rrrru    rrrru
        -- 01234    56789
        let program = do
              x <- inputUInt @4
              return $ rotate x 1
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x[i] = out[i + i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(i + 5, 1), ((i + 1) `mod` 4, -1)])
                                    (Poly.buildEither 1 [])
                                    (Poly.buildEither 0 [])
                                ]

      it "ROL 1" $ do
        -- output
        -- rrrru
        -- 01234
        let program = do
              let x = 3 :: UInt 4
              return $ rotate x (-1)
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(0, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(3, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
      it "ROL 2" $ do
        -- output | input
        -- rrrru    rrrru
        -- 01234    56789
        let program = do
              x <- inputUInt @4
              return $ rotate (rotate x (-1)) 1
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x[i] = out[i]
            forM_ [0 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(i + 5, 1), (i, -1)])
                                    (Poly.buildEither 1 [])
                                    (Poly.buildEither 0 [])
                                ]

      it "SHL 0" $ do
        -- output | input
        -- rrrru    rrrru
        -- 01234    56789
        let program = do
              x <- inputUInt @4
              return $ shift x 1
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- 0 = out[0]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x[i] = out[i + i]
            forM_ [1 .. 3] $ \i ->
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 0 [(i + 5 - 1, 1), (i, -1)])
                                    (Poly.buildEither 1 [])
                                    (Poly.buildEither 0 [])
                                ]

      it "SHL 1" $ do
        -- output
        -- rrrrrrrrrrrruuu
        -- 012345678901234
        let program = do
              let x = 3 :: UInt 4
              return $ toArray [shift x 1, shift x (-1), shift x 3]
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(4, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(5, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(6, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(7, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(8, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(9, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(10, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(11, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
      it "DivMod" $ do
        -- output     | input
        -- rrrrrrrruu   rrrrrrrruu
        -- 0123456789   0123456789
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              performDivMod x y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- dividend = divisor * quotient + remainder
            -- \$18 = $19 * $8 + $9
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(19, 1)])
                                  (Poly.buildEither 0 [(8, 1)])
                                  (Poly.buildEither 0 [(18, 1), (9, -1)])
                              ]
            -- 0 ≤ remainder ($9) < divisor ($19)
            -- remainder + 1 ($21) ≤ divisor ($19)
            -- temp = diviser - remainder - 1 ($22)
            -- 1 + $9 - $21 = 0
            -- \$22 = $19 - $21 - 16$17 * $20
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(17, -16)])
                                  (Poly.buildEither 0 [(20, 1)])
                                  (Poly.buildEither 0 [(19, 1), (21, -1), (22, -1)])
                              ]
            -- divisor != 0
            -- \$23 * $19 = 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(23, 1)])
                                  (Poly.buildEither 0 [(19, 1)])
                                  (Poly.buildEither 1 [])
                              ]