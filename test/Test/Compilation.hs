{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Test.Compilation (tests) where

import qualified Basic
import Keelung
import qualified Keelung.Compiler as Compiler
import qualified Keelung.Constraint.Polynomial as Poly
import Keelung.Constraint.R1C (R1C (..))
import Keelung.Constraint.R1CS (toR1Cs)
import Test.Hspec
import Control.Monad

tests :: SpecWith ()
tests = do
  describe "Compilation" $ do
    -- it "Bit tests on unsigned integers" $ do
    --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile example1 of
    --     Left err -> expectationFailure (show err)
    --     Right r1cs -> do
    --       -- x !!! 0
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(0, -1), (16, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- x !!! 1
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(1, -1), (17, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- x !!! 2
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(2, -1), (18, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- x !!! 3
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(3, -1), (19, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- x !!! 5
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(4, -1), (1, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- x !!! (-1)
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(5, -1), (3, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- y !!! 1
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(6, -1), (14, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- y !!! (-1)
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(7, -1), (15, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- y !!! 3
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(8, -1), (13, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]
    --       -- y !!! 13
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(9, -1), (6, 1)])
    --                             (Poly.buildEither 1 [])
    --                             (Poly.buildEither 0 [])
    --                         ]

    -- it "Bit tests on compound expresions with bitwise operation" $ do
    --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile Basic.bitwise of
    --     Left err -> expectationFailure (show err)
    --     Right r1cs -> do
    --       -- (x .&. y) !!! 0
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(6, 1)])
    --                             (Poly.buildEither 0 [(10, 1)])
    --                             (Poly.buildEither 0 [(0, 1)])
    --                         ]
    --       -- (x .|. y) !!! 1
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 1 [(7, -1)])
    --                             (Poly.buildEither 0 [(11, 1)])
    --                             (Poly.buildEither 0 [(1, 1), (7, -1)])
    --                         ]
    --       -- (x .^. y) !!! 2
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 1 [(8, -2)])
    --                             (Poly.buildEither 1 [(12, 1)])
    --                             (Poly.buildEither 1 [(2, 1), (8, -3)])
    --                         ]
    --       -- not x
    --       toR1Cs r1cs
    --         `shouldContain` [ R1C
    --                             (Poly.buildEither 0 [(9, 1)])
    --                             (Poly.buildEither 0 [(13, 1)])
    --                             (Poly.buildEither 0 [(3, 1)])
    --                         ]

    describe "Unsigned Integer" $ do
      it "Bit test / Value" $ do
        -- 0011
        let program = do
              let c = 3 :: UInt 4
              return $ toArray [c !!! (-1), c !!! 0, c !!! 1, c !!! 2, c !!! 3, c !!! 4]
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C -- c !!! (-1)
                                  (Poly.buildEither 0 [(0, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 []),
                                R1C -- c !!! 0
                                  (Poly.buildEither 1 [(1, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 []),
                                R1C -- c !!! 1
                                  (Poly.buildEither 1 [(2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 []),
                                R1C -- c !!! 2
                                  (Poly.buildEither 0 [(3, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 []),
                                R1C -- c !!! 3
                                  (Poly.buildEither 0 [(4, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 []),
                                R1C -- c !!! 4
                                  (Poly.buildEither 0 [(5, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "Bit test / Input variable" $ do
        -- ooooooibbbb
        -- 01234567890
        let program = do
              x <- inputUInt @4
              return $ toArray [x !!! (-1), x !!! 0, x !!! 1, x !!! 2, x !!! 3, x !!! 4]
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- x !!! (-1) == x !!! 3
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1), (4, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 3
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(0, -1), (10, 1)])
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
                                  (Poly.buildEither 0 [(1, -1), (7, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 1
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(2, -1), (8, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]
            -- x !!! 2
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, -1), (9, 1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "Bit test / AND" $ do
        -- oii bbbb bbbb
        -- 012 3456 7890
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ (x .&. y) !!! 0
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, 1)])
                                  (Poly.buildEither 0 [(7, 1)])
                                  (Poly.buildEither 0 [(0, 1)])
                              ]

      it "Bit test / OR" $ do
        -- oii bbbb bbbb
        -- 012 3456 7890
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ (x .|. y) !!! 0
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - x[0]) * y[0] = output - x[0]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(3, -1)])
                                  (Poly.buildEither 0 [(7, 1)])
                                  (Poly.buildEither 0 [(0, 1), (3, -1)])
                              ]

      it "Bit test / XOR" $ do
        -- oii bbbb bbbb
        -- 012 3456 7890
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ (x .^. y) !!! 0
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - 2x[0]) * (1 + y[0]) = 1 + output - 3x[0]
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(3, -2)])
                                  (Poly.buildEither 1 [(7, 1)])
                                  (Poly.buildEither 1 [(0, 1), (3, -3)])
                              ]

      it "Bit test / NOT" $ do
        -- oi bbbb
        -- 01 2345 
        let program = do
              x <- inputUInt @4
              return $ complement x !!! 0
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 1 [(0, -1), (2, -1)])
                                  (Poly.buildEither 1 [])
                                  (Poly.buildEither 0 [])
                              ]

      it "AND" $ do 
        -- oii bbbb bbbb bbbb
        -- 012 3456 7890 1234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .&. y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            toR1Cs r1cs
              `shouldContain` [ R1C
                                  (Poly.buildEither 0 [(3, 1)])
                                  (Poly.buildEither 0 [(7, 1)])
                                  (Poly.buildEither 0 [(11, 1)])
                              ]

      it "OR 1" $ do 
        -- oii bbbb bbbb bbbb
        -- 012 3456 7890 1234
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
                                    (Poly.buildEither 1 [(3 + i, -1)])
                                    (Poly.buildEither 0 [(7 + i, 1)])
                                    (Poly.buildEither 0 [(11 + i, 1), (3 + i, -1)])
                                ]

      it "OR 2" $ do 
        -- oii bbbb bbbb bbbb bbbb
        -- 012 3456 7890 1234 5678
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .|. y .|. x
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- let temp = x .|. y
            -- (1 - x[i]) * y[i] = temp[i] - x[i]
            forM_ [0 .. 3] $ \i -> 
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(3 + i, -1)])
                                    (Poly.buildEither 0 [(7 + i, 1)])
                                    (Poly.buildEither 0 [(15 + i, 1), (3 + i, -1)])
                                ]
            -- (1 - temp[i]) * x[i] = output[i] - temp[i]
            forM_ [0 .. 3] $ \i -> 
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(15 + i, -1)])
                                    (Poly.buildEither 0 [(3 + i, 1)])
                                    (Poly.buildEither 0 [(11 + i, 1), (15 + i, -1)])
                                ]

      it "XOR" $ do 
        -- oii bbbb bbbb bbbb
        -- 012 3456 7890 1234
        let program = do
              x <- inputUInt @4
              y <- inputUInt @4
              return $ x .^. y
        case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
          Left err -> expectationFailure (show err)
          Right r1cs -> do
            -- (1 - 2x[i]) * y[i] = out[i] - 3x[i]
            forM_ [0 .. 3] $ \i -> 
              toR1Cs r1cs
                `shouldContain` [ R1C
                                    (Poly.buildEither 1 [(3 + i, -2)])
                                    (Poly.buildEither 1 [(7 + i, 1)])
                                    (Poly.buildEither 1 [(11 + i, 1), (3 + i, -3)])
                                ]
--   it "Addition 0" $ do
--     let program = do
--           x <- inputUInt @4
--           y <- inputUInt @4
--           return (x + y)
--     case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
--       Left err -> expectationFailure (show err)
--       Right r1cs -> do
--         -- x + y - carry = output
--         toR1Cs r1cs
--           `shouldContain` [ R1C
--                               (Poly.buildEither 0 [(6, 16)])
--                               (Poly.buildEither 0 [(10, 1)])
--                               (Poly.buildEither 0 [(0, 1), (1, -1), (2, -1)])
--                           ]

--   it "Addition 1" $ do
--     let program = do
--           x <- inputUInt @4
--           y <- inputUInt @4
--           return (x + y + x)
--     case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
--       Left err -> expectationFailure (show err)
--       Right r1cs -> do
--         -- x + y - carryXY = temp
--         -- temp + x - carryTempX = output
--         toR1Cs r1cs
--           `shouldContain` [ R1C
--                               (Poly.buildEither 0 [(6, 16)])
--                               (Poly.buildEither 0 [(10, 1)])
--                               (Poly.buildEither 0 [(11, 1), (1, -1), (2, -1)]),
--                             R1C
--                               (Poly.buildEither 0 [(12, 16)])
--                               (Poly.buildEither 0 [(6, 1)])
--                               (Poly.buildEither 0 [(0, 1), (1, -1), (11, -1)])
--                           ]

--   it "Subtraction 0" $ do
--     let program = do
--           x <- inputUInt @4
--           y <- inputUInt @4
--           return (x - y)
--     case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
--       Left err -> expectationFailure (show err)
--       Right r1cs -> do
--         -- x - y - carry = output
--         toR1Cs r1cs
--           `shouldContain` [ R1C
--                               (Poly.buildEither 0 [(6, 16)])
--                               (Poly.buildEither 0 [(10, 1)])
--                               (Poly.buildEither 0 [(0, 1), (1, -1), (2, 1)])
--                           ]

--   -- it "AND 0" $ do
--   --   let program = do
--   --         x <- inputUInt @4
--   --         y <- inputUInt @4
--   --         return (x `And` y)
--   --   case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
--   --     Left err -> expectationFailure (show err)
--   --     Right r1cs -> do
--   --       -- x - y - carry = output
--   --       toR1Cs r1cs
--   --         `shouldContain` [ R1C
--   --                             (Poly.buildEither 0 [(1, 1), (2, -1)])
--   --                             (Poly.buildEither 0 [(0, 1)])
--   --                             (Poly.buildEither 0 []),
--   --                           R1C
--   --                             (Poly.buildEither 0 [(1, 1), (2, -1)])
--   --                             (Poly.buildEither 0 [(11, 1)])
--   --                             (Poly.buildEither 1 [(0, -1)])
--   --                         ]

--   it "Equality 0" $ do
--     let program = do
--           x <- inputUInt @4
--           y <- inputUInt @4
--           return (x `eq` y)
--     case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
--       Left err -> expectationFailure (show err)
--       Right r1cs -> do
--         -- x - y - carry = output
--         toR1Cs r1cs
--           `shouldContain` [ R1C
--                               (Poly.buildEither 0 [(1, 1), (2, -1)])
--                               (Poly.buildEither 0 [(0, 1)])
--                               (Poly.buildEither 0 []),
--                             R1C
--                               (Poly.buildEither 0 [(1, 1), (2, -1)])
--                               (Poly.buildEither 0 [(11, 1)])
--                               (Poly.buildEither 1 [(0, -1)])
--                           ]

example1 :: Comp (Arr Boolean)
example1 = do
  x <- inputUInt @4
  _x2 <- inputUInt @4
  y <- inputUInt @3
  return $
    toArray
      [ x !!! 0,
        x !!! 1,
        x !!! 2,
        x !!! 3,
        x !!! 5,
        x !!! (-1),
        y !!! 1,
        y !!! (-1),
        y !!! 3,
        y !!! 13
      ]