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

tests :: SpecWith ()
tests = do
  describe "Compilation" $ do
    it "Bit tests on unsigned integers" $ do
      case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile example1 of
        Left err -> expectationFailure (show err)
        Right r1cs -> do
          -- x !!! 0
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(0, -1), (16, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- x !!! 1
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(1, -1), (17, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- x !!! 2
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(2, -1), (18, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- x !!! 3
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(3, -1), (19, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- x !!! 5
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(4, -1), (1, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- x !!! (-1)
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(5, -1), (3, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- y !!! 1
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(6, -1), (14, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- y !!! (-1)
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(7, -1), (15, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- y !!! 3
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(8, -1), (13, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]
          -- y !!! 13
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(9, -1), (6, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]

    it "Bit tests on compound expresions with bitwise operation" $ do
      case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile Basic.bitwise of
        Left err -> expectationFailure (show err)
        Right r1cs -> do
          -- (x .&. y) !!! 0
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(6, 1)])
                                (Poly.buildEither 0 [(10, 1)])
                                (Poly.buildEither 0 [(0, 1)])
                            ]
          -- (x .|. y) !!! 1
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 1 [(7, -1)])
                                (Poly.buildEither 0 [(11, 1)])
                                (Poly.buildEither 0 [(1, 1), (7, -1)])
                            ]
          -- (x .^. y) !!! 2
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 1 [(8, -2)])
                                (Poly.buildEither 1 [(12, 1)])
                                (Poly.buildEither 1 [(2, 1), (8, -3)])
                            ]
          -- x !!! 3
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(9, 1)])
                                (Poly.buildEither 0 [(13, 1)])
                                (Poly.buildEither 0 [(3, 1)])
                            ]

    it "Addition on unsigned integers 0" $ do
      let program = do
            x <- inputUInt @4
            y <- inputUInt @4
            return (x + y)
      case Compiler.asGF181N $ Compiler.toR1CS <$> Compiler.compile program of
        Left err -> expectationFailure (show err)
        Right r1cs -> do
          -- x + y - carry = output
          toR1Cs r1cs
            `shouldContain` [ R1C
                                (Poly.buildEither 0 [(0, -1), (1, 1), (2, 1)])
                                (Poly.buildEither 1 [])
                                (Poly.buildEither 0 [])
                            ]

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