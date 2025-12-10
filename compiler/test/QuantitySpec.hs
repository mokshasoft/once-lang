module QuantitySpec (quantityTests) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit

import Once.Quantity
import Once.Syntax
import Once.TypeCheck

instance Arbitrary Quantity where
  arbitrary = elements [Zero, One, Omega]

quantityTests :: TestTree
quantityTests = testGroup "Quantity"
  [ testGroup "qAdd semiring laws"
      [ testProperty "zero is left identity" $
          \r -> qAdd Zero r === r
      , testProperty "zero is right identity" $
          \r -> qAdd r Zero === r
      , testProperty "associativity" $
          \a b c -> qAdd a (qAdd b c) === qAdd (qAdd a b) c
      , testProperty "commutativity" $
          \a b -> qAdd a b === qAdd b a
      ]
  , testGroup "qMul semiring laws"
      [ testProperty "one is left identity" $
          \r -> qMul One r === r
      , testProperty "one is right identity" $
          \r -> qMul r One === r
      , testProperty "zero is left annihilator" $
          \r -> qMul Zero r === Zero
      , testProperty "zero is right annihilator" $
          \r -> qMul r Zero === Zero
      , testProperty "associativity" $
          \a b c -> qMul a (qMul b c) === qMul (qMul a b) c
      , testProperty "commutativity" $
          \a b -> qMul a b === qMul b a
      ]
  , testGroup "distributivity"
      [ testProperty "left distributivity" $
          \a b c -> qMul a (qAdd b c) === qAdd (qMul a b) (qMul a c)
      , testProperty "right distributivity" $
          \a b c -> qMul (qAdd a b) c === qAdd (qMul a c) (qMul b c)
      ]
  , testGroup "QTT enforcement (Phase 12)"
      [ testCase "linear variable used exactly once passes" $
          -- \x -> x  (x used once, linear is satisfied)
          let expr = ELam "x" (EVar "x")
              mod' = Module
                [ TypeSig "f" (STArrow (STVar "A") (STVar "A"))
                , FunDef "f" Nothing expr
                ]
          in case checkModule mod' of
               Right () -> pure ()
               Left err -> assertFailure $ "Expected success but got: " ++ show err

      , testCase "linear variable used twice fails" $
          -- \x -> (x, x)  (x used twice, violates linear)
          let expr = ELam "x" (EPair (EVar "x") (EVar "x"))
              mod' = Module
                [ TypeSig "f" (STArrow (STVar "A") (STProduct (STVar "A") (STVar "A")))
                , FunDef "f" Nothing expr
                ]
          in case checkModule mod' of
               Left (LinearUsedMultiple "x" 2) -> pure ()
               Left err -> assertFailure $ "Expected LinearUsedMultiple but got: " ++ show err
               Right () -> assertFailure "Expected failure but got success"

      , testCase "linear variable unused fails" $
          -- \x -> ()  (x not used, violates linear)
          let expr = ELam "x" EUnit
              mod' = Module
                [ TypeSig "f" (STArrow (STVar "A") STUnit)
                , FunDef "f" Nothing expr
                ]
          in case checkModule mod' of
               Left (LinearUnused "x") -> pure ()
               Left err -> assertFailure $ "Expected LinearUnused but got: " ++ show err
               Right () -> assertFailure "Expected failure but got success"

      , testCase "point-free composition passes (no lambdas)" $
          -- pair snd fst  (point-free, no bound variables to check)
          let expr = EApp (EApp (EVar "pair") (EVar "snd")) (EVar "fst")
              mod' = Module
                [ TypeSig "swap" (STArrow (STProduct (STVar "A") (STVar "B"))
                                          (STProduct (STVar "B") (STVar "A")))
                , FunDef "swap" Nothing expr
                ]
          in case checkModule mod' of
               Right () -> pure ()
               Left err -> assertFailure $ "Expected success but got: " ++ show err
      ]
  ]
