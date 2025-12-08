module QuantitySpec (quantityTests) where

import Test.Tasty
import Test.Tasty.QuickCheck

import Once.Quantity

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
  ]
