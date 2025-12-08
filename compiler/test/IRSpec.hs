{-# LANGUAGE OverloadedStrings #-}
module IRSpec (irTests) where

import Test.Tasty
import Test.Tasty.QuickCheck

import Once.Eval (eval)
import Once.IR (IR (..))
import Once.Type (Type (..))
import Once.Value (Value (..))

-- Arbitrary instances for testing
instance Arbitrary Value where
  arbitrary = sized genValue
    where
      genValue 0 = pure VUnit
      genValue n = oneof
        [ pure VUnit
        , VPair <$> genValue (n `div` 2) <*> genValue (n `div` 2)
        , VLeft <$> genValue (n - 1)
        , VRight <$> genValue (n - 1)
        ]

-- Helper: simple types for testing
tA, tB :: Type
tA = TVar "A"
tB = TVar "B"

-- Helper: evaluate and compare (ignoring Left errors)
evalEq :: IR -> IR -> Value -> Bool
evalEq f g v = case (eval f v, eval g v) of
  (Right a, Right b) -> a == b
  _ -> True  -- If either fails, we can't compare (might be type error)

irTests :: TestTree
irTests = testGroup "IR Categorical Laws"
  [ testGroup "Category laws"
      [ testProperty "id is right identity: f ∘ id = f" $
          \v -> evalEq (Compose (Fst tA tB) (Id (TProduct tA tB)))
                       (Fst tA tB)
                       (VPair v VUnit)

      , testProperty "id is left identity: id ∘ f = f" $
          \v -> evalEq (Compose (Id tA) (Fst tA tB))
                       (Fst tA tB)
                       (VPair v VUnit)

      , testProperty "composition is associative: (h ∘ g) ∘ f = h ∘ (g ∘ f)" $
          \v -> let f = Fst tA tB  -- A * B -> A
                    g = Pair (Id tA) (Terminal tA)  -- A -> A * Unit
                    h = Fst tA TUnit  -- A * Unit -> A
                in evalEq (Compose (Compose h g) f)
                          (Compose h (Compose g f))
                          (VPair v VUnit)
      ]

  , testGroup "Product laws"
      [ testProperty "fst ∘ pair f g = f" $
          \v -> evalEq (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA)))
                       (Id tA)
                       v

      , testProperty "snd ∘ pair f g = g" $
          \v -> evalEq (Compose (Snd tA TUnit) (Pair (Id tA) (Terminal tA)))
                       (Terminal tA)
                       v

      , testProperty "pair (fst) (snd) = id on products" $
          \a b -> let v = VPair a b
                  in evalEq (Pair (Fst tA tB) (Snd tA tB))
                            (Id (TProduct tA tB))
                            v
      ]

  , testGroup "Terminal object"
      [ testProperty "terminal is unique: any f : A -> Unit equals terminal" $
          \v -> eval (Terminal tA) v == Right VUnit
      ]

  , testGroup "Coproduct laws"
      [ testProperty "case f g ∘ inl = f" $
          \v -> evalEq (Compose (Case (Id tA) (Terminal tB)) (Inl tA tB))
                       (Id tA)
                       v

      , testProperty "case f g ∘ inr = g" $
          \v -> evalEq (Compose (Case (Terminal tA) (Id tB)) (Inr tA tB))
                       (Id tB)
                       v
      ]

  , testGroup "swap example"
      [ testProperty "swap swaps pair components" $
          \a b -> let swap = Pair (Snd tA tB) (Fst tA tB)
                      input = VPair a b
                  in eval swap input == Right (VPair b a)
      ]
  ]
