module OptimizeSpec (optimizeTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Once.Eval (eval)
import Once.IR (IR (..))
import Once.Optimize (optimize)
import Once.Type (Type (..))
import Once.Value (Value (..))

-- Arbitrary instances (same as IRSpec)
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

-- Helper types
tA, tB :: Type
tA = TVar "A"
tB = TVar "B"

optimizeTests :: TestTree
optimizeTests = testGroup "Optimize"
  [ testGroup "Identity elimination"
      [ testCase "f ∘ id = f" $
          optimize (Compose (Fst tA tB) (Id (TProduct tA tB)))
            @?= Fst tA tB

      , testCase "id ∘ f = f" $
          optimize (Compose (Id tA) (Fst tA tB))
            @?= Fst tA tB

      , testCase "id ∘ id = id" $
          optimize (Compose (Id tA) (Id tA))
            @?= Id tA
      ]

  , testGroup "Product laws"
      [ testCase "fst ∘ pair f g = f" $
          optimize (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA)))
            @?= Id tA

      , testCase "snd ∘ pair f g = g" $
          optimize (Compose (Snd tA tB) (Pair (Id tA) (Terminal tA)))
            @?= Terminal tA

      , testCase "pair fst snd = id" $
          optimize (Pair (Fst tA tB) (Snd tA tB))
            @?= Id (TProduct tA tB)
      ]

  , testGroup "Coproduct laws"
      [ testCase "case f g ∘ inl = f" $
          optimize (Compose (Case (Id tA) (Terminal tB)) (Inl tA tB))
            @?= Id tA

      , testCase "case f g ∘ inr = g" $
          optimize (Compose (Case (Terminal tA) (Id tB)) (Inr tA tB))
            @?= Id tB

      , testCase "case inl inr = id" $
          optimize (Case (Inl tA tB) (Inr tA tB))
            @?= Id (TSum tA tB)
      ]

  , testGroup "Nested optimizations"
      [ testCase "id ∘ (fst ∘ pair f g) = f" $
          optimize (Compose (Id tA) (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA))))
            @?= Id tA

      , testCase "(fst ∘ pair f g) ∘ id = f" $
          optimize (Compose (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA))) (Id tA))
            @?= Id tA
      ]

  , testGroup "Semantics preservation"
      [ testProperty "optimization preserves eval for products" $
          \a b -> let ir = Compose (Fst tA tB) (Pair (Fst tA tB) (Snd tA tB))
                      v = VPair a b
                  in eval (optimize ir) v == eval ir v

      , testProperty "optimization preserves eval for swap" $
          \a b -> let swap = Pair (Snd tA tB) (Fst tA tB)
                      v = VPair a b
                  in eval (optimize swap) v == eval swap v
      ]
  ]
