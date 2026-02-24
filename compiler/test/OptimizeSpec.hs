module OptimizeSpec (optimizeTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Once.Eval (eval)
import Once.IR (IR (..))
import Once.MAlonzo (optimizeMAlonzo)

optimize :: IR -> IR
optimize = optimizeMAlonzo
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

-- | IR comparison for testing (since IR doesn't have Eq)
irMatches :: IR -> IR -> Bool
irMatches (Id t1) (Id t2) = t1 == t2
irMatches (Compose g1 f1) (Compose g2 f2) = irMatches g1 g2 && irMatches f1 f2
irMatches (Fst a1 b1) (Fst a2 b2) = a1 == a2 && b1 == b2
irMatches (Snd a1 b1) (Snd a2 b2) = a1 == a2 && b1 == b2
irMatches (Pair a1 b1) (Pair a2 b2) = irMatches a1 a2 && irMatches b1 b2
irMatches (Terminal t1) (Terminal t2) = t1 == t2
irMatches (Inl a1 b1) (Inl a2 b2) = a1 == a2 && b1 == b2
irMatches (Inr a1 b1) (Inr a2 b2) = a1 == a2 && b1 == b2
irMatches (Case a1 b1) (Case a2 b2) = irMatches a1 a2 && irMatches b1 b2
irMatches _ _ = False

-- | Assert IR equality for testing
assertIREqual :: String -> IR -> IR -> Assertion
assertIREqual msg expected actual =
  assertBool (msg ++ ": IR mismatch") (irMatches expected actual)

optimizeTests :: TestTree
optimizeTests = testGroup "Optimize"
  [ testGroup "Identity elimination"
      [ testCase "f ∘ id = f" $
          assertIREqual "f ∘ id = f"
            (Fst tA tB)
            (optimize (Compose (Fst tA tB) (Id (TProduct tA tB))))

      , testCase "id ∘ f = f" $
          assertIREqual "id ∘ f = f"
            (Fst tA tB)
            (optimize (Compose (Id tA) (Fst tA tB)))

      , testCase "id ∘ id = id" $
          assertIREqual "id ∘ id = id"
            (Id tA)
            (optimize (Compose (Id tA) (Id tA)))
      ]

  , testGroup "Product laws"
      [ testCase "fst ∘ pair f g = f" $
          assertIREqual "fst ∘ pair f g = f"
            (Id tA)
            (optimize (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA))))

      , testCase "snd ∘ pair f g = g" $
          assertIREqual "snd ∘ pair f g = g"
            (Terminal tA)
            (optimize (Compose (Snd tA tB) (Pair (Id tA) (Terminal tA))))

      , testCase "pair fst snd = id" $
          assertIREqual "pair fst snd = id"
            (Id (TProduct tA tB))
            (optimize (Pair (Fst tA tB) (Snd tA tB)))
      ]

  , testGroup "Coproduct laws"
      [ testCase "case f g ∘ inl = f" $
          assertIREqual "case f g ∘ inl = f"
            (Id tA)
            (optimize (Compose (Case (Id tA) (Terminal tB)) (Inl tA tB)))

      , testCase "case f g ∘ inr = g" $
          assertIREqual "case f g ∘ inr = g"
            (Id tB)
            (optimize (Compose (Case (Terminal tA) (Id tB)) (Inr tA tB)))

      , testCase "case inl inr = id" $
          assertIREqual "case inl inr = id"
            (Id (TSum tA tB))
            (optimize (Case (Inl tA tB) (Inr tA tB)))
      ]

  , testGroup "Nested optimizations"
      [ testCase "id ∘ (fst ∘ pair f g) = f" $
          assertIREqual "id ∘ (fst ∘ pair f g) = f"
            (Id tA)
            (optimize (Compose (Id tA) (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA)))))

      , testCase "(fst ∘ pair f g) ∘ id = f" $
          assertIREqual "(fst ∘ pair f g) ∘ id = f"
            (Id tA)
            (optimize (Compose (Compose (Fst tA tB) (Pair (Id tA) (Terminal tA))) (Id tA)))
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
