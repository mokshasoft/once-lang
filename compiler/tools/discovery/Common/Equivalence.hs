{-# LANGUAGE LambdaCase #-}
-- | Equivalence testing for IR terms via evaluation
--
-- Two IR terms are considered equivalent if they produce the same
-- output for all inputs of the source type.
module Common.Equivalence
  ( testEquivalent
  , genValueForType
  , evalEq
  ) where

import Test.QuickCheck (Gen, arbitrary, oneof, sized, vectorOf, generate)
import Once.IR (IR)
import Once.Type (Type(..))
import Once.Value (Value(..))
import Once.Eval (eval)

-- | Generate a random value appropriate for a given type
--
-- This extends the Arbitrary instance from IRSpec.hs to be type-directed.
genValueForType :: Type -> Gen Value
genValueForType = sized . genSized
  where
    genSized :: Type -> Int -> Gen Value
    genSized TUnit _ = pure VUnit
    genSized TVoid _ = error "Cannot generate values of type Void"
    genSized (TVar _) n = genAnyValue n  -- Type variable: generate any value
    genSized (TProduct a b) n = do
      let half = n `div` 2
      VPair <$> genSized a half <*> genSized b half
    genSized (TSum a b) n = oneof
      [ VLeft <$> genSized a (n - 1)
      , VRight <$> genSized b (n - 1)
      ]
    genSized TInt _ = VInt <$> arbitrary
    genSized TFloat _ = VFloat <$> arbitrary
    genSized (TString _) _ = pure (VString "test")
    genSized _ n = genAnyValue n  -- Fallback

    -- Generate any value (for type variables)
    genAnyValue :: Int -> Gen Value
    genAnyValue 0 = pure VUnit
    genAnyValue n = oneof
      [ pure VUnit
      , VPair <$> genAnyValue (n `div` 2) <*> genAnyValue (n `div` 2)
      , VLeft <$> genAnyValue (n - 1)
      , VRight <$> genAnyValue (n - 1)
      ]

-- | Test if two IR terms produce the same output for a given input
evalEq :: IR -> IR -> Value -> Bool
evalEq f g v = case (eval f v, eval g v) of
  (Right a, Right b) -> a == b
  (Left _, Left _)   -> True  -- Both error = considered equivalent
  _                  -> False

-- | Test if two IR terms are semantically equivalent
--
-- Generates random inputs and checks if both terms produce the same output.
-- Returns True if all tests pass.
testEquivalent :: IR -> IR -> Type -> Int -> IO Bool
testEquivalent f g srcType numTests = do
  inputs <- generate $ vectorOf numTests (genValueForType srcType)
  pure $ all (evalEq f g) inputs
