module Once.Value
  ( Value (..)
  ) where

import Once.IR (IR)

-- | Runtime values for the interpreter
--
-- These correspond to the categorical constructs:
-- - VUnit: terminal object
-- - VPair: product
-- - VLeft/VRight: coproduct (sum)
-- - VClosure: exponential (function)
data Value
  = VUnit                      -- ^ Unit value (terminal)
  | VPair Value Value          -- ^ Pair value: (a, b)
  | VLeft Value                -- ^ Left injection: inl a
  | VRight Value               -- ^ Right injection: inr b
  | VClosure [(IR, Value)] IR  -- ^ Closure: captured environment + body
  deriving (Eq, Show)
