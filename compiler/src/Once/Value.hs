module Once.Value
  ( Value (..)
  ) where

import Data.Text (Text)

import Once.IR (IR)

-- | Runtime values for the interpreter
--
-- These correspond to the categorical constructs:
-- - VUnit: terminal object
-- - VPair: product
-- - VLeft/VRight: coproduct (sum)
-- - VClosure: exponential (function)
-- - VInt/VFloat/VString: primitive base types
data Value
  = VUnit                      -- ^ Unit value (terminal)
  | VPair Value Value          -- ^ Pair value: (a, b)
  | VLeft Value                -- ^ Left injection: inl a
  | VRight Value               -- ^ Right injection: inr b
  | VClosure [(IR, Value)] IR  -- ^ Closure: captured environment + body
  | VInt Integer               -- ^ Integer value
  | VFloat Double              -- ^ Float value (OCP-0001)
  | VString Text               -- ^ String value (Utf8)

-- | Custom Eq instance for Value
-- Note: Closures always compare unequal (IR has no Eq instance)
instance Eq Value where
  VUnit == VUnit = True
  VPair a1 b1 == VPair a2 b2 = a1 == a2 && b1 == b2
  VLeft a1 == VLeft a2 = a1 == a2
  VRight a1 == VRight a2 = a1 == a2
  VClosure _ _ == VClosure _ _ = False  -- Can't compare IR
  VInt n1 == VInt n2 = n1 == n2
  VFloat f1 == VFloat f2 = f1 == f2
  VString s1 == VString s2 = s1 == s2
  _ == _ = False

-- | Custom Show instance for Value
-- Note: Closures show as <closure> (IR has no Show instance)
instance Show Value where
  show VUnit = "VUnit"
  show (VPair a b) = "VPair (" ++ show a ++ ") (" ++ show b ++ ")"
  show (VLeft a) = "VLeft (" ++ show a ++ ")"
  show (VRight a) = "VRight (" ++ show a ++ ")"
  show (VClosure _ _) = "VClosure <...>"
  show (VInt n) = "VInt " ++ show n
  show (VFloat f) = "VFloat " ++ show f
  show (VString s) = "VString " ++ show s
