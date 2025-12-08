module Once.Quantity
  ( Quantity (..)
  , qAdd
  , qMul
  ) where

-- | Resource usage quantities for QTT
data Quantity
  = Zero   -- ^ Erased (compile-time only)
  | One    -- ^ Linear (exactly once)
  | Omega  -- ^ Unrestricted (any number)
  deriving (Eq, Show)

-- | Semiring addition: how many times a resource is used overall
qAdd :: Quantity -> Quantity -> Quantity
qAdd Zero r = r
qAdd r Zero = r
qAdd One One = Omega
qAdd _ _ = Omega

-- | Semiring multiplication: usage through composition
qMul :: Quantity -> Quantity -> Quantity
qMul Zero _ = Zero
qMul _ Zero = Zero
qMul One r = r
qMul r One = r
qMul Omega Omega = Omega
