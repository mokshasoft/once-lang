-- | Bridge module for MAlonzo-generated Agda code
--
-- This module provides the interface for the verified MAlonzo optimizer.
-- Currently stubbed out - the MAlonzo modules need to be generated from Agda.
--
-- TODO: Run `cd formal && make malonzo` to generate the verified code.
module Once.MAlonzo
  ( -- * Optimization
    optimizeMAlonzo
  , canConvertIR
  ) where

import qualified Once.IR as H

-- | Check if an IR can be converted to MAlonzo format
-- Currently always returns False (MAlonzo not available)
canConvertIR :: H.IR -> Bool
canConvertIR _ = False

-- | Optimize using MAlonzo (verified) optimizer
-- Currently returns input unchanged (MAlonzo not available)
optimizeMAlonzo :: H.IR -> H.IR
optimizeMAlonzo = id
