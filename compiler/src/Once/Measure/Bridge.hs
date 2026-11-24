-- | Bridge to `once stats` (`Once.Measure`, MERGE.md §1): a tool beside the
-- compiler.
module Once.Measure.Bridge
  ( statsFromModule
  ) where

import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Once.Extract.Root as MR
import Once.Bridge.Agda (eitherText, runs)
import Once.Compile.Bridge (Resolved, resolvedAgda)

-- | The static costs of the module's program image, optimized (`True`) or
-- not, or the compiler's error.
statsFromModule :: Bool -> Resolved -> Either Text Text
statsFromModule doOpt r = eitherText (MR.d_stats_60 runs doOpt (unsafeCoerce (resolvedAgda r)))
