-- | Bridge to `once stats` (`Once.Measure`, MERGE.md §1): a tool beside the
-- compiler.
module Once.Measure.Bridge
  ( statsFromModule
  ) where

import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Once.Measure as MMe
import Once.Bridge.Agda (eitherText)
import Once.Compile.Bridge (Resolved, resolvedAgda)

-- | The static costs of the module's program image, optimized (`True`) or
-- not, or the compiler's error.
statsFromModule :: Bool -> Resolved -> Either Text Text
statsFromModule doOpt r = eitherText (MMe.d_statsOf_4 doOpt (unsafeCoerce (resolvedAgda r)))
