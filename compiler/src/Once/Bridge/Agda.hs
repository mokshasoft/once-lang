-- | Value conversions shared by the bridge modules (`Once.Compile.Bridge` and
-- one per tool beside the compiler): Agda strings are Haskell `Text` at run
-- time, and a `String ⊎ String` result is an `Either`.
module Once.Bridge.Agda
  ( agdaToText
  , textToAgda
  , eitherText
  , runs
  ) where

import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Data.Sum.Base as MSum
import qualified MAlonzo.Code.Once.Extract.Root as MR

-- | Agda strings are Haskell `Text` at runtime (MAlonzo primitive binding).
agdaToText :: a -> Text
agdaToText = unsafeCoerce

textToAgda :: Text -> a
textToAgda = unsafeCoerce

-- | What runs (`Once.Extract.Root.runs`, D353): every bridge calls the
-- Agda side through this record's fields, so a function the CLI runs is one of
-- them, and `run-ast-dumps.sh` sees it.
runs :: MR.T_Runs_6
runs = MR.d_runs_66

-- | An Agda `String ⊎ String`: the error, or the output.
eitherText :: MSum.T__'8846'__30 -> Either Text Text
eitherText (MSum.C_inj'8321'_38 err) = Left (agdaToText err)
eitherText (MSum.C_inj'8322'_42 out) = Right (agdaToText out)
