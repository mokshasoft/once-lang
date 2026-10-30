-- | Value conversions shared by the bridge modules (`Once.Compile.Bridge` and
-- one per tool beside the compiler): Agda strings are Haskell `Text` at run
-- time, and a `String ⊎ String` result is an `Either`.
module Once.Bridge.Agda
  ( agdaToText
  , textToAgda
  , eitherText
  ) where

import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Data.Sum.Base as MSum

-- | Agda strings are Haskell `Text` at runtime (MAlonzo primitive binding).
agdaToText :: a -> Text
agdaToText = unsafeCoerce

textToAgda :: Text -> a
textToAgda = unsafeCoerce

-- | An Agda `String ⊎ String`: the error, or the output.
eitherText :: MSum.T__'8846'__30 -> Either Text Text
eitherText (MSum.C_inj'8321'_38 err) = Left (agdaToText err)
eitherText (MSum.C_inj'8322'_42 out) = Right (agdaToText out)
