-- | Bridge to `once fmt` (`Once.Format`, plan 0.124): a tool beside the
-- compiler.
module Once.Format.Bridge
  ( formatSource
  ) where

import Data.Text (Text)

import qualified MAlonzo.Code.Once.Format as MF
import Once.Bridge.Agda (eitherText, textToAgda)

-- | A source text in the canonical layout, or the parser's error.
formatSource :: Text -> Either Text Text
formatSource source = eitherText (MF.d_formatSource_14 (textToAgda source))
