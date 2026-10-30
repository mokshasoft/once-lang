-- | Bridge to `once parse`, `check`, `elaborate` and `optimize`
-- (`Once.Inspect`, D352): a tool beside the compiler.
module Once.Inspect.Bridge
  ( signatures
  , check
  , dumpIR
  ) where

import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Data.Sum.Base as MSum
import qualified MAlonzo.Code.Once.Inspect as MI
import Once.Bridge.Agda (agdaToText, eitherText)
import Once.Compile.Bridge (Resolved, resolvedAgda)

-- | The declarations the typechecker sees, `name : type` per line, or the error.
signatures :: Resolved -> Either Text Text
signatures r = eitherText (MI.d_signatures_40 (unsafeCoerce (resolvedAgda r)))

-- | The module typechecks, or the error.
check :: Resolved -> Either Text ()
check r = case MI.d_check_48 (unsafeCoerce (resolvedAgda r)) of
  MSum.C_inj'8321'_38 err -> Left (agdaToText err)
  MSum.C_inj'8322'_42 _   -> Right ()

-- | Each compiled function's IR, unoptimized (`False`) or optimized (`True`):
-- the functions a built file is emitted from (`Once.Inspect.Proof`).
dumpIR :: Bool -> Resolved -> Either Text Text
dumpIR doOpt r = eitherText (MI.d_dumpIR_68 doOpt (unsafeCoerce (resolvedAgda r)))
