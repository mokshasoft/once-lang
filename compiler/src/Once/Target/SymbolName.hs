-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Haskell mirror of @Once.Target.Symbol.once-symbol-path@ — the verified
-- assembly-symbol mangler the codegen uses for SigOp call sites.
--
-- The build driver (Once.CLI) uses this to map an interpretation operation's
-- CLEAN symbol (its bare signature name, as written in the @.<target>@ impl
-- file) to the mangled symbol the compiled program actually calls, so impl
-- authors never hand-compute a mangled string.
--
-- It is kept in lock-step with the Agda original by the golden tests in
-- test/SymbolNameSpec.hs, which assert exactly the vectors @Once.Target.Symbol@
-- proves by @refl@. (A direct call into the MAlonzo extraction would be brittle:
-- its generated names carry extraction-fingerprint suffixes.)
module Once.Target.SymbolName
  ( onceSymbolPath
  , mangleComponent
  ) where

import Data.List (intercalate)

-- | z-encode a single character (mirrors @z-encode-char@): escape the few
-- characters that are not valid in an assembler symbol.
zEncodeChar :: Char -> String
zEncodeChar 'z'  = "zz"
zEncodeChar '\'' = "zq"
zEncodeChar '+'  = "zp"
zEncodeChar '*'  = "zt"
zEncodeChar '!'  = "zb"
zEncodeChar '?'  = "zh"
zEncodeChar '.'  = "zd"
zEncodeChar c    = [c]

zEncode :: String -> String
zEncode = concatMap zEncodeChar

-- | A length-prefixed, z-encoded name component (mirrors @mangle-component@):
-- the byte length of the z-encoded text, then the z-encoded text.
mangleComponent :: String -> String
mangleComponent s = let e = zEncode s in show (length e) ++ e

-- | The full assembly symbol for a canonical name given as its segment list
-- (mirrors @once-symbol-path@): @once_@ then the @_@-joined mangled components.
--
-- e.g. @onceSymbolPath ["Interpretations","Linux","Syscalls","exit"]@
--      == @"once_15Interpretations_5Linux_8Syscalls_4exit"@
onceSymbolPath :: [String] -> String
onceSymbolPath parts = "once_" ++ intercalate "_" (map mangleComponent parts)
