-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Target.Symbol
--
-- Shared assembly-symbol naming convention across all targets.
--
-- The Once compiler emits all symbols (user functions, SigOp call
-- sites, runtime impl files in `Strata/Interpretations/<…>.<arch>`)
-- with the `once_` prefix. This namespace separates Once-generated
-- code from libc/system symbols and is uniform across architectures.
--
-- Per-arch codegen modules (`Once.CCC.Target.<arch>.CodeGen.*`,
-- `Once.Target.<arch>`, `Once.CCC.Target.<arch>.AbstractTo<arch>`)
-- import this module rather than hard-coding `"once_"` themselves.
------------------------------------------------------------------------

module Once.Target.Symbol where

open import Data.String using (String; _++_)

-- | Once's universal symbol prefix.
-- Applied to every Once-generated assembly symbol (user-defined
-- functions, SigOp call sites, runtime stubs).
once-prefix : String
once-prefix = "once_"

-- | Mangle a name into a valid assembly symbol following Once's
-- convention. Currently just prepends `once_`; future extensions
-- (e.g. dot mangling, arch-specific quirks) belong here, not in
-- per-arch codegen.
once-symbol : String → String
once-symbol name = once-prefix ++ name
