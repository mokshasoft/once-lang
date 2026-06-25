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

open import Data.String using (String; _++_; toList; fromList)
open import Data.List using (List; []; _∷_; map; concatMap; length)
open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showNat)

-- | Once's universal symbol prefix.
-- Applied to every Once-generated assembly symbol (user-defined
-- functions, SigOp call sites, runtime stubs).
once-prefix : String
once-prefix = "once_"

-- | Legacy single-string mangle (just prepends `once_`). Retained for
-- callers not yet migrated to the canonical `once-symbol-path` (Plan 0.50).
once-symbol : String → String
once-symbol name = once-prefix ++ name

------------------------------------------------------------------------
-- Plan 0.50 — canonical, clash-free symbol from a resolved identity.
--
-- A definition's identity is its resolved component list `[path…, name]`
-- (all plain identifiers). The symbol is `once_` + `_`-joined
-- `<len><z-encoded-component>` segments:
--   • z-encoding (escape letter `z`) makes each component asm-safe — the
--     only unsafe identifier chars are `' + * ! ?` (lexer isIdentContinue);
--     `z` self-escapes so it's injective on ALL strings.
--   • the length-prefix carries structure (clash-free) — unambiguous
--     because a (z-encoded) component never starts with a digit, which is
--     exactly the lexer `isIdentStart` precondition.
-- Injectivity (`once-symbol-path` injective on `ValidIdent` component
-- lists) is proved separately and composed with lexer soundness.
------------------------------------------------------------------------

-- z-encode a single character (escape the asm-unsafe ones + `z` itself).
z-encode-char : Char → List Char
z-encode-char 'z'  = 'z' ∷ 'z' ∷ []
z-encode-char '\'' = 'z' ∷ 'q' ∷ []
z-encode-char '+'  = 'z' ∷ 'p' ∷ []
z-encode-char '*'  = 'z' ∷ 't' ∷ []
z-encode-char '!'  = 'z' ∷ 'b' ∷ []
z-encode-char '?'  = 'z' ∷ 'h' ∷ []
z-encode-char c    = c ∷ []

z-encode : String → String
z-encode s = fromList (concatMap z-encode-char (toList s))

-- One length-prefixed, z-encoded component: `<len><z-encoded chars>`.
mangle-component : String → String
mangle-component s = showNat (length (toList (z-encode s))) ++ z-encode s

-- `_`-join (a separator, not a delimiter — the length carries boundaries).
join-us : List String → String
join-us []           = ""
join-us (x ∷ [])     = x
join-us (x ∷ y ∷ xs) = x ++ "_" ++ join-us (y ∷ xs)

-- | The canonical clash-free symbol for a resolved identity `[path…, name]`.
once-symbol-path : List String → String
once-symbol-path comps = once-prefix ++ join-us (map mangle-component comps)

-- Format checks (the clash-free + asm-safe scheme, by example).
private
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  -- module Cars.All, fn foo
  _ : once-symbol-path ("Cars" ∷ "All" ∷ "foo" ∷ []) ≡ "once_4Cars_3All_3foo"
  _ = refl
  -- module Cars, fn All_foo — distinct from the above (no clash)
  _ : once-symbol-path ("Cars" ∷ "All_foo" ∷ []) ≡ "once_4Cars_7All_foo"
  _ = refl
  -- asm-unsafe chars z-encoded: assocL+ → assocLzp (len 8)
  _ : once-symbol-path ("M" ∷ "assocL+" ∷ []) ≡ "once_1M_8assocLzp"
  _ = refl
  -- literal "zp" escapes its z → zzp (≠ the encoding of `+`)
  _ : mangle-component "zp" ≡ "3zzp"
  _ = refl
