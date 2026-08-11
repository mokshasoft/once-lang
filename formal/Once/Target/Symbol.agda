-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Char.Properties using (_≟_)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)
-- `showNat = showInBase 10`: same decimal output as `Data.Nat.Show.show`
-- (definitionally equal on every concrete numeral — the format-checks below
-- are unchanged) but built on `charsInBase`, which the stdlib proves INJECTIVE
-- (`Data.Nat.Show.Properties.charsInBase-injective`). Plan 0.50's
-- `once-symbol-path` injectivity lemma needs that; `show` (via `toNatDigits`)
-- has no stdlib injectivity proof.
open import Data.Nat.Show using (showInBase)
showNat : ℕ → String
showNat = showInBase 10
open import Once.CanonicalName using (CanonicalName; parts; canonical)

-- | Once's universal symbol prefix.
-- Applied to every Once-generated assembly symbol (user-defined
-- functions, SigOp call sites, runtime stubs).
once-prefix : String
once-prefix = "once_"

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
-- Dispatched through a top-level helper taking the `_≟_` DECISIONS as
-- explicit arguments (NOT a `with`-block — the user's blanket preference,
-- and exact-split friendly). This makes `z-encode-char` REDUCE on a
-- variable char once the decisions are supplied, and lets the injectivity
-- proof (`Once.Target.SymbolInjective`) classify a char by pattern-matching
-- the SAME `Dec` values — a literal-pattern catch-all is stuck on an
-- abstract `c`. Output identical (the format-checks below are unchanged).
-- `.` (dot) keeps single-component dotted names (arith.add.int) asm-safe.
z-encode-char-aux :
  (c : Char)
  → Dec (c ≡ 'z') → Dec (c ≡ '\'') → Dec (c ≡ '+') → Dec (c ≡ '*')
  → Dec (c ≡ '!') → Dec (c ≡ '?') → Dec (c ≡ '.') → List Char
z-encode-char-aux c (yes _) _ _ _ _ _ _ = 'z' ∷ 'z' ∷ []
z-encode-char-aux c (no _) (yes _) _ _ _ _ _ = 'z' ∷ 'q' ∷ []
z-encode-char-aux c (no _) (no _) (yes _) _ _ _ _ = 'z' ∷ 'p' ∷ []
z-encode-char-aux c (no _) (no _) (no _) (yes _) _ _ _ = 'z' ∷ 't' ∷ []
z-encode-char-aux c (no _) (no _) (no _) (no _) (yes _) _ _ = 'z' ∷ 'b' ∷ []
z-encode-char-aux c (no _) (no _) (no _) (no _) (no _) (yes _) _ = 'z' ∷ 'h' ∷ []
z-encode-char-aux c (no _) (no _) (no _) (no _) (no _) (no _) (yes _) = 'z' ∷ 'd' ∷ []
z-encode-char-aux c (no _) (no _) (no _) (no _) (no _) (no _) (no _) = c ∷ []

z-encode-char : Char → List Char
z-encode-char c =
  z-encode-char-aux c (c ≟ 'z') (c ≟ '\'') (c ≟ '+') (c ≟ '*')
                      (c ≟ '!') (c ≟ '?') (c ≟ '.')

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

-- | The canonical clash-free symbol for a resolved identity (its `parts`).
once-symbol-path : CanonicalName → String
once-symbol-path cn = once-prefix ++ join-us (map mangle-component (parts cn))

-- | Symbol for an OWN-module definition `name` — a single-component canonical
-- identity. Plan 0.50 (D064): definition-label sites (function prologues,
-- arith-block subroutines, `_start`'s `main` call) use THIS so the emitted
-- symbol equals `compile-sigOp`'s `once-symbol-path` CALL emission for the same
-- function (`canonical [name]`). Replaces the legacy `once-symbol`, which left
-- definitions on `once_name` while calls migrated to `once-symbol-path` — a
-- link mismatch. Being `once-symbol-path ∘ canonical ∘ [_]`, it inherits the
-- clash-freedom (`once-symbol-path-injective`).
once-symbol-own : String → String
once-symbol-own name = once-symbol-path (canonical (name ∷ []))

-- Format checks (the clash-free + asm-safe scheme, by example).
private
  open import Relation.Binary.PropositionalEquality using (refl)
  open import Once.CanonicalName using (canonical)
  -- module Cars.All, fn foo
  _ : once-symbol-path (canonical ("Cars" ∷ "All" ∷ "foo" ∷ [])) ≡ "once_4Cars_3All_3foo"
  _ = refl
  -- module Cars, fn All_foo — distinct from the above (no clash)
  _ : once-symbol-path (canonical ("Cars" ∷ "All_foo" ∷ [])) ≡ "once_4Cars_7All_foo"
  _ = refl
  -- asm-unsafe chars z-encoded: assocL+ → assocLzp (len 8)
  _ : once-symbol-path (canonical ("M" ∷ "assocL+" ∷ [])) ≡ "once_1M_8assocLzp"
  _ = refl
  -- single-component dotted name (arith.add.int) stays asm-safe: . → zd
  _ : once-symbol-path (canonical ("arith.add.int" ∷ [])) ≡ "once_15arithzdaddzdint"
  _ = refl
  -- literal "zp" escapes its z → zzp (≠ the encoding of `+`)
  _ : mangle-component "zp" ≡ "3zzp"
  _ = refl
