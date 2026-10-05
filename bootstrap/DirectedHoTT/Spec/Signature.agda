-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ THE GLOBAL SIGNATURE of closed definitions.
--                      (PLAN-BIDI §2-bis, S5 — design (ii), route B)
--
-- ★ WHAT IT IS.  Entries `0 … size-1`, each a closed annotated body of a
--   declared closed type.  An annotated term names entry `d` by `ref d`.
--   The theory this extends is the kernel's own: extension BY DEFINITIONS.
--
--     type d  — the DECLARED type; `ref d` is typed by it alone, so a
--               body is checked once, never at its use sites.
--     body d  — the body, ERASED.  Erasure unfolds `ref d` to it (δ), so
--               conversion in `⊢ᴬ`, which is on erasures, sees through
--               every definition — transparent definitions.
--
--   The annotated bodies themselves, and the proof that each is typed in
--   its PREFIX (acyclic, hence δ terminates), are well-formedness data —
--   `Metatheory/Signature`'s `WfSig` — not part of what a use site needs.
--
-- ★ `SigOK`: what the bridge to the kernel needs — every erased body has
--   its erased declared type, in the empty context.  `WfSig` proves it.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Signature where
open import normalizer.Syntax.Types using ( ¬_ )
open import Agda.Builtin.Nat using ( zero; suc; _==_ ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing using ( ◇; _⊢_∷_ )
open import DirectedHoTT.Spec.Annotated

-- ★ A TELESCOPE of entries (2026-10-05; the compiler's D071: the signature
--   is the definition CONTEXT, a reference a projection from it).  Entry n
--   is checked over the entries before it; extending a signature is
--   context extension, so a signature built in one module is extended in
--   another without re-checking it (`Metatheory/Signature.WfSig` is the
--   context-formation rule).  The length is cached, so a lookup is one
--   walk down the telescope.
record Entry : Set where
  constructor ⟨_∣_⟩
  field
    eType : ATy ε
    eBody : RTm ε
open Entry public

data Tele : Set where
  ∅   : Tele
  _▸_ : Tele → Entry → Tele
infixl 5 _▸_

-- entry d of a telescope of length n (entries counted from the first)
pickE : Bool → Entry → Entry → Entry
pickE true  x y = x
pickE false x y = y

lookupE : ℕ → Tele → ℕ → Entry
lookupE (suc n) (T ▸ e) d = pickE (d == n) e (lookupE n T d)
lookupE zero    _       d = ⟨ Unit ∣ nzero ⟩
lookupE (suc n) ∅       d = ⟨ Unit ∣ nzero ⟩

record Sig : Set where
  constructor mkSig
  field
    len  : ℕ
    tele : Tele
  -- what the checker and the erasure consult (`open Sig S`)
  size : ℕ
  size = len
  type : ℕ → ATy ε
  type d = eType (lookupE len tele d)
  body : ℕ → RTm ε
  body d = eBody (lookupE len tele d)
open Sig public using ( len; tele )

∅ˢ : Sig
∅ˢ = mkSig 0 ∅

-- extend by one entry
_▸ˢ_ : Sig → Entry → Sig
S ▸ˢ e = mkSig (suc (len S)) (tele S ▸ e)
infixl 5 _▸ˢ_

infix 4 _<ˢ_
data _<ˢ_ : ℕ → ℕ → Set where
  <-here  : ∀ {n} → n <ˢ suc n
  <-there : ∀ {d n} → d <ˢ n → d <ˢ suc n

<ˢ-zero : ∀ {d} → ¬ (d <ˢ zero)
<ˢ-zero ()

-- ★ the bridge's hypothesis: every entry, erased, is a closed kernel term
--   of its erased declared type
SigOK : Sig → Set
SigOK S = ∀ {d} → d <ˢ Sig.size S → ◇ ⊢ Sig.body S d ∷ Era.⌈_⌉ᵀ (Sig.body S) (Sig.type S d)
