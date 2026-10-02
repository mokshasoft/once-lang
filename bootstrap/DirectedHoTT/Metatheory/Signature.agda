-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — ★ A WELL-FORMED SIGNATURE, and CONSERVATIVITY.
--                      (PLAN-BIDI §2-bis, S5 — design (ii), route B)
--
-- ★ `WfSig S`: entry `n` has an ANNOTATED body, typed at its declared type
--   in the empty context over the PREFIX of the first `n` entries, whose
--   erasure is the stored `body n`.  Typing in the prefix is what makes
--   the signature acyclic: a body refers only to earlier entries.
--
-- ★ `wf→ok`: a well-formed signature satisfies `SigOK`, the hypothesis of
--   δ-elimination (`Metatheory/Erasure`).  By induction on the entries:
--   entry `n` is erased by `Erasure` over its prefix, whose `SigOK` is the
--   induction hypothesis.  No new metatheory: the kernel's proofs are
--   reused as they are.
--
-- ★ CONSERVATIVITY, the payoff: every kernel theorem holds over every
--   well-formed signature.  Consistency is below, one line.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Metatheory.Signature where
open import normalizer.Syntax.Types using ( _≡_; subst; Σ; _,_; _×_; ⊤; ⊥ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing using ( ◇; _⊢_∷_ )
open import DirectedHoTT.Spec.Annotated
open import DirectedHoTT.Spec.Signature
import DirectedHoTT.Spec.TypingA as TA
import DirectedHoTT.Metatheory.Erasure as Er

-- entry `n`, well-formed over its prefix
EntryWf : Sig → ℕ → Set
EntryWf S n =
  Σ (ATm ε) λ b →
    TA._⊢ᴬ_∷_ (prefix S n) TA.◇ᴬ b (Sig.type S n)
  × (Era.⌈_⌉ (Sig.body S) b ≡ Sig.body S n)

-- the first `n` entries are well-formed
WfUpTo : Sig → ℕ → Set
WfUpTo S zero    = ⊤
WfUpTo S (suc n) = WfUpTo S n × EntryWf S n

WfSig : Sig → Set
WfSig S = WfUpTo S (Sig.size S)

-- ★ every entry of a well-formed prefix erases to a closed kernel term of
--   its erased declared type
okUpTo : (S : Sig) (n : ℕ) → WfUpTo S n → SigOK (prefix S n)
okUpTo S (suc n) (w , (b , (db , eq))) <-here =
  subst (λ t → ◇ ⊢ t ∷ _) eq (Er.erase (prefix S n) (okUpTo S n w) db)
okUpTo S (suc n) (w , _) (<-there p) = okUpTo S n w p

wf→ok : (S : Sig) → WfSig S → SigOK S
wf→ok S w = okUpTo S (Sig.size S) w

------------------------------------------------------------------------
-- ★ Conservativity: the kernel's consistency, over any signature.
------------------------------------------------------------------------

consistencyˢ : (S : Sig) → WfSig S → {t : ATm ε} →
               TA._⊢ᴬ_∷_ S TA.◇ᴬ t base → ⊥
consistencyˢ S w = Er.consistencyᴬ S (wf→ok S w)
