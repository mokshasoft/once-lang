-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence — the core meaning is a function of the judgment
-- (`Spec.Core.Coherence`, plan 0.116 D1). PROVED.
--
-- Two derivations of one judgment differ only where the structural rules sit
-- (`⊢sub-use`, `⊢sub-eff`, `⊢coerce`) and in `⊢lam`'s body head usage: a core
-- term determines its type (D310, `Coherence.Uniqueness`). The fundamental
-- lemma (`Coherence.Fundamental`) relates any two derivations of one term in
-- agreeing environments by `S`, which holds sameness inside the trees
-- (`Coherence.Relation`); `S` is the Spec's `Same` (`S→Same`), and an
-- environment the same as itself agrees with itself (`Coherence.Env`).
--
-- No axiom: the proof uses neither a postulate nor function extensionality.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Lang.Core.PolyTy using (Sig)
open import Once.Lang.Contract using (ISig)

module Once.Metatheory.Coherence {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Once.Lang.Core.Coherence S using (Coherence)
open import Once.Metatheory.Coherence.Relation using (≈∞→N; S→Same)
open import Once.Metatheory.Coherence.Env using (Same-Agree)
open import Once.Metatheory.Coherence.Fundamental S using (FL)

coherence : Coherence
coherence = record
  { coherent = λ {_} {Γ} {Ψ} {_} {A} d d′ fmt δ sd x sx n →
      ≈∞→N (λ r → S→Same A r n) (FL fmt δ sd d d′ (Same-Agree Γ Ψ sx)) n }
