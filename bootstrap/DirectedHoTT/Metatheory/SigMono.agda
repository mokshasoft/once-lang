-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- ⚠ GENERATED (PLAN-REF): one clause per typing rule.
--
-- OCP-0009 · dHoTT — ★ DERIVATIONS MOVE TO A LARGER NAME BOUND.
--
-- The typing judgement is parameterised by the number of signature names
-- a derivation may use (`Spec/Typing`'s `n`; `⊢ref : d <ˢ n → …`).  Any
-- inclusion of name sets carries a derivation over, unchanged except at
-- `⊢ref`: the definition-context counterpart of renaming.  An entry is
-- typed at its prefix (n = d) and used at the full signature through this.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( KSig; _<ˢ_ )
module DirectedHoTT.Metatheory.SigMono (𝒮 : KSig) (m m' : ℕ)
  (inc : ∀ {d} → d <ˢ m → d <ˢ m') where
import DirectedHoTT.Spec.Typing 𝒮 m as A
import DirectedHoTT.Spec.Typing 𝒮 m' as B

mutual
  mono    : ∀ {Γ t T} → A._⊢_∷_ Γ t T → B._⊢_∷_ Γ t T
  monoTy  : ∀ {Γ T} → A._⊢ty_ Γ T → B._⊢ty_ Γ T
  monoCtx : ∀ {Γ} → A.⊢ctx_ Γ → B.⊢ctx_ Γ
  mono (A.⊢var x0) = B.⊢var x0
  mono (A.⊢lam x0 x1) = B.⊢lam (monoTy x0) (mono x1)
  mono (A.⊢app x0 x1) = B.⊢app (mono x0) (mono x1)
  mono (A.⊢pair x0 x1 x2) = B.⊢pair (monoTy x0) (mono x1) (mono x2)
  mono (A.⊢absurd x0 x1) = B.⊢absurd (mono x0) (mono x1)
  mono (A.⊢ordtr x0 x1 x2 x3 x4) = B.⊢ordtr (mono x0) (mono x1) (mono x2) (mono x3) (mono x4)
  mono (A.⊢fst x0) = B.⊢fst (mono x0)
  mono (A.⊢snd x0) = B.⊢snd (mono x0)
  mono A.⊢⌜base⌝ = B.⊢⌜base⌝
  mono (A.⊢⌜Π⌝ x0 x1) = B.⊢⌜Π⌝ (mono x0) (mono x1)
  mono (A.⊢⌜Σ⌝ x0 x1) = B.⊢⌜Σ⌝ (mono x0) (mono x1)
  mono (A.⊢⌜Hom⌝ x0 x1 x2) = B.⊢⌜Hom⌝ (mono x0) (mono x1) (mono x2)
  mono (A.⊢hrefl x0 x1) = B.⊢hrefl (mono x0) (mono x1)
  mono (A.⊢trU x0 x1 x2 x3) = B.⊢trU (mono x0) (mono x1) (mono x2) (mono x3)
  mono (A.⊢tr x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) = B.⊢tr (mono x0) (mono x1) (mono x2) x3 x4 x5 (mono x6) (mono x7) (mono x8) (mono x9)
  mono (A.⊢ap x0 x1 x2 x3 x4 x5 x6) = B.⊢ap (mono x0) x1 (mono x2) (mono x3) (mono x4) (mono x5) (mono x6)
  mono (A.⊢⌜Id⌝ x0 x1 x2) = B.⊢⌜Id⌝ (mono x0) (mono x1) (mono x2)
  mono A.⊢⌜Nat⌝ = B.⊢⌜Nat⌝
  mono (A.⊢⌜IMu⌝ x0 x1 x2) = B.⊢⌜IMu⌝ (mono x0) (mono x1) (mono x2)
  mono (A.⊢⌜Fin⌝ x0) = B.⊢⌜Fin⌝ (mono x0)
  mono A.⊢⌜Unit⌝ = B.⊢⌜Unit⌝
  mono (A.⊢idrefl x0 x1) = B.⊢idrefl (mono x0) (mono x1)
  mono (A.⊢jsub x0 x1 x2 x3 x4) = B.⊢jsub (mono x0) (mono x1) (mono x2) (mono x3) (mono x4)
  mono A.⊢unit = B.⊢unit
  mono A.⊢nzero = B.⊢nzero
  mono (A.⊢nsuc x0) = B.⊢nsuc (mono x0)
  mono (A.⊢natrec x0 x1 x2 x3) = B.⊢natrec (monoTy x0) (mono x1) (mono x2) (mono x3)
  mono (A.⊢dι x0) = B.⊢dι (mono x0)
  mono (A.⊢dσ x0 x1 x2) = B.⊢dσ (mono x0) (mono x1) (mono x2)
  mono (A.⊢dρ x0 x1 x2) = B.⊢dρ (mono x0) (mono x1) (mono x2)
  mono (A.⊢dpay x0 x1 x2) = B.⊢dpay (mono x0) (mono x1) (mono x2)
  mono (A.⊢con x0 x1 x2 x3) = B.⊢con (mono x0) (mono x1) (mono x2) (mono x3)
  mono (A.⊢dih x0 x1 x2 x3 x4 x5) = B.⊢dih (mono x0) (mono x1) (monoTy x2) (mono x3) (mono x4) (mono x5)
  mono (A.⊢ielim x0 x1 x2 x3 x4 x5) = B.⊢ielim (mono x0) (mono x1) (monoTy x2) (mono x3) (mono x4) (mono x5)
  mono (A.⊢fzero x0) = B.⊢fzero (mono x0)
  mono (A.⊢fsuc x0) = B.⊢fsuc (mono x0)
  mono (A.⊢fcase x0 x1 x2 x3) = B.⊢fcase (monoTy x0) (mono x1) (mono x2) (mono x3)
  mono (A.⊢fcase0 x0 x1) = B.⊢fcase0 (monoTy x0) (mono x1)
  mono (A.⊢psplit x0 x1 x2 x3 x4) = B.⊢psplit (monoTy x0) (monoTy x1) (monoTy x2) (mono x3) (mono x4)
  mono (A.⊢ref x0) = B.⊢ref (inc x0)
  mono (A.⊢conv x0 x1) = B.⊢conv (mono x0) x1
  monoTy A.ty-base = B.ty-base
  monoTy A.ty-U = B.ty-U
  monoTy (A.ty-Π x0 x1) = B.ty-Π (monoTy x0) (monoTy x1)
  monoTy (A.ty-Σ x0 x1) = B.ty-Σ (monoTy x0) (monoTy x1)
  monoTy (A.ty-El x0) = B.ty-El (mono x0)
  monoTy (A.ty-Id x0 x1 x2) = B.ty-Id (monoTy x0) (mono x1) (mono x2)
  monoTy A.ty-Unit = B.ty-Unit
  monoTy A.ty-Nat = B.ty-Nat
  monoTy (A.ty-IMu x0 x1 x2) = B.ty-IMu (mono x0) (mono x1) (mono x2)
  monoTy (A.ty-Desc x0) = B.ty-Desc (mono x0)
  monoTy (A.ty-DIh x0 x1 x2 x3 x4) = B.ty-DIh (mono x0) (mono x1) (monoTy x2) (mono x3) (mono x4)
  monoTy (A.ty-Fin x0) = B.ty-Fin (mono x0)
  monoTy (A.ty-Hom x0 x1 x2) = B.ty-Hom (monoTy x0) (mono x1) (mono x2)
  monoCtx A.c-◇ = B.c-◇
  monoCtx (A.c-▹ x0 x1) = B.c-▹ (monoCtx x0) (monoTy x1)
