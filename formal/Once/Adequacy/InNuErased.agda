-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.InNuErased — the `in-ν`/ν erased-functor coherence.
--
-- The exact mirror of `InErased`, at the OTHER fixpoint. `realize`'s `in-ν`
-- builds a ν value through the ERASED functor `⌈eraseF F⌉F`, while the meaning
-- (`Denotation.Meaning.in-ν-value`) uses the SURFACE functor `F`. `liftFn-in-ν`
-- reduces the transported `in-ν` denotation to `returnT (in-ν-value v)`.
--
-- Shorter than `OutErased` (473 lines) for the same reason `InErased` (128) is:
-- this direction USES `AnaErased.coerce-νin-erase-D` forward, where `Out` had
-- to invert it.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

module Once.Adequacy.InNuErased (fmt : TargetNum) where

open import Function using (id)
open import Data.Product using (_,_; proj₂)
open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym)

open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ν-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF; translateF)
open import Once.IRTy using (IRTy; eraseF; ⌈_⌉F; ⌈_⌉; ⌊_⌋; ⌊⟧T-commute; ⌈⟧TI-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Semantics.Functor using (SFunctor; ⟦_⟧SF)
open import Once.Semantics.Machine using (coerce-functor; coh; tF-coh; ⟦_⟧; ⟦_⟧F; coerce-ν-in)
open import Once.Res using (Res; returns; mapRes)
open import Once.Denotation.TraceMonad using (T; returnT; projTrace)
open import Once.Denotation.ValueDomain
  using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; forget; cohᴰ; νᵈ; in-νᵈ; coerce-functor-D)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Meaning using (in-ν-value)
open import Once.Adequacy.CataErased fmt using (subst-T-projTrace; subst-T-resT; T-ext; evalᴰ-subst-dom)
open import Once.Adequacy.AnaErased fmt using (coerce-νin-erase-D)
open import Once.Adequacy.InErased fmt using (subst-⟦⟧ᴰᴵ-fix; coerce-μ-in-subst)
open import Once.Postulates using (extensionality)
import Once.IR as IR

-- The transported `in-ν` morphism `realize` emits.
in-ν-ir : ∀ {F : Functor} → WellFormedF F → IR.IR ⌊ ⟦ F ⟧T (ν-type F) ⌋ ⌊ ν-type F ⌋
in-ν-ir {F} wfF = subst (λ o → IR.IR o ⌊ ν-type F ⌋)
                        (sym (⌊⟧T-commute F (ν-type F)))
                        (IR.in-ν (wf-⌊⌋ wfF))

-- `in-νᵈ` commutes with a subst over the functor eq. Match-to-refl.
in-νᵈ-subst-nat : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (z : ⟦ H₁ ⟧SF (νᵈ H₁))
  → subst νᵈ eq (in-νᵈ z) ≡ in-νᵈ (subst (λ H → ⟦ H ⟧SF (νᵈ H)) eq z)
in-νᵈ-subst-nat refl z = refl

-- `subst id (cong νᵈ p) = subst νᵈ p`. Match-to-refl.
subst-id-νᵈ : ∀ {H₁ H₂ : SFunctor} (p : H₁ ≡ H₂) (z : νᵈ H₁)
  → subst id (cong νᵈ p) z ≡ subst νᵈ p z
subst-id-νᵈ refl z = refl

-- Split a diagonal subst `⟦H⟧SF(νᵈ H)` into carrier-subst then functor-subst.
subst-diag-ν : ∀ {H₁ H₂ : SFunctor} (eq : H₁ ≡ H₂) (z : ⟦ H₁ ⟧SF (νᵈ H₁))
  → subst (λ H → ⟦ H ⟧SF (νᵈ H)) eq z
    ≡ subst (λ H → ⟦ H ⟧SF (νᵈ H₂)) eq (subst (λ C → ⟦ H₁ ⟧SF C) (cong νᵈ eq) z)
subst-diag-ν refl z = refl

-- TRACE half: `[]`. `evalᴰ (in-ν wf)` is a `returnT`, so once the two
-- transports are peeled the trace is `[]` definitionally.
in-ν-trace : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (ν-type F) ⟧ᴰ) (n : ℕ)
  → projTrace (liftFn fmt {⟦ F ⟧T (ν-type F)} {ν-type F} (in-ν-ir wfF) v) n ≡ []
in-ν-trace {F} wfF v n =
  trans (subst-T-projTrace (cong νᵈ (tF-coh F))
          (evalᴰ fmt (in-ν-ir wfF) (subst id (sym (cohᴰ (⟦ F ⟧T (ν-type F)))) v)) n)
        (cong (λ hh → projTrace hh n)
          (evalᴰ-subst-dom (sym (⌊⟧T-commute F (ν-type F))) (IR.in-ν (wf-⌊⌋ wfF))
                           (subst id (sym (cohᴰ (⟦ F ⟧T (ν-type F)))) v)))

-- RESULT half — one fact, not two. Before plan 0.98 this was a pair of
-- lemmas: `in-ν-stopped` said the flag was `false` and `in-ν-value-erase`
-- said the value was `in-ν-value v`. `Res` makes "it returned" and "what it
-- returned" the same statement, so the flag half is gone and the coherence
-- (`AnaErased.coerce-νin-erase-D`, wrapped by `in-νᵈ`) sits under one
-- `returns`.
--
-- The budget index went with it: the old value lemma took an `n` only
-- because `valueT` did, and the RESULT never depended on the budget — only
-- the trace does. `evalᴰ` is still stuck under the domain `subst`, which is
-- why this is not `refl` (the same reason `in-ν-trace` is not).
in-ν-res : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (ν-type F) ⟧ᴰ)
  → T.resT (liftFn fmt {⟦ F ⟧T (ν-type F)} {ν-type F} (in-ν-ir wfF) v)
    ≡ returns (in-ν-value v)
in-ν-res {F} wfF v =
  trans (subst-T-resT (cong νᵈ (tF-coh F))
                      (evalᴰ fmt (in-ν-ir wfF) (subst id (sym (cohᴰ (⟦ F ⟧T (ν-type F)))) v)))
  (trans (cong (λ hh → mapRes (subst id (cong νᵈ (tF-coh F))) (T.resT hh))
               (evalᴰ-subst-dom (sym (⌊⟧T-commute F (ν-type F))) (IR.in-ν (wf-⌊⌋ wfF))
                                (subst id (sym (cohᴰ (⟦ F ⟧T (ν-type F)))) v)))
  (trans (cong (λ arg → mapRes (subst id (cong νᵈ (tF-coh F)))
                          (T.resT (evalᴰ fmt (IR.in-ν (wf-⌊⌋ wfF)) arg)))
               (subst-⟦⟧ᴰᴵ-fix (⌊⟧T-commute F (ν-type F)) (subst id (sym (cohᴰ (⟦ F ⟧T (ν-type F)))) v)))
  (cong returns
    (trans (subst-id-νᵈ (tF-coh F) _)
    (trans (in-νᵈ-subst-nat (tF-coh F) _)
           (cong in-νᵈ
             (trans (subst-diag-ν (tF-coh F) _)
             (trans (cong (subst (λ H → ⟦ H ⟧SF ⟦ ν-type F ⟧ᴰ) (tF-coh F))
                          (sym (coerce-μ-in-subst ⌈ eraseF F ⌉F (cohᴰ (ν-type F)) _)))
                    (trans (coerce-νin-erase-D F (ν-type F) (subst id (sym (cohᴰ (⟦ F ⟧T (ν-type F)))) v))
                           (cong (λ x → coerce-ν-in F ⟦ ν-type F ⟧ᴰ (coerce-functor-D F (ν-type F) x))
                                 (subst-subst-sym (cohᴰ (⟦ F ⟧T (ν-type F))))))))))))))

-- The combinator reduction: `liftFn` of the transported `in-ν` is
-- `returnT (in-ν-value v)` — trace `[]`, result `in-ν-res`.
liftFn-in-ν : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (ν-type F) ⟧ᴰ)
  → liftFn fmt {⟦ F ⟧T (ν-type F)} {ν-type F} (in-ν-ir wfF) v ≡ returnT (in-ν-value v)
liftFn-in-ν {F} wfF v =
  -- plan 0.98: record eta over the TWO fields — trace family and result.
  -- The introduction form emits nothing and cannot end the program, so its
  -- result is `returnT`'s `returns` on both sides.
  T-ext (in-ν-trace wfF v)
        (in-ν-res wfF v)
