-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.InErased — the `In`/μ erased-functor coherence (Plan 0.52 M2).
--
-- `realize`'s `In` builds a μ value via the ERASED functor `⌈eraseF F⌉F`
-- (`eval (In (wf-⌊⌋ wfF) …) = sem-In ⌈eraseF F⌉F ∘ coerce-functor …`), while the
-- meaning uses the SURFACE functor `F` (`in-value = sem-In F ∘ coerce-functor`).
-- `liftFn-In` reduces the transported `In` denotation to `returnT (in-value v)`.
-- Framed as a combinator reduction (like `LiftFnReduce.liftFn-fst`): the TRACE
-- is `[]` (`rec-trace-D (In) = []`), the RESULT is `returns` of the coherence
-- `in-res` (the μ-twin of `AnaErased.coerce-νin-erase`, wrapped by
-- `sem-In = ⟨_⟩∘coerce-μ-in`).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.InErased (fmt : TargetNum) (ρ : CallEnv) where

open import Function using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst; subst-subst-sym)

open import Once.Word using (Carrier)
open import Once.Type using (Functor; μ-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF; translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F; ⌊_⌋; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Semantics.Functor using (μS; ⟨_⟩; ⟦_⟧SF)
open import Once.Semantics.Machine using (tF-coh; ⟦_⟧F; coerce-μ-in)
open import Once.Denotation.TraceMonad using (T; returnT)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ; coerce-functor-D)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Meaning using (in-value)
open import Once.Adequacy.CataErased fmt ρ using (evalᴰ-subst-dom)
open import Once.Adequacy.AnaErased fmt ρ using (coerce-νin-erase-D; subst-T-returnT)
import Once.IR as IR

-- `coerce-μ-in G X x` computes structurally, IGNORING the carrier `X`, so it
-- commutes with a carrier subst.  Match-to-refl.
coerce-μ-in-subst : ∀ (G : Functor) {X X' : Set} (p : X ≡ X') (x : ⟦ G ⟧F X)
  → coerce-μ-in G X' (subst (λ Y → ⟦ G ⟧F Y) p x)
    ≡ subst (λ Y → ⟦ translateF Carrier Carrier G ⟧SF Y) p (coerce-μ-in G X x)
coerce-μ-in-subst G refl x = refl

-- Split a diagonal subst `⟦H⟧SF(μS H)` into carrier-subst then functor-subst.
subst-diag : ∀ {H₁ H₂ : Once.Semantics.Functor.SFunctor} (eq : H₁ ≡ H₂)
               (z : ⟦ H₁ ⟧SF (μS H₁))
  → subst (λ H → ⟦ H ⟧SF (μS H)) eq z
    ≡ subst (λ H → ⟦ H ⟧SF (μS H₂)) eq (subst (λ C → ⟦ H₁ ⟧SF C) (cong μS eq) z)
subst-diag refl z = refl

-- The transported `In` morphism `realize` uses (Realize:156 / :104).
In-ir : ∀ {F : Functor} → WellFormedF F → IR.IR ⌊ ⟦ F ⟧T (μ-type F) ⌋ ⌊ μ-type F ⌋
In-ir {F} wfF = subst (λ o → IR.IR o ⌊ μ-type F ⌋)
                      (sym (⌊⟧T-commute F (μ-type F)))
                      (IR.In (wf-⌊⌋ wfF))

-- `⟨_⟩` (the μS "in" constructor) commutes with a subst over the functor eq.
-- Match-to-refl.
⟨⟩-subst-nat : ∀ {H₁ H₂ : Once.Semantics.Functor.SFunctor} (eq : H₁ ≡ H₂)
                 (z : ⟦ H₁ ⟧SF (μS H₁))
  → subst μS eq ⟨ z ⟩ ≡ ⟨ subst (λ H → ⟦ H ⟧SF (μS H)) eq z ⟩
⟨⟩-subst-nat refl z = refl

-- `subst id (cong μS p) = subst μS p`.  Match-to-refl.
subst-id-μS : ∀ {H₁ H₂ : Once.Semantics.Functor.SFunctor} (p : H₁ ≡ H₂) (z : μS H₁)
  → subst id (cong μS p) z ≡ subst μS p z
subst-id-μS refl z = refl

-- Bridge the innermost subst from `evalᴰ-subst-dom`'s `subst ⟦_⟧ᴰᴵ (sym(sym p))`
-- (IRTy-level) to `coerce-νin-erase`'s `subst id (cong ⟦_⟧ᴰᴵ p)` (Set-level) —
-- same value, different universe level.  Match-to-refl.
open import Once.IRTy using (IRTy)
subst-⟦⟧ᴰᴵ-fix : ∀ {X Y : IRTy} (p : X ≡ Y) (x : ⟦ X ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (sym p)) x ≡ subst id (cong ⟦_⟧ᴰᴵ p) x
subst-⟦⟧ᴰᴵ-fix refl x = refl

-- The combinator reduction (like `LiftFnReduce.liftFn-fst`): `liftFn` of the
-- transported `In` is `returnT (in-value v)`. Plan 0.105: one equation of
-- trees — the domain transport peels (`evalᴰ-subst-dom`), the result
-- transport moves into the `ret` leaf, and what remains is the μ-twin of
-- `AnaErased.coerce-νin-erase-D` at the value.
liftFn-In : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ)
  → liftFn fmt ρ {⟦ F ⟧T (μ-type F)} {μ-type F} (In-ir wfF) v ≡ returnT (in-value wfF v)
liftFn-In {F} wfF v =
  trans (cong (subst T (cohᴰ (μ-type F)))
              (evalᴰ-subst-dom (sym (⌊⟧T-commute F (μ-type F))) (IR.In (wf-⌊⌋ wfF)) v′))
  (trans (cong (λ arg → subst T (cohᴰ (μ-type F)) (evalᴰ fmt ρ (IR.In (wf-⌊⌋ wfF)) arg))
               (subst-⟦⟧ᴰᴵ-fix (⌊⟧T-commute F (μ-type F)) v′))
  (trans (subst-T-returnT (cohᴰ (μ-type F)) _)
  (cong returnT
    (trans (subst-id-μS (tF-coh F) _)
    (trans (⟨⟩-subst-nat (tF-coh F) _)
           (cong ⟨_⟩
             (trans (subst-diag (tF-coh F) _)
             (trans (cong (subst (λ H → ⟦ H ⟧SF ⟦ μ-type F ⟧ᴰ) (tF-coh F))
                          (sym (coerce-μ-in-subst ⌈ eraseF F ⌉F (cohᴰ (μ-type F)) _)))
                    (trans (coerce-νin-erase-D wfF (μ-type F) v′)
                           (cong (λ x → coerce-μ-in F ⟦ μ-type F ⟧ᴰ (coerce-functor-D wfF (μ-type F) x))
                                 (subst-subst-sym (cohᴰ (⟦ F ⟧T (μ-type F))))))))))))))
  where
    v′ = subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v
