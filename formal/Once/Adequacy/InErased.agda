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
-- is `[]` (`rec-trace-D (In) = []`), the VALUE is the coherence `in-value-erase`
-- (the μ-twin of `AnaErased.coerce-νin-erase`, wrapped by `sem-In = ⟨_⟩∘coerce-μ-in`).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.InErased (fmt : TargetNum) where

open import Function using (id)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst-subst-sym)

open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Type using (Type; Functor; μ-type; ⟦_⟧T)
open import Once.Functor.Translate using (WellFormedF; translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F; ⌈_⌉; ⌊_⌋; ⌊⟧T-commute; ⌈⟧TI-commute)
open import Once.IRTy.WF using (wf-⌊⌋)
open import Once.Semantics.Functor using (μS; ⟨_⟩; ⟦_⟧SF)
open import Once.Semantics.Machine using (sem-In; coerce-functor; coh; tF-coh; ⟦_⟧; ⟦_⟧F; ⟦μ⟧; coerce-μ-in)
open import Once.Denotation.TraceMonad using (T; returnT; projTrace)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; forget; inject; cohᴰ)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Meaning using (in-value)
open import Once.Adequacy.CataErased fmt using (subst-T-apply; subst-T-projTrace; evalᴰ-subst-dom)
open import Once.Adequacy.AnaErased fmt using (coerce-νin-erase)
open import Once.Postulates using (extensionality)
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
                      (IR.In (wf-⌊⌋ wfF) IR.Heap)

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

-- TRACE half: `[]` — `subst T` doesn't touch the trace; `evalᴰ-subst-dom` peels
-- the domain subst; `rec-trace-D (In) = []` is definitional.
in-trace : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ) (n : ℕ)
  → projTrace (liftFn fmt (In-ir wfF) v) n ≡ []
in-trace {F} wfF v n =
  trans (subst-T-projTrace (cong μS (tF-coh F))
          (evalᴰ fmt (In-ir wfF) (subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v)) n)
        (cong (λ hh → projTrace hh n)
          (evalᴰ-subst-dom (sym (⌊⟧T-commute F (μ-type F))) (IR.In (wf-⌊⌋ wfF) IR.Heap)
                           (subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v)))

-- VALUE half — the coherence (PROBE: refl to read the goal).
in-value-erase : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ) (n : ℕ)
  → proj₂ (liftFn fmt (In-ir wfF) v n) ≡ in-value v
in-value-erase {F} wfF v n =
  trans (cong proj₂ (subst-T-apply (cong μS (tF-coh F))
                      (evalᴰ fmt (In-ir wfF) (subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v)) n))
  (trans (cong (λ hh → subst id (cong μS (tF-coh F)) (proj₂ (hh n)))
               (evalᴰ-subst-dom (sym (⌊⟧T-commute F (μ-type F))) (IR.In (wf-⌊⌋ wfF) IR.Heap)
                                (subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v)))
  (trans (cong (λ arg → subst id (cong μS (tF-coh F))
                         (proj₂ (evalᴰ fmt (IR.In (wf-⌊⌋ wfF) IR.Heap) arg n)))
               (subst-⟦⟧ᴰᴵ-fix (⌊⟧T-commute F (μ-type F)) (subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v)))
  (trans (subst-id-μS (tF-coh F) _)
  (trans (⟨⟩-subst-nat (tF-coh F) _)
         (cong ⟨_⟩
           (trans (subst-diag (tF-coh F) _)
           (trans (cong (subst (λ H → ⟦ H ⟧SF ⟦ μ-type F ⟧) (tF-coh F))
                        (sym (coerce-μ-in-subst ⌈ eraseF F ⌉F (coh (μ-type F)) _)))
                  (trans (coerce-νin-erase F (μ-type F) (subst id (sym (cohᴰ (⟦ F ⟧T (μ-type F)))) v))
                         (cong (λ x → coerce-μ-in F ⟦ μ-type F ⟧ (coerce-functor F (μ-type F) (forget x)))
                               (subst-subst-sym (cohᴰ (⟦ F ⟧T (μ-type F)))))))))))))

-- The combinator reduction (like `LiftFnReduce.liftFn-fst`): `liftFn` of the
-- transported `In` is `returnT (in-value v)` — trace `[]`, value `in-value-erase`
-- (the value is n-independent, so `in-value-erase` at 0 covers every `n`).
liftFn-In : ∀ {F : Functor} (wfF : WellFormedF F) (v : ⟦ ⟦ F ⟧T (μ-type F) ⟧ᴰ)
  → liftFn fmt (In-ir wfF) v ≡ returnT (in-value v)
liftFn-In wfF v = extensionality λ n → cong₂ _,_ (in-trace wfF v n) (in-value-erase wfF v n)
