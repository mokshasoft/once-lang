------------------------------------------------------------------------
-- OCP-0009 · Positive η (`sum-η`, `μ-η`) as SURFACE SUGAR (§3.A / §4.6)
--
-- The §2 design line: negative η (`Unit`, `×`, `⇒`) is CHEAP — decided by
-- `reflect` — and is baked into core conversion (done: `NbEP`/`NbEKF`/
-- `NbEPF`). Positive η (`sum-η : [inl,inr] ≈ id`, `μ-η : In ∘ Out ≈ id`)
-- is EXPENSIVE for a checker (sheaf NbE / commuting conversions) and — by
-- Hofmann's conservativity — adds NO new theorems. So the design says:
-- keep it OUT of core conversion, provide it as surface sugar that
-- elaborates to EXPLICIT PROPOSITIONAL PROOFS. This module is those proofs.
--
--   * `sum-η-prop` / `μ-η-prop` — the two laws as theorems of the
--     (`--safe`) Set-model: pointwise, by case analysis. These are the
--     proof terms the surface elaboration inserts (the "transport clutter"
--     §3.A names as the — right — price of a minimal TCB).
--   * The demonstration pair: `nf` deliberately does NOT equate
--     `[inl,inr] ∘ Out` with `Out` (the sum-typed result is a genuine
--     neutral — positive η is not core conversion), yet the propositional
--     proof `sum-η-prop` closes the same equation in the model, ready to be
--     transported along. Definitional-vs-propositional, again — this time
--     as a design CHOICE, not a limitation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPEta where

open import normalizer.Syntax.Types
open import normalizer.Syntax.CCC as C using ()
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; ⟦_⟧FS; Fix; fix; eval; coherence; coherence⁻¹ )

------------------------------------------------------------------------
-- The two positive-η laws, as propositional theorems of the Set-model.
------------------------------------------------------------------------

-- sum-η: `[inl , inr] ≈ id` — pointwise, by case analysis on the sum.
sum-η-prop : ∀ {X Y} (v : ⟦ X + Y ⟧T) →
             eval (C.[_,_] {X} {Y} C.inl C.inr) v ≡ v
sum-η-prop (inj₁ a) = refl
sum-η-prop (inj₂ b) = refl

-- μ-η: `In ∘ Out ≈ id` — by case analysis on the fixpoint value, via the
-- round-trip of the Evaluator's functor-representation coherence maps.
coh∘coh⁻¹ : ∀ F A (y : ⟦ F ⟧FS ⟦ A ⟧T) →
            coherence F A (coherence⁻¹ F A y) ≡ y
coh∘coh⁻¹ Id      A y        = refl
coh∘coh⁻¹ One     A y        = refl
coh∘coh⁻¹ (Kc G)  A y        = refl
coh∘coh⁻¹ (F ⊕ G) A (inj₁ x) = cong inj₁ (coh∘coh⁻¹ F A x)
coh∘coh⁻¹ (F ⊕ G) A (inj₂ y) = cong inj₂ (coh∘coh⁻¹ G A y)
coh∘coh⁻¹ (F ⊗ G) A (x , y)  = cong₂ _,_ (coh∘coh⁻¹ F A x) (coh∘coh⁻¹ G A y)

μ-η-prop : ∀ {F} (v : ⟦ μ F ⟧T) →
           eval (C.In {F} C.∘ C.Out) v ≡ v
μ-η-prop {F} (fix x) = cong fix (coh∘coh⁻¹ F (μ F) x)

-- The composed forms the elaboration actually inserts: against an arbitrary
-- continuation `h`, positive η rewrites `[inl,inr] ∘ h ↦ h`, `In∘Out ∘ h ↦ h`
-- — justified pointwise, no funext.
sum-η-∘ : ∀ {A X Y} (h : C.Term A (X + Y)) (x : ⟦ A ⟧T) →
          eval (C.[_,_] C.inl C.inr C.∘ h) x ≡ eval h x
sum-η-∘ h x = sum-η-prop (eval h x)

μ-η-∘ : ∀ {A F} (h : C.Term A (μ F)) (x : ⟦ A ⟧T) →
        eval ((C.In {F} C.∘ C.Out) C.∘ h) x ≡ eval h x
μ-η-∘ h x = μ-η-prop (eval h x)

------------------------------------------------------------------------
-- The demonstration pair — the design line made visible on one example.
--
-- Definitional side (core conversion): `nf` does NOT decide sum-η — on a
-- neutral scrutinee, `[inl,inr]` stays a stuck case. That is §2's choice:
-- deciding it needs sheaf NbE, and Hofmann says we lose no theorems.
-- Propositional side (the sugar): the SAME equation, closed by
-- `sum-η-∘ C.Out` — the explicit proof the surface elaboration inserts.
------------------------------------------------------------------------

B₂F : Func
B₂F = One ⊕ One

lhs rhs : C.Term (μ B₂F) (Unit + Unit)
lhs = C.[_,_] C.inl C.inr C.∘ C.Out
rhs = C.Out

-- The propositional η-proof for this instance (what the sugar elaborates to):
sugar : ∀ x → eval lhs x ≡ eval rhs x
sugar = sum-η-∘ C.Out
