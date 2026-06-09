------------------------------------------------------------------------
-- normalizer.Theory.Eval.Idempotence
--
-- Denotational IDEMPOTENCE of the real normalizer: `eval normalize` applied
-- twice equals once. This module builds the CRUX — the comp position — and
-- (next) assembles the full theorem by structural induction (FixInduction).
--
-- The predicate is `Idem c = eval normalize (eval normalize c) ≡ eval
-- normalize c` ("the output is a normalize-fixpoint", i.e. already normal).
--
-- The comp case reduces to ONE real fact: `handle-comp` applied to two
-- normalize-fixpoints is itself a normalize-fixpoint (`handle-comp-normal`).
-- Both identity collapses (`id ∘ h`, `f ∘ id`) land on an already-normal
-- child; the rebuild branch lands on `comp-code v₁ v₂` whose re-normalisation
-- is pinned by `normalize-comp` + the children's normality + the rebuild
-- spec. Everything is with-FREE (lift to top-level `private`, abstract the
-- giant `eval handle-comp …` term behind a variable `r`) per the standing
-- memory rule.
--
-- Build: bootstrap/check.sh normalizer/Theory/Eval/Idempotence.agda
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module normalizer.Theory.Eval.Idempotence where

open import normalizer.Syntax.Types
  using (_≡_; refl; sym; trans; cong; cong₂; ⊤; tt; _×_; _,_; _⊎_; inj₁; inj₂)
open import normalizer.Encoding.Encoding using (TermF)
open import normalizer.Testing.Evaluator using (Fix; fix; eval)
open import normalizer.TCB0.Normalizer.Handlers using (normalize; handle-comp)
open import normalizer.TCB0.Normalizer.Dispatch using (is-id)
open import normalizer.Theory.Eval.HandlerCorrectness
  using (is-id-correct; handle-comp-spec-id-left;
         handle-comp-spec-id-right; handle-comp-spec-rebuild)
open import normalizer.Theory.Eval.StepTransparency
  using (comp-code; pair-code; case-code; normalize-comp)
open import normalizer.Theory.Eval.FixInduction using (All-rec; induct)

------------------------------------------------------------------------
-- The idempotence predicate: `c`'s normal form is a normalize-fixpoint.
------------------------------------------------------------------------

Idem : Fix TermF → Set
Idem c = eval normalize (eval normalize c) ≡ eval normalize c

------------------------------------------------------------------------
-- CRUX: handle-comp of two normalize-fixpoints is a normalize-fixpoint.
--
-- `hcn-aux` abstracts the handler output `eval handle-comp (v₁ , v₂)` behind
-- a fresh `r` (+ refl witness) and pattern-matches the two small `is-id`
-- decisions — no `with`, so the giant term is never re-expanded.
------------------------------------------------------------------------

private
  -- Transport a normality fact along `r ≡ s`: from `eval normalize s ≡ s`
  -- conclude `eval normalize r ≡ r`.
  along : ∀ (r s : Fix TermF) → r ≡ s → eval normalize s ≡ s → eval normalize r ≡ r
  along r s req hs = trans (cong (eval normalize) req) (trans hs (sym req))

  hcn-aux :
    ∀ (v₁ v₂ r : Fix TermF) →
    eval handle-comp (v₁ , v₂) ≡ r →
    eval normalize v₁ ≡ v₁ → eval normalize v₂ ≡ v₂ →
    (eval is-id v₁ ≡ inj₁ tt) ⊎ (eval is-id v₁ ≡ inj₂ v₁) →
    (eval is-id v₂ ≡ inj₁ tt) ⊎ (eval is-id v₂ ≡ inj₂ v₂) →
    eval normalize r ≡ r
  -- v₁ = id  →  handle-comp (v₁ , v₂) = v₂, already normal (h₂).
  hcn-aux v₁ v₂ r eq h₁ h₂ (inj₁ y₁) _ =
    along r v₂ (trans (sym eq) (handle-comp-spec-id-left v₁ v₂ y₁)) h₂
  -- v₁ ≠ id, v₂ = id  →  handle-comp = v₁, already normal (h₁).
  hcn-aux v₁ v₂ r eq h₁ h₂ (inj₂ n₁) (inj₁ y₂) =
    along r v₁ (trans (sym eq) (handle-comp-spec-id-right v₁ v₂ v₁ n₁ y₂)) h₁
  -- both ≠ id  →  handle-comp = comp-code v₁ v₂; its re-normalisation is
  -- itself, since the (already-normal) children rebuild unchanged.
  hcn-aux v₁ v₂ r eq h₁ h₂ (inj₂ n₁) (inj₂ n₂) =
    along r (comp-code v₁ v₂)
          (trans (sym eq) (handle-comp-spec-rebuild v₁ v₂ v₁ v₂ n₁ n₂))
          (trans (normalize-comp v₁ v₂)
                 (trans (cong₂ (λ a b → eval handle-comp (a , b)) h₁ h₂)
                        (handle-comp-spec-rebuild v₁ v₂ v₁ v₂ n₁ n₂)))

handle-comp-normal :
  ∀ (v₁ v₂ : Fix TermF) →
  eval normalize v₁ ≡ v₁ → eval normalize v₂ ≡ v₂ →
  eval normalize (eval handle-comp (v₁ , v₂)) ≡ eval handle-comp (v₁ , v₂)
handle-comp-normal v₁ v₂ h₁ h₂ =
  hcn-aux v₁ v₂ (eval handle-comp (v₁ , v₂)) refl h₁ h₂
          (is-id-correct v₁) (is-id-correct v₂)

------------------------------------------------------------------------
-- The comp case of idempotence: from idempotence on both children.
------------------------------------------------------------------------

comp-idem : ∀ (c₁ c₂ : Fix TermF) → Idem c₁ → Idem c₂ → Idem (comp-code c₁ c₂)
comp-idem c₁ c₂ ih₁ ih₂ =
  trans (cong (eval normalize) (normalize-comp c₁ c₂))
        (trans (handle-comp-normal (eval normalize c₁) (eval normalize c₂) ih₁ ih₂)
               (sym (normalize-comp c₁ c₂)))

------------------------------------------------------------------------
-- The induction method: one clause per TermF position. `x` is the raw
-- functor LAYER ⟦TermF⟧FS (Fix TermF) (a coproduct, NOT under `fix`).
-- Leaves are normalize-fixpoints (refl); rebuild positions close by
-- cong/cong₂ over the IHs; comp uses the crux comp-idem. NO `with`.
------------------------------------------------------------------------

idem-step : ∀ x → All-rec TermF TermF Idem x → Idem (fix x)
idem-step (inj₁ _) _ = refl
idem-step (inj₂ (inj₁ (c₁ , c₂))) (ih₁ , ih₂) = comp-idem c₁ c₂ ih₁ ih₂
idem-step (inj₂ (inj₂ (inj₁ _))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₁ _)))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (c₁ , c₂)))))) (ih₁ , ih₂) = cong₂ pair-code ih₁ ih₂
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (c₁ , c₂))))))))) (ih₁ , ih₂) = cong₂ case-code ih₁ ih₂
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))))))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _))))))))))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ _)))))))))))) _ = refl
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (ff , alg)))))))))))))) (_ , ih) = cong (λ b → fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (ff , b))))))))))))))) ih
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (ab , (cc , body)))))))))))))))) (_ , (_ , ih)) = cong (λ b → fix (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (ab , (cc , b))))))))))))))))) ih
idem-step (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (_))))))))))))))) _ = refl

------------------------------------------------------------------------
-- Denotational idempotence of `eval normalize`, by structural induction.
------------------------------------------------------------------------

idempotent : ∀ (c : Fix TermF) → eval normalize (eval normalize c) ≡ eval normalize c
idempotent = induct TermF Idem idem-step
