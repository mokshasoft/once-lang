-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.ThinSound — the source denotation is STABLE UNDER THINNING.
--
--   ⟦ rename θ e ⟧ˢ fmt dδ ≡ ⟦ e ⟧ˢ fmt (restrictᴰ θ dδ)
--
-- Why this exists (D126). `Once.Surface.Thinning.rename` had, until now, no
-- semantic justification anywhere — every construct that needed a closed
-- subterm either carried it in the EMPTY context (`cata`/`ana`) or embedded a
-- pre-built IR morphism (`lift-morphism`), so nothing ever had to say what
-- renaming MEANS. D126's closed-expression lift is the first construct whose
-- realization weakens a genuine subterm (`λ_. e` needs `e` one context deeper),
-- and its adequacy (`RealizeAgrees.agree-embedOrSubsume-no`) is exactly the
-- statement that the two weakened bodies agree. That needs this.
--
-- The proof is the textbook structural induction; the only real content is the
-- `var` case (thinning preserves lookup, at the level of ENVIRONMENTS rather
-- than types) and peeling `rename`'s usage transports, which `⟦_⟧ˢ` ignores
-- because its result type does not mention the usage.
------------------------------------------------------------------------

module Once.Denotation.ThinSound where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Type as Type using (Type; One; Many; Zero; Unit; Void; Int; Float; Str; Buffer)
open import Once.Surface.Syntax as Surface using (Expr; Ctx; Usage; lookup; ⟦_⟧ᶜ; singleUse)
open import Once.Surface.Thinning
  using (_⊆_; done; skip; keep; rename; thin-var; thin-var-lookup; thin-usage-singleUse; thin-usage; substᵀ₂;
         thin-usage-+ᵘ; thin-usage-*ᵘ; thin-usage-zeroUsage; thin-usage-⊔ᵘ;
         weaken; ⊆-wk; ⊆-refl; thin-usage-refl)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ; cohᴰ; evalᴰ)
open import Once.Denotation.TraceMonad using (T; returnT; _>>=T_)
open import Once.Denotation.SourceDenote using (⟦_⟧ˢ; lookupᴰ)
open import Once.Postulates using (extensionality)
open import Once.Functor.Translate using (con-fun)
open import Once.SigOp.Info using (semM)
open import Once.Arith.SigOp.Builders
  using (add-info; sub-info; mul-info; div-info; mod-info;
         fadd-info; fsub-info; fmul-info; fdiv-info; i2f-info; neg-info;
         lt-info; le-info; gt-info; ge-info; eq-info; ne-info)
open import Once.Target.Arch using (TargetNum)

open Surface.Expr

------------------------------------------------------------------------
-- Environments along a thinning
------------------------------------------------------------------------

-- | The environment projection a thinning induces: `skip` drops the slot the
-- thinning added, `keep` keeps it. This is the semantic counterpart of
-- `thin-var`, and the `var` case below is the two agreeing.
restrictᴰ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m}
          → Γ ⊆ Δ → ⟦ ⟦ Δ ⟧ᶜ ⟧ᴰ → ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ
restrictᴰ done     dδ = dδ
restrictᴰ (skip θ) dδ = restrictᴰ θ (proj₁ dδ)
restrictᴰ (keep θ) dδ = restrictᴰ θ (proj₁ dδ) , proj₂ dδ

-- | Thinning preserves lookup — semantically. `thin-var-lookup` says the two
-- TYPES agree; this says the two VALUES do, transported along it.
lookupᴰ-thin : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m}
               (θ : Γ ⊆ Δ) (i : Fin n) (dδ : ⟦ ⟦ Δ ⟧ᶜ ⟧ᴰ)
             → subst ⟦_⟧ᴰ (thin-var-lookup θ i) (lookupᴰ Γ i (restrictᴰ θ dδ))
                 ≡ lookupᴰ Δ (thin-var θ i) dδ
lookupᴰ-thin (skip θ) i       dδ = lookupᴰ-thin θ i (proj₁ dδ)
lookupᴰ-thin (keep θ) zero    dδ = refl
lookupᴰ-thin (keep θ) (suc i) dδ = lookupᴰ-thin θ i (proj₁ dδ)

------------------------------------------------------------------------
-- Peeling `rename`'s transports
------------------------------------------------------------------------

-- | `⟦_⟧ˢ`'s result type does not mention the usage, so `rename`'s usage
-- transports are invisible to it. Every non-leaf `rename` clause is wrapped in
-- one of these, and this is how each gets peeled.
⟦⟧-substΨ : ∀ {n} {Δ : Ctx n} {Ψ Ψ' : Usage n} {A : Type} {eq : Ψ ≡ Ψ'}
              (e : Expr Δ Ψ A) (fmt : TargetNum) (dδ : ⟦ ⟦ Δ ⟧ᶜ ⟧ᴰ)
          → ⟦ subst (λ Ψ'' → Expr Δ Ψ'' A) eq e ⟧ˢ fmt dδ ≡ ⟦ e ⟧ˢ fmt dδ
⟦⟧-substΨ {eq = refl} e fmt dδ = refl

-- | Congruence for the one- and two-scrutinee bind shapes `⟦_⟧ˢ` uses, so the
-- 30-odd structural clauses stay one-liners (no hand-written motives).
bind₁ : ∀ {A C : Set} {x x' : T A} (f : A → T C) → x ≡ x' → (x >>=T f) ≡ (x' >>=T f)
bind₁ f refl = refl

bind₂ : ∀ {A B C : Set} {x x' : T A} {y y' : T B} (f : A → B → T C)
      → x ≡ x' → y ≡ y' → (x >>=T λ a → y >>=T λ b → f a b)
                        ≡ (x' >>=T λ a → y' >>=T λ b → f a b)
bind₂ f refl refl = refl

-- | The `var` clause's DOUBLE transport. Only the type half survives into the
-- denotation (the usage half is invisible, as above).
⟦⟧-subst₂ : ∀ {n} {Δ : Ctx n} {Ψ Ψ' : Usage n} {A A' : Type}
              (eΨ : Ψ ≡ Ψ') (eA : A ≡ A') (e : Expr Δ Ψ A)
              (fmt : TargetNum) (dδ : ⟦ ⟦ Δ ⟧ᶜ ⟧ᴰ)
          → ⟦ substᵀ₂ (Expr Δ) eΨ eA e ⟧ˢ fmt dδ
              ≡ subst (λ B → T ⟦ B ⟧ᴰ) eA (⟦ e ⟧ˢ fmt dδ)
⟦⟧-subst₂ refl refl e fmt dδ = refl

subst-returnT : ∀ {A B : Type} (e : A ≡ B) (x : ⟦ A ⟧ᴰ)
              → subst (λ C → T ⟦ C ⟧ᴰ) e (returnT x) ≡ returnT (subst ⟦_⟧ᴰ e x)
subst-returnT refl x = refl

subst-sym-move : ∀ {A B : Type} (e : A ≡ B) (x : ⟦ A ⟧ᴰ) (y : ⟦ B ⟧ᴰ)
               → subst ⟦_⟧ᴰ e x ≡ y → subst ⟦_⟧ᴰ (sym e) y ≡ x
subst-sym-move refl x .x refl = refl

------------------------------------------------------------------------
-- Congruences for the shapes with a binder
------------------------------------------------------------------------

bindᶠ : ∀ {A C : Set} {x x' : T A} {f f' : A → T C}
      → x ≡ x' → (∀ a → f a ≡ f' a) → (x >>=T f) ≡ (x' >>=T f')
bindᶠ {x = x} refl hf = cong (λ g → x >>=T g) (extensionality hf)

case-cong : ∀ {A B D : Set} {x x' : T (A ⊎ B)} {l l' : A → T D} {r r' : B → T D}
          → x ≡ x' → (∀ a → l a ≡ l' a) → (∀ b → r b ≡ r' b)
          → (x >>=T λ v → [ l , r ]′ v) ≡ (x' >>=T λ v → [ l' , r' ]′ v)
case-cong {x = x} refl hl hr =
  cong₂ (λ l r → x >>=T λ v → [ l , r ]′ v) (extensionality hl) (extensionality hr)

------------------------------------------------------------------------
-- THE LEMMA
------------------------------------------------------------------------

thin-⟦⟧ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ : Usage n} {A : Type}
            (θ : Γ ⊆ Δ) (e : Expr Γ Ψ A) (fmt : TargetNum) (dδ : ⟦ ⟦ Δ ⟧ᶜ ⟧ᴰ)
        → ⟦ rename θ e ⟧ˢ fmt dδ ≡ ⟦ e ⟧ˢ fmt (restrictᴰ θ dδ)

-- The `var` case IS the lemma; everything else is plumbing. Both of `rename`'s
-- transports have to become `refl` before its local `subst₂` reduces, so both
-- are abstracted — and then `lookupᴰ-thin` is exactly the remaining content.
-- J-STYLE, not `with`: both of `rename`'s transports are between STUCK terms,
-- so `refl` has nothing to unify. Instead quantify over the equations, let `J`
-- (pattern-matching them in the helpers) discharge them, and the var case is
-- then just `lookupᴰ-thin` moved across one `sym`.
thin-⟦⟧ {Γ = Γ} {Δ = Δ} θ (var i) fmt dδ =
  trans (⟦⟧-subst₂ (sym (thin-usage-singleUse θ i One))
                   (sym (thin-var-lookup θ i)) (var (thin-var θ i)) fmt dδ)
        (trans (subst-returnT (sym (thin-var-lookup θ i)) _)
               (cong returnT (subst-sym-move (thin-var-lookup θ i) _ _
                                             (lookupᴰ-thin θ i dδ))))

thin-⟦⟧ θ (lam q p e) fmt dδ =
  cong returnT (extensionality (λ a → thin-⟦⟧ (keep θ) e fmt (dδ , a)))
thin-⟦⟧ θ (app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} f x) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (trans (thin-usage-+ᵘ θ Ψ₁ (q Surface.*ᵘ Ψ₂))
                                    (cong (Surface._+ᵘ_ (thin-usage θ Ψ₁))
                                          (thin-usage-*ᵘ θ q Ψ₂)))}
                   (app (rename θ f) (rename θ x)) fmt dδ)
        (bind₂ (λ vf vx → vf vx) (thin-⟦⟧ θ f fmt dδ) (thin-⟦⟧ θ x fmt dδ))
thin-⟦⟧ θ (effApp {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f x) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (effApp (rename θ f) (rename θ x)) fmt dδ)
        (cong returnT (extensionality (λ _ →
          bind₂ (λ vf vx → vf vx) (thin-⟦⟧ θ f fmt dδ) (thin-⟦⟧ θ x fmt dδ))))
thin-⟦⟧ θ (pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (pair (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (va , vb))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
-- D127: the combinators. Usage `Ψ₁ +ᵘ Ψ₂`, so they thin exactly as `pair`
-- does; `curry'` leaves the usage alone and thins as `fst'` does.
thin-⟦⟧ θ (comp' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (comp' (rename θ f) (rename θ g)) fmt dδ)
        (bind₂ (λ vf vg → returnT (λ a → vg a >>=T vf))
               (thin-⟦⟧ θ f fmt dδ) (thin-⟦⟧ θ g fmt dδ))
thin-⟦⟧ θ (copair' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (copair' (rename θ f) (rename θ g)) fmt dδ)
        (bind₂ (λ vf vg → returnT (λ ab → [ vf , vg ]′ ab))
               (thin-⟦⟧ θ f fmt dδ) (thin-⟦⟧ θ g fmt dδ))
thin-⟦⟧ θ (fork' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} f g) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (fork' (rename θ f) (rename θ g)) fmt dδ)
        (bind₂ (λ vf vg → returnT (λ a → vf a >>=T λ b → vg a >>=T λ c → returnT (b , c)))
               (thin-⟦⟧ θ f fmt dδ) (thin-⟦⟧ θ g fmt dδ))
thin-⟦⟧ θ (curry' f) fmt dδ =
  bind₁ (λ vf → returnT (λ a → returnT (λ b → vf (a , b)))) (thin-⟦⟧ θ f fmt dδ)
thin-⟦⟧ θ (fst' p) fmt dδ = bind₁ (λ v → returnT (proj₁ v)) (thin-⟦⟧ θ p fmt dδ)
thin-⟦⟧ θ (snd' p) fmt dδ = bind₁ (λ v → returnT (proj₂ v)) (thin-⟦⟧ θ p fmt dδ)
thin-⟦⟧ θ (arr' f) fmt dδ = thin-⟦⟧ θ f fmt dδ
thin-⟦⟧ θ (inl' a) fmt dδ = bind₁ (λ v → returnT (inj₁ v)) (thin-⟦⟧ θ a fmt dδ)
thin-⟦⟧ θ (inr' b) fmt dδ = bind₁ (λ v → returnT (inj₂ v)) (thin-⟦⟧ θ b fmt dδ)
thin-⟦⟧ θ (case' {Ψs = Ψs} {Ψₗ = Ψₗ} {Ψᵣ = Ψᵣ} s l r) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (trans (thin-usage-+ᵘ θ Ψs (Ψₗ Surface.⊔ᵘ Ψᵣ))
                                    (cong (Surface._+ᵘ_ (thin-usage θ Ψs))
                                          (thin-usage-⊔ᵘ θ Ψₗ Ψᵣ)))}
                   (case' (rename θ s) (rename (keep θ) l) (rename (keep θ) r)) fmt dδ)
        (case-cong (thin-⟦⟧ θ s fmt dδ)
                   (λ a → thin-⟦⟧ (keep θ) l fmt (dδ , a))
                   (λ b → thin-⟦⟧ (keep θ) r fmt (dδ , b)))
thin-⟦⟧ {Δ = Δ} θ unit fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (unit {Γ = Δ}) fmt dδ) refl
thin-⟦⟧ θ (absurd v) fmt dδ = bind₁ (λ x → ⊥-elim x) (thin-⟦⟧ θ v fmt dδ)
thin-⟦⟧ θ (let' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = q} e₁ e₂) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (trans (thin-usage-+ᵘ θ Ψ₂ (q Surface.*ᵘ Ψ₁))
                                    (cong (Surface._+ᵘ_ (thin-usage θ Ψ₂))
                                          (thin-usage-*ᵘ θ q Ψ₁)))}
                   (let' (rename θ e₁) (rename (keep θ) e₂)) fmt dδ)
        (bindᶠ (thin-⟦⟧ θ e₁ fmt dδ) (λ v → thin-⟦⟧ (keep θ) e₂ fmt (dδ , v)))
thin-⟦⟧ {Δ = Δ} θ (int n) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (int {Γ = Δ} n) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (str s) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (str {Γ = Δ} s) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (float d) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (float {Γ = Δ} d) fmt dδ) refl
thin-⟦⟧ θ (i2f a) fmt dδ = bind₁ (λ v → returnT (semM i2f-info fmt v)) (thin-⟦⟧ θ a fmt dδ)
thin-⟦⟧ θ (neg a) fmt dδ = bind₁ (λ v → returnT (semM neg-info fmt v)) (thin-⟦⟧ θ a fmt dδ)
thin-⟦⟧ θ (add {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (add (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM add-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (sub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (sub (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM sub-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (mul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (mul (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM mul-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (fadd {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (fadd (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM fadd-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (fsub {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (fsub (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM fsub-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (fmul {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (fmul (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM fmul-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (fdiv {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (fdiv (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM fdiv-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (div {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (div (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM div-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (mod' {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (mod' (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM mod-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (lt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (lt (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM lt-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (le {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (le (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM le-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (gt {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (gt (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM gt-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (ge {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (ge (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM ge-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (eq {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (eq (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM eq-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
thin-⟦⟧ θ (ne {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} a b) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-+ᵘ θ Ψ₁ Ψ₂)}
                   (ne (rename θ a) (rename θ b)) fmt dδ)
        (bind₂ (λ va vb → returnT (semM ne-info fmt (va , vb)))
               (thin-⟦⟧ θ a fmt dδ) (thin-⟦⟧ θ b fmt dδ))
-- `sigOp` is the one leaf whose denotation DISPATCHES on its result type (an
-- arrow is a closure that fires the effect on application; anything else runs
-- on `terminal`), so the type has to be split before either side reduces.
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = _ Type.⇒[ _ ] _} name (con-fun bDom cCod)) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name (con-fun bDom cCod)) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = Unit} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = Void} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = Int} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = Float} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = Str} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = Buffer} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = (_ Type.* _)} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = (_ Type.+ _)} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = (Type.μ-type _)} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (sigOp {A = (Type.ν-type _)} name conc) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)}
                   (sigOp {Γ = Δ} name conc) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (closure name) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (closure {Γ = Δ} name) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (poly name PT) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (poly {Γ = Δ} name PT) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (lift-morphism m) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (lift-morphism {Γ = Δ} m) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (cata wf alg) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (cata {Γ = Δ} wf alg) fmt dδ) refl
thin-⟦⟧ {Δ = Δ} θ (ana wf coalg) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (thin-usage-zeroUsage θ)} (ana {Γ = Δ} wf coalg) fmt dδ) refl
-- The only clause whose continuation has to be written out: its transports
-- (`cohᴰ`, the grade-erasure coercion) block inference of the motive.
thin-⟦⟧ {Δ = Δ} θ (morph-app {A = A} {B = B} m x) fmt dδ =
  trans (⟦⟧-substΨ {eq = sym (trans (thin-usage-+ᵘ θ Surface.zeroUsage (Many Surface.*ᵘ _))
                                    (cong₂ Surface._+ᵘ_ (thin-usage-zeroUsage θ)
                                                        (thin-usage-*ᵘ θ Many _)))}
                   (morph-app m (rename θ x)) fmt dδ)
        (bind₁ (λ v → subst T (cohᴰ B)
                        (evalᴰ fmt m (subst (λ z → z) (sym (cohᴰ A)) v)))
               (thin-⟦⟧ θ x fmt dδ))

------------------------------------------------------------------------
-- The corollary D126 actually needs
------------------------------------------------------------------------

restrictᴰ-refl : ∀ {n} {Γ : Ctx n} (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) → restrictᴰ (⊆-refl {Γ = Γ}) dγ ≡ dγ
restrictᴰ-refl {Γ = Surface.∅}         dγ = refl
restrictᴰ-refl {Γ = Γ Surface., A ^ q} dγ =
  cong (λ z → z , proj₂ dγ) (restrictᴰ-refl {Γ = Γ} (proj₁ dγ))

-- `weaken`'s transport has a different motive from `rename`'s (the new slot's
-- `Zero` sits outside), so it gets its own peel.
⟦⟧-substΨ-cons : ∀ {n} {Δ : Ctx (ℕ.suc n)} {Ψ Ψ' : Usage n} {A : Type} {eq : Ψ ≡ Ψ'}
                   (e : Expr Δ (Zero Surface.∷ Ψ) A)
                   (fmt : TargetNum) (dδ : ⟦ ⟦ Δ ⟧ᶜ ⟧ᴰ)
               → ⟦ subst (λ Ψ'' → Expr Δ (Zero Surface.∷ Ψ'') A) eq e ⟧ˢ fmt dδ
                   ≡ ⟦ e ⟧ˢ fmt dδ
⟦⟧-substΨ-cons {eq = refl} e fmt dδ = refl

-- | WEAKENING IS INVISIBLE TO THE MEANING. This is the fact D126's adequacy
-- turns on: the closed lift realizes as `λ_. e`, on both the elaborator's and
-- `realize`'s side, so their agreement is the two `e`s agreeing one context up.
weaken-⟦⟧ : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {A B : Type} {q}
              (e : Expr Γ Ψ B) (fmt : TargetNum)
              (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (a : ⟦ A ⟧ᴰ)
          → ⟦ weaken {A = A} {q = q} e ⟧ˢ fmt (dγ , a) ≡ ⟦ e ⟧ˢ fmt dγ
weaken-⟦⟧ {Γ = Γ} {Ψ = Ψ} e fmt dγ a =
  trans (⟦⟧-substΨ-cons {eq = thin-usage-refl Ψ} (rename ⊆-wk e) fmt (dγ , a))
        (trans (thin-⟦⟧ ⊆-wk e fmt (dγ , a))
               (cong (⟦ e ⟧ˢ fmt) (restrictᴰ-refl {Γ = Γ} dγ)))
