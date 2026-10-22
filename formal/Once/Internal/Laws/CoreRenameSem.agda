-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Laws.CoreRenameSem — plan 0.103 6b, step B.1 (plan 0.122: over
-- the Spec core): the core meaning is STABLE UNDER RENAMING.
--
--   ⟦ ren-⊢ θ ρ h c d ⟧ fmt δ x ≡ ⟦ d ⟧ fmt δ (thinᴰ c Ψ x)
--
-- The derived combinators weaken an arm (`wk-⊢`), so the 6b bridge (surface
-- meaning = core meaning of the elaboration) needs to know what renaming
-- MEANS. The core meaning runs over the RUNTIME environment `Γ ↾ Ψ` (D143),
-- whose shape depends on the usage, and `ren-⊢` moves a usage by a cast (a
-- sub-usaging, i.e. a restriction); so besides the environment thinning
-- `thinᴰ` the proof needs:
--   * `_⊑ᵘ_` is proof-irrelevant, so `restrictᵛ` does not see its witness;
--   * `restrictᵛ` commutes with `thinᴰ`.
-- (The term model's own renaming lemma, `Metatheory.TermModel.Ren`, is
-- relational; the compiler needs it on the nose.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Internal.Laws.CoreRenameSem (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Once.Postulates using (extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; eff; fin; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; KCtx)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _⊑∷_; _⊑ᵘ_; singleUse; lookup)
open import Once.Internal.Context using (_+ᵘ_; _*ᵘ_; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Internal.Graded using (⟦_⟧ᵛ; M; bindM; bindᵍ)
open import Once.Internal.Environment using (restrictᵛ; bindᵛ; lookupᵛUsed)
open import Once.Denotation.EnvAlgebraV using (⊑ᵘ-unique; restrict-∘)
open import Once.Internal.GradedOps using (fmapM)
open import Once.Spec.Core.Typing Σ S
open import Once.Metatheory.TermModel.Subst Σ S
  using (Thin; done; keep; skip; ⟦_⟧θ; _θ*_; θ*-mono; idθ; idθ-id; CThin; cdone; ckeep; cskip; cid; cthin-lookup;
         θ*-id; retype; varAt; ren-⊢; wk-⊢)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-≡)
open import Once.Internal.Core.Meaning Σ S using (⟦_⟧; DefSem; Env)

------------------------------------------------------------------------
-- The environment a thinning induces
------------------------------------------------------------------------

-- `skip` drops the slot the thinning added (its usage is `Zero`, so the
-- runtime environment has no slot for it); `keep` keeps a slot iff it is live.
thinᴰ : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) (Ψ : Usage n)
      → Env Γ′ (θ θ* Ψ) → Env Γ Ψ
thinᴰ cdone     []         x = x
thinᴰ (cskip c) Ψ          x = thinᴰ c Ψ x
thinᴰ (ckeep c) (Zero ∷ Ψ) x = thinᴰ c Ψ x
thinᴰ (ckeep c) (One  ∷ Ψ) x = thinᴰ c Ψ (proj₁ x) , proj₂ x
thinᴰ (ckeep c) (Many ∷ Ψ) x = thinᴰ c Ψ (proj₁ x) , proj₂ x

------------------------------------------------------------------------
-- Thinning and restriction commute
------------------------------------------------------------------------

thin-restrict : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ′ Ψ : Usage n}
                (u : Ψ′ ⊑ᵘ Ψ) (x : Env Γ′ (θ θ* Ψ))
              → thinᴰ c Ψ′ (restrictᵛ {Γ = Γ′} (θ*-mono θ u) x) ≡ restrictᵛ {Γ = Γ} u (thinᴰ c Ψ x)
thin-restrict cdone     []                 x = refl
thin-restrict (cskip c) u                  x = thin-restrict c u x
thin-restrict (ckeep c) (0≤q {Zero} ⊑∷ u) x = thin-restrict c u x
thin-restrict (ckeep c) (0≤q {One}  ⊑∷ u) x = thin-restrict c u (proj₁ x)
thin-restrict (ckeep c) (0≤q {Many} ⊑∷ u) x = thin-restrict c u (proj₁ x)
thin-restrict (ckeep c) (1≤1 ⊑∷ u)        x = cong (_, proj₂ x) (thin-restrict c u (proj₁ x))
thin-restrict (ckeep c) (1≤ω ⊑∷ u)        x = cong (_, proj₂ x) (thin-restrict c u (proj₁ x))
thin-restrict (ckeep c) (ω≤ω ⊑∷ u)        x = cong (_, proj₂ x) (thin-restrict c u (proj₁ x))

-- The environment of a subterm: two restrictions (the cast `ren-⊢` puts on a
-- rule, then the rule's own split), thinned, are the split of the thinned one.
envEq : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ′ Ψ : Usage n} {U : Usage n′}
          (u : Ψ′ ⊑ᵘ Ψ) (u₁ : θ θ* Ψ′ ⊑ᵘ U) (u₂ : U ⊑ᵘ θ θ* Ψ) (x : Env Γ′ (θ θ* Ψ))
      → thinᴰ c Ψ′ (restrictᵛ {Γ = Γ′} u₁ (restrictᵛ {Γ = Γ′} u₂ x)) ≡ restrictᵛ {Γ = Γ} u (thinᴰ c Ψ x)
envEq {θ = θ} {Γ′ = Γ′} c {Ψ′} u u₁ u₂ x =
  trans (cong (thinᴰ c Ψ′) (trans (restrict-∘ {Γ = Γ′} u₁ u₂ x)
                                  (cong (λ w → restrictᵛ {Γ = Γ′} w x) (⊑ᵘ-unique (⊑ᵘ-trans u₁ u₂) (θ*-mono θ u)))))
        (thin-restrict c u x)

-- A binder under `keep`.
thin-bind : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {A : Ty 0} (q : Quantity) (Ψ : Usage n)
            (x : Env Γ′ (θ θ* Ψ)) (a : ⟦ A ⟧ᵛ)
          → thinᴰ (ckeep {A = A} c) (q ∷ Ψ) (bindᵛ {Γ = Γ′} {A = A} q x a) ≡ bindᵛ {Γ = Γ} {A = A} q (thinᴰ c Ψ x) a
thin-bind c Zero Ψ x a = refl
thin-bind c One  Ψ x a = refl
thin-bind c Many Ψ x a = refl

-- Binds, pointwise in the continuation.
bindC : ∀ {π} {X Y : Set} {a a′ : M π X} {f g : X → M π Y} → a ≡ a′ → (∀ v → f v ≡ g v) → bindM π a f ≡ bindM π a′ g
bindC {π} {a = a} refl h = cong (bindM π a) (extensionality h)

-- … and the graded bind (D311).
bindCᵍ : ∀ {π₁ π₂} {X Y : Set} {a a′ : M π₁ X} {f g : X → M π₂ Y} → a ≡ a′ → (∀ v → f v ≡ g v) → bindᵍ π₁ π₂ a f ≡ bindᵍ π₁ π₂ a′ g
bindCᵍ {π₁} {π₂} {a = a} refl h = cong (bindᵍ π₁ π₂ a) (extensionality h)

------------------------------------------------------------------------
-- The variable: thinning preserves lookup, at the level of environments.
------------------------------------------------------------------------

module _ {Δ : KCtx 0} (fmt : TargetNum) (δ : DefSem) where

  -- A retyped derivation means the transported meaning.
  ⟦⟧-retype : ∀ {n} {Γ : Ctx 0 n} {Ψ t A A′ π} (e : A ≡ A′) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (x : Env Γ Ψ)
            → ⟦ retype e d ⟧ fmt δ x ≡ subst (λ X → M π ⟦ X ⟧ᵛ) e (⟦ d ⟧ fmt δ x)
  ⟦⟧-retype refl d x = refl

lookup-thin : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) (i : Fin n)
                (u : singleUse (⟦ θ ⟧θ i) One ⊑ᵘ θ θ* singleUse i One) (x : Env Γ′ (θ θ* singleUse i One))
            → subst (λ X → ⟦ X ⟧ᵛ) (cthin-lookup c i) (lookupᵛUsed Γ′ (⟦ θ ⟧θ i) (restrictᵛ {Γ = Γ′} u x))
              ≡ lookupᵛUsed Γ i (thinᴰ c (singleUse i One) x)
lookup-thin (cskip c) i       (0≤q ⊑∷ u) x = lookup-thin c i u x
lookup-thin (ckeep c) zero    (1≤1 ⊑∷ u) x = refl
lookup-thin (ckeep c) (suc i) (0≤q ⊑∷ u) x = lookup-thin c i u x

------------------------------------------------------------------------
-- THE RENAMING LEMMA
------------------------------------------------------------------------

module _ {Δ : KCtx 0} (fmt : TargetNum) (δ : DefSem) where

  var-sem : ∀ {n n′} {θ : Thin n n′} {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) (i : Fin n) {j} (e : ⟦ θ ⟧θ i ≡ j)
              (x : Env Γ′ (θ θ* singleUse i One))
          → ⟦ varAt {Δ = Δ} c i e ⟧ fmt δ x ≡ lookupᵛUsed Γ i (thinᴰ c (singleUse i One) x)
  var-sem {θ = θ} {Γ′ = Γ′} c i refl x =
    trans (⟦⟧-retype fmt δ (cthin-lookup c i) (⊢var (⟦ θ ⟧θ i)) _) (lookup-thin c i _ x)

  ren-sem : ∀ {n n′} (θ : Thin n n′) (ρ : Fin n → Fin n′) (h : ∀ i → ⟦ θ ⟧θ i ≡ ρ i)
              {Γ : Ctx 0 n} {Γ′ : Ctx 0 n′} (c : CThin θ Γ Γ′) {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
              (x : Env Γ′ (θ θ* Ψ))
          → ⟦ ren-⊢ θ ρ h c d ⟧ fmt δ x ≡ ⟦ d ⟧ fmt δ (thinᴰ c Ψ x)

  ren-sem θ ρ h c (⊢var i) x = var-sem c i (h i) x

  ren-sem θ ρ h c (⊢lam {q = Zero} 0≤q d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
  ren-sem θ ρ h c (⊢lam {q = One}  0≤q d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
  ren-sem θ ρ h c (⊢lam {q = Many} 0≤q d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
  ren-sem θ ρ h c (⊢lam 1≤1 d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
  ren-sem θ ρ h c (⊢lam 1≤ω d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _
  ren-sem θ ρ h c (⊢lam ω≤ω d) x = extensionality λ _ → ren-sem (keep θ) _ _ (ckeep c) d _

  ren-sem θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} {π₁ = π₁} df dx) x =
    bindCᵍ {π₁} {π} (trans (ren-sem θ ρ h c df _) (cong (⟦ df ⟧ fmt δ) (envEq c (⊑ᵘ-+ˡ Ψ₁ (Zero *ᵘ Ψ₂)) _ _ x)))
           (λ vf → refl)
  ren-sem θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} {π₁ = π₁} {π₂ = π₂} df dx) x =
    bindCᵍ {π₁} (trans (ren-sem θ ρ h c df _) (cong (⟦ df ⟧ fmt δ) (envEq c (⊑ᵘ-+ˡ Ψ₁ (One *ᵘ Ψ₂)) _ _ x)))
           (λ vf → bindCᵍ {π₂} {π} (trans (ren-sem θ ρ h c dx _)
                                     (cong (⟦ dx ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*One Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (One *ᵘ Ψ₂))) _ _ x)))
                            (λ vx → refl))
  ren-sem θ ρ h c (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} {π₁ = π₁} {π₂ = π₂} df dx) x =
    bindCᵍ {π₁} (trans (ren-sem θ ρ h c df _) (cong (⟦ df ⟧ fmt δ) (envEq c (⊑ᵘ-+ˡ Ψ₁ (Many *ᵘ Ψ₂)) _ _ x)))
           (λ vf → bindCᵍ {π₂} {π} (trans (ren-sem θ ρ h c dx _)
                                     (cong (⟦ dx ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₂) (⊑ᵘ-+ʳ Ψ₁ (Many *ᵘ Ψ₂))) _ _ x)))
                            (λ vx → refl))

  ren-sem θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} d₁ d₂) x =
    trans (ren-sem (keep θ) _ _ (ckeep c) d₂ _) (cong (⟦ d₂ ⟧ fmt δ) (envEq c (⊑ᵘ-+ˡ Ψ₂ (Zero *ᵘ Ψ₁)) _ _ x))
  ren-sem θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π₁ = π₁} {π₂ = π₂} d₁ d₂) x =
    bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c d₁ _)
                           (cong (⟦ d₁ ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*One Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (One *ᵘ Ψ₁))) _ _ x)))
           (λ v → trans (ren-sem (keep θ) _ _ (ckeep c) d₂ _)
                        (cong (λ z → ⟦ d₂ ⟧ fmt δ (z , v)) (envEq c (⊑ᵘ-+ˡ Ψ₂ (One *ᵘ Ψ₁)) _ _ x)))
  ren-sem θ ρ h c (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π₁ = π₁} {π₂ = π₂} d₁ d₂) x =
    bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c d₁ _)
                           (cong (⟦ d₁ ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*Many Ψ₁) (⊑ᵘ-+ʳ Ψ₂ (Many *ᵘ Ψ₁))) _ _ x)))
           (λ v → trans (ren-sem (keep θ) _ _ (ckeep c) d₂ _)
                        (cong (λ z → ⟦ d₂ ⟧ fmt δ (z , v)) (envEq c (⊑ᵘ-+ˡ Ψ₂ (Many *ᵘ Ψ₁)) _ _ x)))

  ren-sem θ ρ h c ⊢unit x = refl

  ren-sem θ ρ h c (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π₁ = π₁} {π₂ = π₂} da db) x =
    bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c da _) (cong (⟦ da ⟧ fmt δ) (envEq c (⊑ᵘ-+ˡ Ψ₁ Ψ₂) _ _ x)))
           (λ a → cong (fmapM π₂ _) (trans (ren-sem θ ρ h c db _) (cong (⟦ db ⟧ fmt δ) (envEq c (⊑ᵘ-+ʳ Ψ₁ Ψ₂) _ _ x))))
  ren-sem θ ρ h c (⊢fst {π = π} d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c (⊢snd {π = π} d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c (⊢inl {π = π} d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c (⊢inr {π = π} d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c (⊢case {Ψs = Ψs} {Ψ = Ψ} {qℓ = qℓ} {qr = qr} {π₁ = π₁} {π₂ = π₂} ds dl dr) x =
    bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c ds _) (cong (⟦ ds ⟧ fmt δ) (envEq c (⊑ᵘ-+ˡ Ψs Ψ) _ _ x)))
           (λ { (inj₁ a) → trans (ren-sem (keep θ) _ _ (ckeep c) dl _)
                           (trans (cong (⟦ dl ⟧ fmt δ) (thin-bind c qℓ Ψ _ a))
                                  (cong (λ z → ⟦ dl ⟧ fmt δ (bindᵛ qℓ z a)) (envEq c (⊑ᵘ-+ʳ Ψs Ψ) _ _ x)))
              ; (inj₂ b) → trans (ren-sem (keep θ) _ _ (ckeep c) dr _)
                           (trans (cong (⟦ dr ⟧ fmt δ) (thin-bind c qr Ψ _ b))
                                  (cong (λ z → ⟦ dr ⟧ fmt δ (bindᵛ qr z b)) (envEq c (⊑ᵘ-+ʳ Ψs Ψ) _ _ x))) })
  ren-sem θ ρ h c (⊢absurd {π = π} d) x = bindC {π} (ren-sem θ ρ h c d x) (λ _ → refl)
  ren-sem θ ρ h c (⊢roll {π = π} wf d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c (⊢fold {Ψa = Ψa} {Ψt = Ψt} {π = π} {π₁ = π₁} {π₂ = π₂} wf da dt) x =
    bindCᵍ {π₁} (trans (ren-sem θ ρ h c da _)
                       (cong (⟦ da ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*Many Ψa) (⊑ᵘ-+ˡ (Many *ᵘ Ψa) Ψt)) _ _ x)))
           (λ valg → bindCᵍ {π₂} {π} (trans (ren-sem θ ρ h c dt _)
                                       (cong (⟦ dt ⟧ fmt δ) (envEq c (⊑ᵘ-+ʳ (Many *ᵘ Ψa) Ψt) _ _ x)))
                              (λ _ → refl))
  ren-sem θ ρ h c (⊢unfold {Ψc = Ψc} {Ψs = Ψs} {π₁ = π₁} {π₂ = π₂} wf dc ds) x =
    bindCᵍ {π₁} {π₂} (trans (ren-sem θ ρ h c dc _)
                            (cong (⟦ dc ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*Many Ψc) (⊑ᵘ-+ˡ (Many *ᵘ Ψc) Ψs)) _ _ x)))
           (λ clo → cong (fmapM π₂ _) (trans (ren-sem θ ρ h c ds _)
                                             (cong (⟦ ds ⟧ fmt δ) (envEq c (⊑ᵘ-+ʳ (Many *ᵘ Ψc) Ψs) _ _ x))))
  ren-sem θ ρ h c (⊢iter {Ψf = Ψf} {Ψs = Ψs} {π₁ = π₁} {π₂ = π₂} df ds) x =
    bindCᵍ {π₁} (trans (ren-sem θ ρ h c df _)
                       (cong (⟦ df ⟧ fmt δ) (envEq c (⊑ᵘ-trans (⊑ᵘ-*Many Ψf) (⊑ᵘ-+ˡ (Many *ᵘ Ψf) Ψs)) _ _ x)))
           (λ f → bindCᵍ {π₂} {eff} (trans (ren-sem θ ρ h c ds _)
                                      (cong (⟦ ds ⟧ fmt δ) (envEq c (⊑ᵘ-+ʳ (Many *ᵘ Ψf) Ψs) _ _ x)))
                           (λ _ → refl))
  ren-sem θ ρ h c (⊢out {f = φ} {π₁ = π₁} wf d) x = bindCᵍ {π₁} {fin φ} (ren-sem θ ρ h c d x) (λ _ → refl)
  ren-sem θ ρ h c (⊢coerce {π = π} p d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c ⊢lit-int x = refl
  ren-sem θ ρ h c ⊢lit-float x = refl
  ren-sem θ ρ h c (⊢prim {π = π} p d) x = cong (fmapM π _) (ren-sem θ ρ h c d x)
  ren-sem θ ρ h c (⊢sigop m) x = refl
  ren-sem θ ρ h c (⊢ref d τ r) x = refl
  ren-sem θ ρ h c (⊢sub-eff g d) x = cong (Once.Internal.Graded.subM g) (ren-sem θ ρ h c d x)
  -- D276: sub-usaging is a restriction, and restriction commutes with thinning.
  ren-sem θ ρ h c (⊢sub-use p d) x = trans (ren-sem θ ρ h c d _) (cong (⟦ d ⟧ fmt δ) (thin-restrict c p x))

------------------------------------------------------------------------
-- Weakening by one unused variable (what the derived combinators use).
------------------------------------------------------------------------

-- The identity thinning, after a restriction onto its usage, is the identity.
thin-id : ∀ {n} (Γ : Ctx 0 n) (Ψ : Usage n) (v : idθ n θ* Ψ ⊑ᵘ Ψ) (x : Env Γ Ψ)
        → thinᴰ (cid Γ) Ψ (restrictᵛ {Γ = Γ} v x) ≡ x
thin-id ∅       []         []          x = refl
thin-id (Γ ▸ A) (Zero ∷ Ψ) (0≤q ⊑∷ v) x = thin-id Γ Ψ v x
thin-id (Γ ▸ A) (One  ∷ Ψ) (1≤1 ⊑∷ v) x = cong (_, proj₂ x) (thin-id Γ Ψ v (proj₁ x))
thin-id (Γ ▸ A) (Many ∷ Ψ) (ω≤ω ⊑∷ v) x = cong (_, proj₂ x) (thin-id Γ Ψ v (proj₁ x))

module _ {Δ : KCtx 0} (fmt : TargetNum) (δ : DefSem) where

  private
    wk-help : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Ty 0} {t π} (B : Ty 0) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
                (w : Zero ∷ (idθ n θ* Ψ) ⊑ᵘ Zero ∷ Ψ) (x : Env Γ Ψ)
            → ⟦ ⊢sub-use {Γ = Γ ▸ B} w (ren-⊢ (skip (idθ n)) suc (λ i → cong suc (idθ-id i)) (cskip (cid Γ)) d) ⟧ fmt δ x
              ≡ ⟦ d ⟧ fmt δ x
    wk-help {Γ = Γ} {Ψ} B d (0≤q ⊑∷ v) x =
      trans (ren-sem fmt δ _ _ _ (cskip (cid Γ)) d _) (cong (⟦ d ⟧ fmt δ) (thin-id Γ Ψ v x))

  -- THE WEAKENING LEMMA: a term weakened by one unused variable means what it meant.
  wk-sem : ∀ {n} {Γ : Ctx 0 n} {Ψ : Usage n} {A : Ty 0} {t π} (B : Ty 0) (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) (x : Env Γ Ψ)
         → ⟦ wk-⊢ {B = B} d ⟧ fmt δ x ≡ ⟦ d ⟧ fmt δ x
  wk-sem {Ψ = Ψ} B d x = wk-help B d (⊑ᵘ-≡ (cong (Zero ∷_) (θ*-id Ψ))) x
