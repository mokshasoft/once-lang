-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoreSubstSem — plan 0.102 phase B (D276): ⟦_⟧ PRESERVES
-- COMPOSITION.
--
--   ⟦ sub-⊢ d h ⟧ fmt δ x ≡ ⟦ d ⟧ fmt δ (rowsᴰ h Ψ x)
--
-- A typed substitution of PURE rows (`SubTy`) induces an environment map
-- `rowsᴰ`: each live slot of the source environment is its row's value, the
-- row evaluated on the target environment restricted to what it uses. The
-- induction needs three facts about `rowsᴰ`, all from ONE lookup lemma
-- (`lookup-rowsᴰ`) through ENVIRONMENT EXTENSIONALITY (`env-ext`: a runtime
-- environment is the tuple of its live lookups):
--   * naturality under restriction (`rows-nat`) — the sub-usaging rule and
--     every multi-premise rule's split of the environment;
--   * the binder (`rows-ext`, `rows-ext0`) — `extS`;
--   * (in `Once.Adequacy.TermModel`) single substitution's environment.
-- Every transport of an environment is itself a restriction (`subst-restr`),
-- and the usage order is proof-irrelevant, so all restriction chains with the
-- same ends agree (`EnvAlgebraV.restrict-≡`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)

module Once.Adequacy.CoreSubstSem {Fs : ISig} {s : ℕ} (S : Sig Fs s) where

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _,ₚ_)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Once.Postulates using (extensionality)
open import Once.Type using (Type; Quantity; Zero; One; Many; Purity; pure)
open import Once.Target.Arch using (TargetNum)
open import Once.Surface.Context
  using (Ctx; ∅; _,_^_; _,_; lookup; Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_;
         _⊑ᵘ_; ⊑[]; _⊑∷_; _≤q'_; z≤z; z≤o; z≤m; o≤o; o≤m; m≤m;
         ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-trans; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Surface.GradeMatrix using (Grades; _⋆_; ⋆-mono; extΦ; ⋆-ext)
open import Once.Denotation.GradedDomain using (⟦_⟧ᵛ)
open import Once.Denotation.PhaseV using (restrictᵛ; bindᵛ; bindᵛ0; lookupᵛUsed)
open import Once.Denotation.EnvAlgebraV using (Env; restrict-irr; restrict-refl; restrict-∘; restrict-≡; restrict-bind)
open import Once.Spec.Core.Syntax S
open import Once.Spec.Core.Typing S
open import Once.Spec.Core.Subst S using (SubTy; rows; row; tailᴿ; ext-ty; retype)
import Once.Spec.Core.Meaning S as GM
open import Once.Adequacy.CoreRenameSem S using (wk-sem; bindC)
open import Once.Denotation.GradedDomain using (M; bindM; subM)
open import Once.Denotation.GradedOps using (fmapM; ana-semᵛ)
open import Once.Spec.Core.Subst S using (sub-⊢)
open import Once.Surface.GradeMatrix using (⋆-zero; ⋆-+; ⋆-*; ⋆-single)

------------------------------------------------------------------------
-- Live slots and environment extensionality
------------------------------------------------------------------------

-- `i` is live in `Ψ`: the runtime environment has a slot for it.
data Live : ∀ {n} → Usage n → Fin n → Set where
  l-one  : ∀ {n} {Ψ : Usage n} → Live (One ∷ Ψ) zero
  l-many : ∀ {n} {Ψ : Usage n} → Live (Many ∷ Ψ) zero
  l-suc  : ∀ {n} {q : Quantity} {Ψ : Usage n} {i : Fin n} → Live Ψ i → Live (q ∷ Ψ) (suc i)

z≤ : ∀ (q : Quantity) → Zero ≤q' q
z≤ Zero = z≤z
z≤ One  = z≤o
z≤ Many = z≤m

zero⊑ : ∀ {n} (Ψ : Usage n) → zeroUsage ⊑ᵘ Ψ
zero⊑ []      = ⊑[]
zero⊑ (q ∷ Ψ) = z≤ q ⊑∷ zero⊑ Ψ

single-⊑ : ∀ {n} {Ψ : Usage n} {i} → Live Ψ i → singleUse i One ⊑ᵘ Ψ
single-⊑ (l-one {Ψ = Ψ})  = o≤o ⊑∷ zero⊑ Ψ
single-⊑ (l-many {Ψ = Ψ}) = o≤m ⊑∷ zero⊑ Ψ
single-⊑ (l-suc {q = q} l) = z≤ q ⊑∷ single-⊑ l

-- A live slot's value.
look : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} {i} → Live Ψ i → Env Γ Ψ → ⟦ lookup Γ i ⟧ᵛ
look {Γ = Γ} {i = i} l ρ = lookupᵛUsed Γ i (restrictᵛ {Γ = Γ} (single-⊑ l) ρ)

env-ext : ∀ {n} {Γ : Ctx n} {Ψ : Usage n} (ρ ρ′ : Env Γ Ψ)
        → (∀ {i} (l : Live Ψ i) → look {Γ = Γ} l ρ ≡ look {Γ = Γ} l ρ′) → ρ ≡ ρ′
env-ext {Γ = ∅}         {[]}       ρ ρ′ h = refl
env-ext {Γ = Γ , A ^ r} {Zero ∷ Ψ} ρ ρ′ h = env-ext {Γ = Γ} ρ ρ′ (λ l → h (l-suc l))
env-ext {Γ = Γ , A ^ r} {One ∷ Ψ}  (ρ ,ₚ a) (ρ′ ,ₚ a′) h = cong₂ _,ₚ_ (env-ext {Γ = Γ} ρ ρ′ (λ l → h (l-suc l))) (h l-one)
env-ext {Γ = Γ , A ^ r} {Many ∷ Ψ} (ρ ,ₚ a) (ρ′ ,ₚ a′) h = cong₂ _,ₚ_ (env-ext {Γ = Γ} ρ ρ′ (λ l → h (l-suc l))) (h l-many)

private
  lm : ∀ {n} {Ψ Ψ′ : Usage n} {i} → Live Ψ i → Ψ ⊑ᵘ Ψ′ → Live Ψ′ i
  lm l-one     (o≤o ⊑∷ p) = l-one
  lm l-one     (o≤m ⊑∷ p) = l-many
  lm l-many    (m≤m ⊑∷ p) = l-many
  lm (l-suc l) (_ ⊑∷ p)   = l-suc (lm l p)

live-mono : ∀ {n} {Ψ Ψ′ : Usage n} {i} → Ψ ⊑ᵘ Ψ′ → Live Ψ i → Live Ψ′ i
live-mono p l = lm l p

look-restr : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {i} (p : Ψ ⊑ᵘ Ψ′) (l : Live Ψ i) (ρ : Env Γ Ψ′)
           → look {Γ = Γ} l (restrictᵛ {Γ = Γ} p ρ) ≡ look {Γ = Γ} (live-mono p l) ρ
look-restr {Γ = Γ} {i = i} p l ρ =
  cong (lookupᵛUsed Γ i) (restrict-≡ {Γ = Γ} (single-⊑ l) p (single-⊑ (live-mono p l)) ρ)

-- A binder's slot is dropped by `l-suc`, whatever the binder's grade.
look-bind : ∀ {n} {Γ : Ctx n} {A : Type} {Ψ : Usage n} {i} (q : Quantity) (l : Live Ψ i) (ρ : Env Γ Ψ) (a : ⟦ A ⟧ᵛ)
          → look {Γ = Γ , A ^ Many} (l-suc {q = q} l) (bindᵛ {Γ = Γ} {A = A} q ρ a) ≡ look {Γ = Γ} l ρ
look-bind Zero l ρ a = refl
look-bind One  l ρ a = refl
look-bind Many l ρ a = refl

------------------------------------------------------------------------
-- Transports are restrictions
------------------------------------------------------------------------

≡⊑ : ∀ {n} {U V : Usage n} → U ≡ V → V ⊑ᵘ U
≡⊑ {U = U} refl = ⊑ᵘ-refl′ U
  where
    ⊑ᵘ-refl′ : ∀ {n} (Ψ : Usage n) → Ψ ⊑ᵘ Ψ
    ⊑ᵘ-refl′ []         = ⊑[]
    ⊑ᵘ-refl′ (Zero ∷ Ψ) = z≤z ⊑∷ ⊑ᵘ-refl′ Ψ
    ⊑ᵘ-refl′ (One ∷ Ψ)  = o≤o ⊑∷ ⊑ᵘ-refl′ Ψ
    ⊑ᵘ-refl′ (Many ∷ Ψ) = m≤m ⊑∷ ⊑ᵘ-refl′ Ψ

subst-restr : ∀ {n} {Δ : Ctx n} {U V : Usage n} (e : U ≡ V) (x : Env Δ U)
            → subst (Env Δ) e x ≡ restrictᵛ {Γ = Δ} (≡⊑ e) x
subst-restr {Δ = Δ} refl x = sym (restrict-refl {Γ = Δ} _ x)

-- The meaning of a usage transport.
⟦retype⟧ : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {t A π} (e : Ψ ≡ Ψ′) (d : Γ ⊢[ Ψ ] t ∷ A ! π)
             (fmt : TargetNum) (δ : GM.DefSem) (x : Env Γ Ψ′)
         → GM.⟦ retype e d ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (subst (Env Γ) (sym e) x)
⟦retype⟧ refl d fmt δ x = refl

------------------------------------------------------------------------
-- The environment a typed substitution induces
------------------------------------------------------------------------

module Rows (fmt : TargetNum) (δ : GM.DefSem) where

  rowsᴰ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m}
        → SubTy Δ σ Γ Φ → (Ψ : Usage n) → Env Δ (Ψ ⋆ Φ) → Env Γ Ψ
  rowsᴰ {Γ = ∅}         h []         x = tt
  rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h (Zero ∷ Ψ) x =
    rowsᴰ (tailᴿ h) Ψ (restrictᵛ {Γ = Δ} (⊑ᵘ-+ʳ (Zero *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i)))) x)
  rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h (One ∷ Ψ) x =
    rowsᴰ (tailᴿ h) Ψ (restrictᵛ {Γ = Δ} (⊑ᵘ-+ʳ (One *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i)))) x)
    ,ₚ GM.⟦ row h zero ⟧ fmt δ (restrictᵛ {Γ = Δ} (⊑ᵘ-trans (⊑ᵘ-*One (Φ zero)) (⊑ᵘ-+ˡ (One *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i))))) x)
  rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h (Many ∷ Ψ) x =
    rowsᴰ (tailᴿ h) Ψ (restrictᵛ {Γ = Δ} (⊑ᵘ-+ʳ (Many *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i)))) x)
    ,ₚ GM.⟦ row h zero ⟧ fmt δ (restrictᵛ {Γ = Δ} (⊑ᵘ-trans (⊑ᵘ-*Many (Φ zero)) (⊑ᵘ-+ˡ (Many *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i))))) x)

  -- What a live row reads.
  row-⊑ : ∀ {n m} {Ψ : Usage n} {i} (Φ : Grades n m) → Live Ψ i → Φ i ⊑ᵘ (Ψ ⋆ Φ)
  row-⊑ Φ (l-one {Ψ = Ψ})  = ⊑ᵘ-trans (⊑ᵘ-*One (Φ zero)) (⊑ᵘ-+ˡ (One *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i))))
  row-⊑ Φ (l-many {Ψ = Ψ}) = ⊑ᵘ-trans (⊑ᵘ-*Many (Φ zero)) (⊑ᵘ-+ˡ (Many *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i))))
  row-⊑ Φ (l-suc {q = q} {Ψ = Ψ} l) = ⊑ᵘ-trans (row-⊑ (λ i → Φ (suc i)) l) (⊑ᵘ-+ʳ (q *ᵘ Φ zero) (Ψ ⋆ (λ i → Φ (suc i))))

  -- THE LOOKUP LEMMA: a live slot of `rowsᴰ` is its row, evaluated.
  lookup-rowsᴰ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
                   {Ψ : Usage n} {i} (l : Live Ψ i) (x : Env Δ (Ψ ⋆ Φ))
               → look {Γ = Γ} l (rowsᴰ h Ψ x) ≡ GM.⟦ row h i ⟧ fmt δ (restrictᵛ {Γ = Δ} (row-⊑ Φ l) x)
  lookup-rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h {One ∷ Ψ} l-one x =
    cong (λ z → GM.⟦ row h zero ⟧ fmt δ z) refl
  lookup-rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h {Many ∷ Ψ} l-many x = refl
  lookup-rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h {Zero ∷ Ψ} {suc i} (l-suc l) x =
    trans (lookup-rowsᴰ (tailᴿ h) l _)
          (cong (GM.⟦ row h (suc i) ⟧ fmt δ) (restrict-∘ {Γ = Δ} (row-⊑ (λ j → Φ (suc j)) l) _ x))
  lookup-rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h {One ∷ Ψ} {suc i} (l-suc l) x =
    trans (lookup-rowsᴰ (tailᴿ h) l _)
          (cong (GM.⟦ row h (suc i) ⟧ fmt δ) (restrict-∘ {Γ = Δ} (row-⊑ (λ j → Φ (suc j)) l) _ x))
  lookup-rowsᴰ {Γ = Γ , A ^ r} {Δ = Δ} {σ = σ} {Φ = Φ} h {Many ∷ Ψ} {suc i} (l-suc l) x =
    trans (lookup-rowsᴰ (tailᴿ h) l _)
          (cong (GM.⟦ row h (suc i) ⟧ fmt δ) (restrict-∘ {Γ = Δ} (row-⊑ (λ j → Φ (suc j)) l) _ x))

  -- NATURALITY: restricting the induced environment = inducing from the
  -- restricted one.
  rows-nat : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
               {Ψ Ψ′ : Usage n} (p : Ψ ⊑ᵘ Ψ′) (x : Env Δ (Ψ′ ⋆ Φ))
           → restrictᵛ {Γ = Γ} p (rowsᴰ h Ψ′ x) ≡ rowsᴰ h Ψ (restrictᵛ {Γ = Δ} (⋆-mono Φ p) x)
  rows-nat {Γ = Γ} {Δ = Δ} {Φ = Φ} h p x =
    env-ext {Γ = Γ} _ _ λ {i} l →
      trans (look-restr {Γ = Γ} p l (rowsᴰ h _ x))
        (trans (lookup-rowsᴰ h (live-mono p l) x)
          (trans (cong (GM.⟦ row h i ⟧ fmt δ) (sym (restrict-≡ {Γ = Δ} (row-⊑ Φ l) (⋆-mono Φ p) (row-⊑ Φ (live-mono p l)) x)))
                 (sym (lookup-rowsᴰ h l _))))

  -- Any two ways to reach a smaller induced environment agree: a restriction
  -- of a transport of `x` is a restriction of `x`.
  rows-via : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
               {Ψ₁ Ψ : Usage n} {U : Usage m} (p : Ψ₁ ⊑ᵘ Ψ) (e : Ψ ⋆ Φ ≡ U) (w : Ψ₁ ⋆ Φ ⊑ᵘ U) (x : Env Δ (Ψ ⋆ Φ))
           → rowsᴰ h Ψ₁ (restrictᵛ {Γ = Δ} w (subst (Env Δ) e x)) ≡ restrictᵛ {Γ = Γ} p (rowsᴰ h Ψ x)
  rows-via {Δ = Δ} {Φ = Φ} h p e w x =
    trans (cong (rowsᴰ h _) (trans (cong (restrictᵛ {Γ = Δ} w) (subst-restr {Δ = Δ} e x))
                                   (restrict-≡ {Γ = Δ} w (≡⊑ e) (⋆-mono Φ p) x)))
          (sym (rows-nat h p x))

  -- THE BINDER: under `extS`, the bound slot is itself and the rest is `rowsᴰ`.
  extᴰ : ∀ {n m} {Δ : Ctx m} (Φ : Grades n m) (A : Type) (q : Quantity) (Ψ : Usage n)
       → Env Δ (Ψ ⋆ Φ) → ⟦ A ⟧ᵛ → Env (Δ , A) ((q ∷ Ψ) ⋆ extΦ Φ)
  extᴰ {Δ = Δ} Φ A q Ψ x a = subst (Env (Δ , A)) (sym (⋆-ext q Ψ Φ)) (bindᵛ {Γ = Δ} {A = A} q x a)

  -- `extᴰ` restricted anywhere is the bind restricted there.
  extᴰ-via : ∀ {n m} {Δ : Ctx m} (Φ : Grades n m) (A : Type) (q : Quantity) (Ψ : Usage n)
               (x : Env Δ (Ψ ⋆ Φ)) (a : ⟦ A ⟧ᵛ) {V : Usage (suc m)}
               (u : V ⊑ᵘ ((q ∷ Ψ) ⋆ extΦ Φ)) (w : V ⊑ᵘ (q ∷ (Ψ ⋆ Φ)))
           → restrictᵛ {Γ = Δ , A} u (extᴰ {Δ = Δ} Φ A q Ψ x a) ≡ restrictᵛ {Γ = Δ , A} w (bindᵛ {Γ = Δ} {A = A} q x a)
  extᴰ-via {Δ = Δ} Φ A q Ψ x a u w =
    trans (cong (restrictᵛ {Γ = Δ , A} u) (subst-restr {Δ = Δ , A} (sym (⋆-ext q Ψ Φ)) (bindᵛ {Γ = Δ} {A = A} q x a)))
          (restrict-≡ {Γ = Δ , A} u (≡⊑ (sym (⋆-ext q Ψ Φ))) w (bindᵛ {Γ = Δ} {A = A} q x a))

  rows-ext-slot : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
                    (A : Type) (q : Quantity) (Ψ : Usage n) (x : Env Δ (Ψ ⋆ Φ)) (a : ⟦ A ⟧ᵛ) {i} (l : Live (q ∷ Ψ) i)
                → look {Γ = Γ , A} l (rowsᴰ (ext-ty A h) (q ∷ Ψ) (extᴰ {Δ = Δ} Φ A q Ψ x a))
                  ≡ look {Γ = Γ , A} l (bindᵛ {Γ = Γ} {A = A} q (rowsᴰ h Ψ x) a)
  rows-ext-slot {Γ = Γ} {Δ = Δ} {Φ = Φ} h A .One Ψ x a l-one =
    trans (lookup-rowsᴰ {Γ = Γ , A} {Δ = Δ , A} (ext-ty A h) {Ψ = One ∷ Ψ} l-one (extᴰ {Δ = Δ} Φ A One Ψ x a))
          (cong (lookupᵛUsed (Δ , A) zero) (extᴰ-via {Δ = Δ} Φ A One Ψ x a (row-⊑ {Ψ = One ∷ Ψ} (extΦ Φ) l-one) (o≤o ⊑∷ zero⊑ (Ψ ⋆ Φ))))
  rows-ext-slot {Γ = Γ} {Δ = Δ} {Φ = Φ} h A .Many Ψ x a l-many =
    trans (lookup-rowsᴰ {Γ = Γ , A} {Δ = Δ , A} (ext-ty A h) {Ψ = Many ∷ Ψ} l-many (extᴰ {Δ = Δ} Φ A Many Ψ x a))
          (cong (lookupᵛUsed (Δ , A) zero) (extᴰ-via {Δ = Δ} Φ A Many Ψ x a (row-⊑ {Ψ = Many ∷ Ψ} (extΦ Φ) l-many) (o≤m ⊑∷ zero⊑ (Ψ ⋆ Φ))))
  rows-ext-slot {Γ = Γ} {Δ = Δ} {Φ = Φ} h A q Ψ x a (l-suc {i = i} l) =
    trans (lookup-rowsᴰ {Γ = Γ , A} {Δ = Δ , A} (ext-ty A h) {Ψ = q ∷ Ψ} (l-suc l) (extᴰ {Δ = Δ} Φ A q Ψ x a))
      (trans (wk-sem A (row h i) fmt δ _)
        (trans (cong (GM.⟦ row h i ⟧ fmt δ)
                     (trans (extᴰ-via {Δ = Δ} Φ A q Ψ x a (row-⊑ {Ψ = q ∷ Ψ} (extΦ Φ) (l-suc l)) (z≤ q ⊑∷ row-⊑ Φ l))
                            (restrict-bind {Γ = Δ} {A = A} Zero q (z≤ q ⊑∷ row-⊑ Φ l) (row-⊑ Φ l) x a)))
          (trans (sym (lookup-rowsᴰ {Γ = Γ} {Δ = Δ} h l x)) (sym (look-bind {Γ = Γ} {A = A} q l (rowsᴰ h Ψ x) a)))))

  rows-ext : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
               (A : Type) (q : Quantity) (Ψ : Usage n) (x : Env Δ (Ψ ⋆ Φ)) (a : ⟦ A ⟧ᵛ)
           → rowsᴰ (ext-ty A h) (q ∷ Ψ) (extᴰ {Δ = Δ} Φ A q Ψ x a) ≡ bindᵛ {Γ = Γ} {A = A} q (rowsᴰ h Ψ x) a
  rows-ext {Γ = Γ} {Δ = Δ} {Φ = Φ} h A q Ψ x a =
    env-ext {Γ = Γ , A} {Ψ = q ∷ Ψ} (rowsᴰ (ext-ty A h) (q ∷ Ψ) (extᴰ {Δ = Δ} Φ A q Ψ x a)) (bindᵛ {Γ = Γ} {A = A} q (rowsᴰ h Ψ x) a)
      (rows-ext-slot {Γ = Γ} {Δ = Δ} h A q Ψ x a)

  -- …and at an ERASED binder (no value to bind).
  extᴰ0 : ∀ {n m} {Δ : Ctx m} (Φ : Grades n m) (A : Type) (Ψ : Usage n)
        → Env Δ (Ψ ⋆ Φ) → Env (Δ , A) ((Zero ∷ Ψ) ⋆ extΦ Φ)
  extᴰ0 {Δ = Δ} Φ A Ψ x = subst (Env (Δ , A)) (sym (⋆-ext Zero Ψ Φ)) (bindᵛ0 {Γ = Δ} {A = A} x)

  rows-ext0-slot : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
                     (A : Type) (Ψ : Usage n) (x : Env Δ (Ψ ⋆ Φ)) {i} (l : Live (Zero ∷ Ψ) i)
                 → look {Γ = Γ , A} l (rowsᴰ (ext-ty A h) (Zero ∷ Ψ) (extᴰ0 {Δ = Δ} Φ A Ψ x))
                   ≡ look {Γ = Γ , A} l (bindᵛ0 {Γ = Γ} {A = A} (rowsᴰ h Ψ x))
  rows-ext0-slot {Γ = Γ} {Δ = Δ} {Φ = Φ} h A Ψ x (l-suc {i = i} l) =
    trans (lookup-rowsᴰ {Γ = Γ , A} {Δ = Δ , A} (ext-ty A h) {Ψ = Zero ∷ Ψ} (l-suc l) (extᴰ0 {Δ = Δ} Φ A Ψ x))
      (trans (wk-sem A (row h i) fmt δ _)
        (trans (cong (GM.⟦ row h i ⟧ fmt δ)
                     (trans (cong (restrictᵛ {Γ = Δ , A} u) (subst-restr {Δ = Δ , A} (sym (⋆-ext Zero Ψ Φ)) (bindᵛ0 {Γ = Δ} {A = A} x)))
                            (restrict-≡ {Γ = Δ , A} u (≡⊑ (sym (⋆-ext Zero Ψ Φ))) (z≤z ⊑∷ row-⊑ Φ l) (bindᵛ0 {Γ = Δ} {A = A} x))))
               (sym (lookup-rowsᴰ {Γ = Γ} {Δ = Δ} h l x))))
    where u = row-⊑ {Ψ = Zero ∷ Ψ} (extΦ Φ) (l-suc l)

  rows-ext0 : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {σ : Sub n m} {Φ : Grades n m} (h : SubTy Δ σ Γ Φ)
                (A : Type) (Ψ : Usage n) (x : Env Δ (Ψ ⋆ Φ))
            → rowsᴰ (ext-ty A h) (Zero ∷ Ψ) (extᴰ0 {Δ = Δ} Φ A Ψ x) ≡ bindᵛ0 {Γ = Γ} {A = A} (rowsᴰ h Ψ x)
  rows-ext0 {Γ = Γ} {Δ = Δ} {Φ = Φ} h A Ψ x =
    env-ext {Γ = Γ , A} {Ψ = Zero ∷ Ψ} (rowsᴰ (ext-ty A h) (Zero ∷ Ψ) (extᴰ0 {Δ = Δ} Φ A Ψ x)) (bindᵛ0 {Γ = Γ} {A = A} (rowsᴰ h Ψ x))
      (rows-ext0-slot {Γ = Γ} {Δ = Δ} h A Ψ x)

  live-single : ∀ {n} (i : Fin n) → Live (singleUse i One) i
  live-single zero    = l-one
  live-single (suc i) = l-suc (live-single i)

  ------------------------------------------------------------------------
  -- THE SEMANTIC SUBSTITUTION LEMMA
  ------------------------------------------------------------------------

  mutual
    sub-sem : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ : Usage n} {t A π} {σ : Sub n m} {Φ : Grades n m}
                (d : Γ ⊢[ Ψ ] t ∷ A ! π) (h : SubTy Δ σ Γ Φ) (x : Env Δ (Ψ ⋆ Φ))
            → GM.⟦ sub-⊢ d h ⟧ fmt δ x ≡ GM.⟦ d ⟧ fmt δ (rowsᴰ h Ψ x)

    sub-sem {Γ = Γ} {Δ = Δ} {Φ = Φ} (⊢var i) h x =
      trans (⟦retype⟧ (sym (⋆-single i Φ)) (row h i) fmt δ x)
        (trans (cong (GM.⟦ row h i ⟧ fmt δ)
                     (trans (subst-restr {Δ = Δ} (sym (sym (⋆-single i Φ))) x)
                            (restrict-irr {Γ = Δ} _ (row-⊑ Φ (live-single i)) x)))
          (trans (sym (lookup-rowsᴰ h (live-single i) x))
                 (cong (lookupᵛUsed Γ i) (restrict-refl {Γ = Γ} (single-⊑ (live-single i)) _))))

    sub-sem (⊢lam {q = Zero} {q' = Zero} {A = A} le d) h x = extensionality λ _ → ihb0′ A d h x
    sub-sem (⊢lam {q = Zero} {q' = One}  () d) h x
    sub-sem (⊢lam {q = Zero} {q' = Many} () d) h x
    sub-sem (⊢lam {q = One}  {q' = Zero} {A = A} le d) h x = extensionality λ _ → ihb0′ A d h x
    sub-sem (⊢lam {q = One}  {q' = One}  {A = A} le d) h x = extensionality λ a → ihb′ A One d h x a
    sub-sem (⊢lam {q = One}  {q' = Many} () d) h x
    sub-sem (⊢lam {q = Many} {q' = Zero} {A = A} le d) h x = extensionality λ _ → ihb0′ A d h x
    sub-sem (⊢lam {q = Many} {q' = One}  {A = A} le d) h x = extensionality λ a → ihb′ A One d h x a
    sub-sem (⊢lam {q = Many} {q' = Many} {A = A} le d) h x = extensionality λ a → ihb′ A Many d h x a

    sub-sem {Φ = Φ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {π = π} df dx) h x =
      trans (⟦retype⟧ (sym E) _ fmt δ x) (bindC {π} (ih df h _ (sym (sym E)) _ x) (λ _ → refl))
      where E = trans (⋆-+ Ψ₁ (Zero *ᵘ Ψ₂) Φ) (cong ((Ψ₁ ⋆ Φ) +ᵘ_) (⋆-* Zero Ψ₂ Φ))
    sub-sem {Φ = Φ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} df dx) h x =
      trans (⟦retype⟧ (sym E) _ fmt δ x)
            (bindC {π} (ih df h _ (sym (sym E)) _ x) (λ vf → bindC {π} (ih dx h _ (sym (sym E)) _ x) (λ _ → refl)))
      where E = trans (⋆-+ Ψ₁ (One *ᵘ Ψ₂) Φ) (cong ((Ψ₁ ⋆ Φ) +ᵘ_) (⋆-* One Ψ₂ Φ))
    sub-sem {Φ = Φ} (⊢app {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} df dx) h x =
      trans (⟦retype⟧ (sym E) _ fmt δ x)
            (bindC {π} (ih df h _ (sym (sym E)) _ x) (λ vf → bindC {π} (ih dx h _ (sym (sym E)) _ x) (λ _ → refl)))
      where E = trans (⋆-+ Ψ₁ (Many *ᵘ Ψ₂) Φ) (cong ((Ψ₁ ⋆ Φ) +ᵘ_) (⋆-* Many Ψ₂ Φ))

    sub-sem {Φ = Φ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Zero} {A = A} de db) h x =
      trans (⟦retype⟧ (sym E) _ fmt δ x) (ihb0 A db h _ (sym (sym E)) _ x)
      where E = trans (⋆-+ Ψ₂ (Zero *ᵘ Ψ₁) Φ) (cong ((Ψ₂ ⋆ Φ) +ᵘ_) (⋆-* Zero Ψ₁ Φ))
    sub-sem {Φ = Φ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = One} {π = π} {A = A} de db) h x =
      trans (⟦retype⟧ (sym E) _ fmt δ x)
            (bindC {π} (ih de h _ (sym (sym E)) _ x) (λ v → ihb A One db h _ (sym (sym E)) _ x v))
      where E = trans (⋆-+ Ψ₂ (One *ᵘ Ψ₁) Φ) (cong ((Ψ₂ ⋆ Φ) +ᵘ_) (⋆-* One Ψ₁ Φ))
    sub-sem {Φ = Φ} (⊢let {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {q = Many} {π = π} {A = A} de db) h x =
      trans (⟦retype⟧ (sym E) _ fmt δ x)
            (bindC {π} (ih de h _ (sym (sym E)) _ x) (λ v → ihb A Many db h _ (sym (sym E)) _ x v))
      where E = trans (⋆-+ Ψ₂ (Many *ᵘ Ψ₁) Φ) (cong ((Ψ₂ ⋆ Φ) +ᵘ_) (⋆-* Many Ψ₁ Φ))

    sub-sem {Δ = Δ} {Φ = Φ} ⊢unit h x = ⟦retype⟧ {Γ = Δ} (sym (⋆-zero Φ)) ⊢unit fmt δ x

    sub-sem {Φ = Φ} (⊢pair {Ψ₁ = Ψ₁} {Ψ₂ = Ψ₂} {π = π} da db) h x =
      trans (⟦retype⟧ (sym (⋆-+ Ψ₁ Ψ₂ Φ)) _ fmt δ x)
            (bindC {π} (ih da h _ (sym (sym (⋆-+ Ψ₁ Ψ₂ Φ))) _ x)
                   (λ a → bindC {π} (ih db h _ (sym (sym (⋆-+ Ψ₁ Ψ₂ Φ))) _ x) (λ _ → refl)))
    sub-sem (⊢fst {π = π} d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem (⊢snd {π = π} d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem (⊢inl {π = π} d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem (⊢inr {π = π} d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)

    sub-sem {Φ = Φ} (⊢case {Ψs = Ψs} {Ψ = Ψ} {qℓ = qℓ} {qr = qr} {π = π} {A = A} {B = B} ds dl dr) h x =
      trans (⟦retype⟧ (sym (⋆-+ Ψs Ψ Φ)) _ fmt δ x)
            (bindC {π} (ih ds h _ (sym (sym (⋆-+ Ψs Ψ Φ))) _ x)
                   (λ { (inj₁ a) → ihb A qℓ dl h _ (sym (sym (⋆-+ Ψs Ψ Φ))) _ x a
                      ; (inj₂ b) → ihb B qr dr h _ (sym (sym (⋆-+ Ψs Ψ Φ))) _ x b }))

    sub-sem (⊢absurd {π = π} d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem (⊢roll {π = π} wf d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem {Φ = Φ} (⊢fold {Ψa = Ψa} {Ψt = Ψt} {π = π} wf da dt) h x =
      trans (⟦retype⟧ (sym (⋆-+ Ψa Ψt Φ)) _ fmt δ x)
            (bindC {π} (ih da h _ (sym (sym (⋆-+ Ψa Ψt Φ))) _ x)
                   (λ valg → bindC {π} (ih dt h _ (sym (sym (⋆-+ Ψa Ψt Φ))) _ x) (λ _ → refl)))
    sub-sem {Φ = Φ} (⊢unfold {Ψc = Ψc} {Ψs = Ψs} {π = π} {π′ = π′} wf dc ds) h x =
      trans (⟦retype⟧ (sym (⋆-+ Ψc Ψs Φ)) _ fmt δ x)
            (cong₂ (λ m c → bindM π′ m (λ s → ana-semᵛ π π′ wf c s))
                   (ih ds h _ (sym (sym (⋆-+ Ψc Ψs Φ))) _ x)
                   (ih dc h _ (sym (sym (⋆-+ Ψc Ψs Φ))) _ x))
    sub-sem (⊢out {π = π} wf d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem (⊢coerce {π = π} p d) h x = cong (fmapM π _) (sub-sem d h x)
    sub-sem {Δ = Δ} {Φ = Φ} ⊢lit-int h x = ⟦retype⟧ {Γ = Δ} (sym (⋆-zero Φ)) ⊢lit-int fmt δ x
    sub-sem {Δ = Δ} {Φ = Φ} ⊢lit-float h x = ⟦retype⟧ {Γ = Δ} (sym (⋆-zero Φ)) ⊢lit-float fmt δ x
    sub-sem (⊢prim {π = π} p d) h x = bindC {π} (sub-sem d h x) (λ _ → refl)
    sub-sem {Δ = Δ} {Φ = Φ} (⊢sigop c k hf rf m) h x = ⟦retype⟧ {Γ = Δ} (sym (⋆-zero Φ)) (⊢sigop c k hf rf m) fmt δ x
    sub-sem {Δ = Δ} {Φ = Φ} (⊢ref d τ r) h x = ⟦retype⟧ {Γ = Δ} (sym (⋆-zero Φ)) (⊢ref d τ r) fmt δ x
    sub-sem (⊢sub-eff g d) h x = cong (subM g) (sub-sem d h x)
    sub-sem {Γ = Γ} {Φ = Φ} (⊢sub-use p d) h x =
      trans (sub-sem d h _) (cong (GM.⟦ d ⟧ fmt δ) (sym (rows-nat h p x)))

    -- A premise, read through the conclusion's restriction of a transport.
    ih : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ₁ Ψ : Usage n} {U : Usage m} {t A π} {σ : Sub n m} {Φ : Grades n m}
           (d : Γ ⊢[ Ψ₁ ] t ∷ A ! π) (h : SubTy Δ σ Γ Φ)
           (p : Ψ₁ ⊑ᵘ Ψ) (e : Ψ ⋆ Φ ≡ U) (w : Ψ₁ ⋆ Φ ⊑ᵘ U) (x : Env Δ (Ψ ⋆ Φ))
       → GM.⟦ sub-⊢ d h ⟧ fmt δ (restrictᵛ {Γ = Δ} w (subst (Env Δ) e x))
         ≡ GM.⟦ d ⟧ fmt δ (restrictᵛ {Γ = Γ} p (rowsᴰ h Ψ x))
    ih d h p e w x = trans (sub-sem d h _) (cong (GM.⟦ d ⟧ fmt δ) (rows-via h p e w x))

    -- A body under a binder, at a given environment.
    ihb′ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ : Usage n} {t B π} {σ : Sub n m} {Φ : Grades n m}
             (A : Type) (q : Quantity) (d : (Γ , A) ⊢[ q ∷ Ψ ] t ∷ B ! π) (h : SubTy Δ σ Γ Φ)
             (y : Env Δ (Ψ ⋆ Φ)) (a : ⟦ A ⟧ᵛ)
         → GM.⟦ retype (⋆-ext q Ψ Φ) (sub-⊢ d (ext-ty A h)) ⟧ fmt δ (bindᵛ {Γ = Δ} {A = A} q y a)
           ≡ GM.⟦ d ⟧ fmt δ (bindᵛ {Γ = Γ} {A = A} q (rowsᴰ h Ψ y) a)
    ihb′ {Ψ = Ψ} {Φ = Φ} A q d h y a =
      trans (⟦retype⟧ (⋆-ext q Ψ Φ) (sub-⊢ d (ext-ty A h)) fmt δ _)
            (trans (sub-sem d (ext-ty A h) _) (cong (GM.⟦ d ⟧ fmt δ) (rows-ext h A q Ψ y a)))

    ihb0′ : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ : Usage n} {t B π} {σ : Sub n m} {Φ : Grades n m}
              (A : Type) (d : (Γ , A) ⊢[ Zero ∷ Ψ ] t ∷ B ! π) (h : SubTy Δ σ Γ Φ) (y : Env Δ (Ψ ⋆ Φ))
          → GM.⟦ retype (⋆-ext Zero Ψ Φ) (sub-⊢ d (ext-ty A h)) ⟧ fmt δ (bindᵛ0 {Γ = Δ} {A = A} y)
            ≡ GM.⟦ d ⟧ fmt δ (bindᵛ0 {Γ = Γ} {A = A} (rowsᴰ h Ψ y))
    ihb0′ {Ψ = Ψ} {Φ = Φ} A d h y =
      trans (⟦retype⟧ (⋆-ext Zero Ψ Φ) (sub-⊢ d (ext-ty A h)) fmt δ _)
            (trans (sub-sem d (ext-ty A h) _) (cong (GM.⟦ d ⟧ fmt δ) (rows-ext0 h A Ψ y)))

    -- …and through the conclusion's restriction of a transport.
    ihb : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ₂ Ψ : Usage n} {U : Usage m} {t B π} {σ : Sub n m} {Φ : Grades n m}
            (A : Type) (q : Quantity) (d : (Γ , A) ⊢[ q ∷ Ψ₂ ] t ∷ B ! π) (h : SubTy Δ σ Γ Φ)
            (p : Ψ₂ ⊑ᵘ Ψ) (e : Ψ ⋆ Φ ≡ U) (w : Ψ₂ ⋆ Φ ⊑ᵘ U) (x : Env Δ (Ψ ⋆ Φ)) (a : ⟦ A ⟧ᵛ)
        → GM.⟦ retype (⋆-ext q Ψ₂ Φ) (sub-⊢ d (ext-ty A h)) ⟧ fmt δ
            (bindᵛ {Γ = Δ} {A = A} q (restrictᵛ {Γ = Δ} w (subst (Env Δ) e x)) a)
          ≡ GM.⟦ d ⟧ fmt δ (bindᵛ {Γ = Γ} {A = A} q (restrictᵛ {Γ = Γ} p (rowsᴰ h Ψ x)) a)
    ihb {Γ = Γ} A q d h p e w x a =
      trans (ihb′ A q d h _ a) (cong (λ z → GM.⟦ d ⟧ fmt δ (bindᵛ {Γ = Γ} {A = A} q z a)) (rows-via h p e w x))

    ihb0 : ∀ {n m} {Γ : Ctx n} {Δ : Ctx m} {Ψ₂ Ψ : Usage n} {U : Usage m} {t B π} {σ : Sub n m} {Φ : Grades n m}
             (A : Type) (d : (Γ , A) ⊢[ Zero ∷ Ψ₂ ] t ∷ B ! π) (h : SubTy Δ σ Γ Φ)
             (p : Ψ₂ ⊑ᵘ Ψ) (e : Ψ ⋆ Φ ≡ U) (w : Ψ₂ ⋆ Φ ⊑ᵘ U) (x : Env Δ (Ψ ⋆ Φ))
         → GM.⟦ retype (⋆-ext Zero Ψ₂ Φ) (sub-⊢ d (ext-ty A h)) ⟧ fmt δ
             (bindᵛ0 {Γ = Δ} {A = A} (restrictᵛ {Γ = Δ} w (subst (Env Δ) e x)))
           ≡ GM.⟦ d ⟧ fmt δ (bindᵛ0 {Γ = Γ} {A = A} (restrictᵛ {Γ = Γ} p (rowsᴰ h Ψ x)))
    ihb0 {Γ = Γ} A d h p e w x =
      trans (ihb0′ A d h _) (cong (λ z → GM.⟦ d ⟧ fmt δ (bindᵛ0 {Γ = Γ} {A = A} z)) (rows-via h p e w x))
