{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Laws.Tools — what the laws (`Spec.Metatheory.Categorical`,
-- `Equations`) are proved with.
--
-- A law relates two derivations of one judgment. Each side is read through
-- the fundamental lemma (`Coherence.Fundamental.FL`): a derivation means what
-- the derivation under its sub-rules means (`peel`), and that one's meaning is
-- its rule's clause. Every environment the clauses build is a restriction of
-- the law's environment (`Views.Res`), so any two of them agree.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature; OneName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Core.Syntax using (Defs)

module Once.Metatheory.Laws.Tools (Σ : Signature) (u : OneName Σ) (fmt : TargetNum) {s : ℕ} (S : Defs s) where

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; _·p_; _⊑π_; ⊑-pure; 1≤1; 1≤ω)
open import Once.Spec.Type using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _⊑ᵘ_; _⊑∷_; _+ᵘ_; _*ᵘ_; singleUse)
open import Once.Spec.Core.Syntax using (Tm; var)
open import Once.Spec.Core.Typing Σ S
open import Once.Spec.Core.Meaning Σ fmt S
open import Once.Spec.Effect Σ using (M; toT∞; T∞; _≈_)
open import Once.Spec.Domain Σ using (⟦_⟧ᵛ)
open import Once.Spec.Equivalence Σ using (Same; SameM)
open import Once.Spec.Metatheory using (SameDefs; SameEnv)
open import Once.Metatheory.Coherence.Relation Σ
  using (Related; Related-trans; Related-flip; Related-mono; toObserved; ≈-Relatedˡ; ≈-Relatedʳ)
open import Once.Metatheory.Coherence.Layer Σ using (Rel; rel; runs)
open import Once.Metatheory.Coherence.PER Σ using (Same-sym; Same-trans)
open import Once.Metatheory.Coherence.Env Σ fmt S
  using (SlotAgree; Agree; restrictˡ; restrictʳ; selfAgree;
         envˡ-restrict; envʳ-restrict; env*One-restrict; env*Many-restrict; restrict-∘)
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-trans; ⊑ᵘ-+ˡ; ⊑ᵘ-+ʳ; ⊑ᵘ-*One; ⊑ᵘ-*Many)
open import Once.Metatheory.Coherence.Fundamental Σ u fmt S using (module FL)
open import Once.Metatheory.Coherence.Uniqueness Σ S using (ty-unique)
open import Once.Metatheory.Types using (⊑π-refl; ⊑π-trans)

------------------------------------------------------------------------
-- Related computations: an equivalence, and bisimilar ones replace each other
------------------------------------------------------------------------

module _ {A : Type} where
  relTrans : ∀ {π₁ π₂ π₃} {m₁ : M π₁ ⟦ A ⟧ᵛ} {m₂ : M π₂ ⟦ A ⟧ᵛ} {m₃ : M π₃ ⟦ A ⟧ᵛ}
           → Rel π₁ π₂ A m₁ m₂ → Rel π₂ π₃ A m₂ m₃ → Rel π₁ π₃ A m₁ m₃
  relTrans p q = rel (Related-trans (Same-trans A) (runs p) (runs q))

  relSym : ∀ {π π′} {m : M π ⟦ A ⟧ᵛ} {m′ : M π′ ⟦ A ⟧ᵛ} → Rel π π′ A m m′ → Rel π′ π A m′ m
  relSym p = rel (Related-mono (Same-sym A) (Related-flip (runs p)))

  -- Rewriting either side by bisimilarity of its embedding.
  rel≈ˡ : ∀ {π π₀ π′} {m : M π ⟦ A ⟧ᵛ} {m₀ : M π₀ ⟦ A ⟧ᵛ} {m′ : M π′ ⟦ A ⟧ᵛ}
        → toT∞ π m ≈ toT∞ π₀ m₀ → Rel π₀ π′ A m₀ m′ → Rel π π′ A m m′
  rel≈ˡ e p = rel (≈-Relatedˡ e (runs p))

  rel≈ʳ : ∀ {π π′ π₀} {m : M π ⟦ A ⟧ᵛ} {m′ : M π′ ⟦ A ⟧ᵛ} {m₀ : M π₀ ⟦ A ⟧ᵛ}
        → toT∞ π′ m′ ≈ toT∞ π₀ m₀ → Rel π π₀ A m m₀ → Rel π π′ A m m′
  rel≈ʳ e p = rel (≈-Relatedʳ e (runs p))

  -- What a law concludes: related computations at one grade are the same.
  sameM : ∀ {π} {m m′ : M π ⟦ A ⟧ᵛ} → Rel π π A m m′ → SameM π A m m′
  sameM p = toObserved (runs p)

------------------------------------------------------------------------
-- The derivation under the sub-rules
------------------------------------------------------------------------

module _ {m : ℕ} {Δ : KCtx m} where

  -- The last rule is the term's former's.
  Head : ∀ {n} {Γ : Ctx m n} {Ψ t A π} → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Set
  Head (⊢sub-use _ _) = ⊥
  Head (⊢sub-eff _ _) = ⊥
  Head (⊢var _) = ⊤
  Head (⊢lam _ _) = ⊤
  Head (⊢app _ _) = ⊤
  Head (⊢let _ _) = ⊤
  Head ⊢unit = ⊤
  Head (⊢pair _ _) = ⊤
  Head (⊢fst _) = ⊤
  Head (⊢snd _) = ⊤
  Head (⊢inl _) = ⊤
  Head (⊢inr _) = ⊤
  Head (⊢case _ _ _) = ⊤
  Head (⊢absurd _) = ⊤
  Head (⊢roll _ _) = ⊤
  Head (⊢fold _ _ _) = ⊤
  Head (⊢unfold _ _ _) = ⊤
  Head (⊢out _ _) = ⊤
  Head (⊢iter _ _) = ⊤
  Head (⊢coerce _ _) = ⊤
  Head ⊢lit-int = ⊤
  Head ⊢lit-float = ⊤
  Head (⊢prim _ _) = ⊤
  Head (⊢sigop _) = ⊤
  Head (⊢ref _ _ _) = ⊤

  record Peeled {n} {Γ : Ctx m n} {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) : Set where
    constructor peeled
    field
      {Ψ₀}  : Usage n
      {π₀}  : Purity
      D₀    : Δ ⊩ Γ ⊢[ Ψ₀ ] t ∷ A ! π₀
      inc   : Ψ₀ ⊑ᵘ Ψ
      head  : Head D₀
      {grd} : π₀ ⊑π π

  private
    top : ∀ {n} {Γ : Ctx m n} {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Head d → Peeled d
    top d h = peeled d (⊑ᵘ-refl _) h {⊑π-refl _}

  peel : ∀ {n} {Γ : Ctx m n} {Ψ t A π} (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → Peeled d
  peel (⊢sub-use p d) with peel d
  ... | peeled D P h {e} = peeled D (⊑ᵘ-trans P p) h {e}
  peel (⊢sub-eff g d) with peel d
  ... | peeled D P h {e} = peeled D P h {⊑π-trans e g}
  peel d@(⊢var _) = top d tt
  peel d@(⊢lam _ _) = top d tt
  peel d@(⊢app _ _) = top d tt
  peel d@(⊢let _ _) = top d tt
  peel d@⊢unit = top d tt
  peel d@(⊢pair _ _) = top d tt
  peel d@(⊢fst _) = top d tt
  peel d@(⊢snd _) = top d tt
  peel d@(⊢inl _) = top d tt
  peel d@(⊢inr _) = top d tt
  peel d@(⊢case _ _ _) = top d tt
  peel d@(⊢absurd _) = top d tt
  peel d@(⊢roll _ _) = top d tt
  peel d@(⊢fold _ _ _) = top d tt
  peel d@(⊢unfold _ _ _) = top d tt
  peel d@(⊢out _ _) = top d tt
  peel d@(⊢iter _ _) = top d tt
  peel d@(⊢coerce _ _) = top d tt
  peel d@⊢lit-int = top d tt
  peel d@⊢lit-float = top d tt
  peel d@(⊢prim _ _) = top d tt
  peel d@(⊢sigop _) = top d tt
  peel d@(⊢ref _ _ _) = top d tt

-- A variable's derivation uses the variable.
module _ {m : ℕ} {Δ : KCtx m} where
  varUse : ∀ {n} {Γ : Ctx m n} {Ψ i A π} → Δ ⊩ Γ ⊢[ Ψ ] var i ∷ A ! π → singleUse i One ⊑ᵘ Ψ
  varUse (⊢var i) = ⊑ᵘ-refl _
  varUse (⊢sub-use p d) = ⊑ᵘ-trans (varUse d) p
  varUse (⊢sub-eff _ d) = varUse d

------------------------------------------------------------------------
-- A term's grade and usage are independent: derivable at grade `π₁` and at
-- usage `Ψ₂`, it is derivable at both. (A premise a rule scales by `Zero` is
-- typed at any usage; this reads it at the usage the law's environment has.)
------------------------------------------------------------------------

module _ {m : ℕ} {Δ : KCtx m} where
  transfer : ∀ {n} {Γ : Ctx m n} {Ψ₁ Ψ₂ t A A₂ π₁ π₂}
           → Δ ⊩ Γ ⊢[ Ψ₁ ] t ∷ A ! π₁ → Δ ⊩ Γ ⊢[ Ψ₂ ] t ∷ A₂ ! π₂ → Δ ⊩ Γ ⊢[ Ψ₂ ] t ∷ A ! π₁
  transfer (⊢sub-use _ d₁) d₂ = transfer d₁ d₂
  transfer (⊢sub-eff g d₁) d₂ = ⊢sub-eff g (transfer d₁ d₂)
  {-# CATCHALL #-}
  transfer d₁ (⊢sub-use p d₂) = ⊢sub-use p (transfer d₁ d₂)
  {-# CATCHALL #-}
  transfer d₁ (⊢sub-eff _ d₂) = transfer d₁ d₂
  transfer (⊢var i) (⊢var .i) = ⊢var i
  transfer (⊢lam _ b₁) (⊢lam p₂ b₂) = ⊢lam p₂ (transfer b₁ b₂)
  transfer (⊢app df₁ dx₁) (⊢app df₂ dx₂) with ty-unique df₁ df₂
  ... | refl = ⊢app (transfer df₁ df₂) (transfer dx₁ dx₂)
  transfer (⊢let e₁ b₁) (⊢let e₂ b₂) with ty-unique e₁ e₂
  ... | refl = ⊢let (transfer e₁ e₂) (transfer b₁ b₂)
  transfer ⊢unit ⊢unit = ⊢unit
  transfer (⊢pair a₁ b₁) (⊢pair a₂ b₂) = ⊢pair (transfer a₁ a₂) (transfer b₁ b₂)
  transfer (⊢fst d₁) (⊢fst d₂) = ⊢fst (transfer d₁ d₂)
  transfer (⊢snd d₁) (⊢snd d₂) = ⊢snd (transfer d₁ d₂)
  transfer (⊢inl d₁) (⊢inl d₂) = ⊢inl (transfer d₁ d₂)
  transfer (⊢inr d₁) (⊢inr d₂) = ⊢inr (transfer d₁ d₂)
  transfer (⊢case s₁ l₁ r₁) (⊢case s₂ l₂ r₂) with ty-unique s₁ s₂
  ... | refl = ⊢case (transfer s₁ s₂) (transfer l₁ l₂) (transfer r₁ r₂)
  transfer (⊢absurd d₁) (⊢absurd d₂) = ⊢absurd (transfer d₁ d₂)
  transfer (⊢roll wf d₁) (⊢roll _ d₂) = ⊢roll wf (transfer d₁ d₂)
  transfer (⊢fold wf a₁ t₁) (⊢fold _ a₂ t₂) = ⊢fold wf (transfer a₁ a₂) (transfer t₁ t₂)
  transfer (⊢unfold wf c₁ a₁) (⊢unfold _ c₂ a₂) = ⊢unfold wf (transfer c₁ c₂) (transfer a₁ a₂)
  transfer (⊢out wf d₁) (⊢out _ d₂) = ⊢out wf (transfer d₁ d₂)
  transfer (⊢iter f₁ s₁) (⊢iter f₂ s₂) = ⊢iter (transfer f₁ f₂) (transfer s₁ s₂)
  transfer (⊢coerce p d₁) (⊢coerce _ d₂) = ⊢coerce p (transfer d₁ d₂)
  transfer ⊢lit-int ⊢lit-int = ⊢lit-int
  transfer ⊢lit-float ⊢lit-float = ⊢lit-float
  transfer (⊢prim p d₁) (⊢prim .p d₂) = ⊢prim p (transfer d₁ d₂)
  transfer (⊢sigop m₁) (⊢sigop _) = ⊢sigop m₁
  transfer (⊢ref d τ rd) (⊢ref .d .τ _) = ⊢ref d τ rd

------------------------------------------------------------------------
-- The law's environment, and the environments the clauses build from it
------------------------------------------------------------------------

-- Forgetting nothing.
restrict-refl : ∀ {m} (σ : TySub m 0) {n} {Γ : Ctx m n} {Ψ : Usage n} (γ : Env σ Γ Ψ)
              → restrict σ (⊑ᵘ-refl Ψ) γ ≡ γ
restrict-refl σ {Γ = ∅}     {[]}       tt      = refl
restrict-refl σ {Γ = Γ ▸ A} {Zero ∷ Ψ} (γ , v) = cong (_, tt) (restrict-refl σ γ)
restrict-refl σ {Γ = Γ ▸ A} {One ∷ Ψ}  (γ , v) = cong (_, v) (restrict-refl σ γ)
restrict-refl σ {Γ = Γ ▸ A} {Many ∷ Ψ} (γ , v) = cong (_, v) (restrict-refl σ γ)

-- An environment that agrees with itself has values each the same as itself.
agreeSelf : ∀ {m} (σ : TySub m 0) {n} {Γ : Ctx m n} {Ψ : Usage n} {γ : Env σ Γ Ψ}
          → Agree σ Γ Ψ Ψ γ γ → SameEnv Σ fmt S σ Γ Ψ γ
agreeSelf σ {Γ = ∅}     {[]}       a        = tt
agreeSelf σ {Γ = Γ ▸ A} {Zero ∷ Ψ} (a , _)  = agreeSelf σ a
agreeSelf σ {Γ = Γ ▸ A} {One ∷ Ψ}  (a , sv) = agreeSelf σ a , sv
agreeSelf σ {Γ = Γ ▸ A} {Many ∷ Ψ} (a , sv) = agreeSelf σ a , sv

-- One more value, the same as itself.
sameEnv▸ : ∀ {m} (σ : TySub m 0) {n} {Γ : Ctx m n} {Ψ : Usage n} {A : Ty m} (q : Quantity) {γ : Env σ Γ Ψ} {v}
         → SameEnv Σ fmt S σ Γ Ψ γ → SlotAgree σ A q q v v → SameEnv Σ fmt S σ (Γ ▸ A) (q ∷ Ψ) (γ , v)
sameEnv▸ σ Zero se sv = se
sameEnv▸ σ One  se sv = se , sv
sameEnv▸ σ Many se sv = se , sv

-- A value the same as another is the same as itself.
sameRefl : ∀ (A : Type) {x y} → Same A x y → Same A x x
sameRefl A s = Same-trans A s (Same-sym A s)

-- The variable a binder binds holds the value put there.
look0 : ∀ {m} (σ : TySub m 0) {n} {Γ : Ctx m n} {A : Ty m} {Ψ : Usage n} (q : Quantity) {e : Env σ Γ Ψ} {x : ⟦ A ⟨ σ ⟩ ⟧ᵛ}
        (P : singleUse zero One ⊑ᵘ (q ∷ Ψ))
      → lookupᵛ σ (Γ ▸ A) zero (restrict σ {Γ = Γ ▸ A} P (e , slot q {⟦ A ⟨ σ ⟩ ⟧ᵛ} x)) ≡ x
look0 σ Zero (() ⊑∷ _)
look0 σ {A = A} One  {e} {x} (1≤1 ⊑∷ _) = refl
look0 σ {A = A} Many {e} {x} (1≤ω ⊑∷ _) = refl

-- Below `pure` is only `pure`; a sequence is pure only if its first part is.
⊑pure : ∀ {π} → π ⊑π pure → π ≡ pure
⊑pure ⊑-pure = refl

·p-pureˡ : ∀ π₁ π₂ → π₁ ·p π₂ ≡ pure → π₁ ≡ pure
·p-pureˡ pure π₂ e = refl
·p-pureˡ act pure ()
·p-pureˡ act act ()
·p-pureˡ act eff ()
·p-pureˡ eff π₂ ()

·p-pureʳ : ∀ π₁ π₂ → π₁ ·p π₂ ≡ pure → π₂ ≡ pure
·p-pureʳ pure π₂ e = e
·p-pureʳ act pure ()
·p-pureʳ act act ()
·p-pureʳ act eff ()
·p-pureʳ eff π₂ ()

-- Slots: the value a binder holds, at any two quantities.
slotAgree : ∀ {m} (σ : TySub m 0) {B : Ty m} (qa qb : Quantity) {x y : ⟦ B ⟨ σ ⟩ ⟧ᵛ}
          → Same (B ⟨ σ ⟩) x y → SlotAgree σ B qa qb (slot qa x) (slot qb y)
slotAgree σ Zero qb       s = tt
slotAgree σ One  Zero     s = tt
slotAgree σ Many Zero     s = tt
slotAgree σ One  One      s = s
slotAgree σ One  Many     s = s
slotAgree σ Many One      s = s
slotAgree σ Many Many     s = s
