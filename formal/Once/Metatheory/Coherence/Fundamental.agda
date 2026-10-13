-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Metatheory.Coherence.Fundamental — THE FUNDAMENTAL LEMMA (plan 0.116
-- D1c): two derivations of one core term, in agreeing environments, mean
-- related computations.
--
--     FL : Γ ⊢[ Ψ ] t ∷ A ! π → Γ ⊢[ Ψ′ ] t ∷ A ! π′ → Agree Γ Ψ Ψ′ x x′
--        → TreeEq∞ (S A) (toT∞ π (⟦ d ⟧ x)) (toT∞ π′ (⟦ d′ ⟧ x′))
--
-- By induction on the two derivations. `⊢sub-use` restricts an environment
-- (agreement survives), `⊢sub-eff` is invisible as a tree (`toT-subM`); the
-- other rules are fixed by the term's former, and a core term determines its
-- type (`Uniqueness`, D310), so the premises are compared at one type — their
-- grades may differ, and only through `toT`. Each former's case is the
-- relation's congruence for its semantic operation (`Layer`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Numerics using (TargetNum)

module Once.Metatheory.Coherence.Fundamental {Fs : ISig} {s : ℕ} (Sg : Sig Fs s) where

open import Data.Bool using (true)
open import Data.Fin using (Fin)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Type.Grade using (Quantity; Zero; One; Many; Purity; pure; eff; prod; mk-kind; _≤q_; positionGrade; _·p_; eff⁺)
open import Once.Spec.Type using (Type; Int; Float; Void; _*_; _+_; _⇒[_]_; μ-type; ν-type; ⟦_⟧T; Functor; K; Id; _⊕_; _⊗_)
open import Once.Spec.Type.WellFormed using (IsBaseType; base-Int; base-Float; base-Unit; base-Prod; base-Sum;
  IsConcrete; con-base; con-fun; WellFormedF)
open import Once.Spec.Type.Sub using (_<:_; _⊑π_)
open import Once.Metatheory.SubLaws using (<:-unique; ⊑π-unique)
open import Once.Functor.Translate using (IsConcrete-irrelevant; WellFormedF-irrelevant)
open import Once.Spec.Context using (Ctx; Usage; _∷_) renaming (_,_ to _,ᶜ_)
open import Once.Spec.Contract using (Impl; Key; valueKeys; valueOf; valueOf-at; _∈K?_)
open import Once.Spec.Equivalence using (TreeEq; ret≈; call≈; halt≈; Same)
open import Once.Spec.Core.PolyTy using (_!!_; _⟪_⟫; module Schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Graded using (⟦_⟧ᵛ; M; toT∞; bindM; returnM; subM; bindᵍ)
open import Once.Spec.Iterative using (TreeEq∞)
open import Once.Denotation.TraceMonadInfLaws using (≈∞-bind; ≈∞-rewrite; embed-≈)
open import Once.Spec.Trace using (T; ret; fmapT)
open import Once.Spec.Environment using (bindᵛ)
open import Once.Spec.GradedOps using (fmapM; injB; prjB; cfᵛ; in-valueᵛ; ⟦_⟧<:ᵛ; sigOpRefᵛ)
import Once.Semantics.Machine as Val
open import Once.Spec.Core.Syntax Sg
open import Once.Spec.Core.Typing Sg
open import Once.Spec.Core.Meaning Sg using (⟦_⟧; DefSem; defs; impl; primSem)
open import Once.Spec.Core.Coherence Sg using (SameDefs)
open import Once.Metatheory.Coherence.Relation
open import Once.Metatheory.Coherence.Env
open import Once.Metatheory.Coherence.Layer
open import Once.Metatheory.Coherence.Uniqueness Sg using (uniq)

------------------------------------------------------------------------
-- The graded monad, compared through `toT∞` at two grades
------------------------------------------------------------------------

bind≈ : ∀ π π′ {X Y : Set} {R : X → X → Set} {R′ : Y → Y → Set}
          {m : M π X} {m′ : M π′ X} {k : X → M π Y} {k′ : X → M π′ Y}
      → TreeEq∞ R (toT∞ π m) (toT∞ π′ m′)
      → (∀ {a b} → R a b → TreeEq∞ R′ (toT∞ π (k a)) (toT∞ π′ (k′ b)))
      → TreeEq∞ R′ (toT∞ π (bindM π m k)) (toT∞ π′ (bindM π′ m′ k′))
bind≈ π π′ {m = m} {m′} {k} {k′} h c = ≈∞-rewrite (toT∞-bindM π m k) (toT∞-bindM π′ m′ k′) (≈∞-bind h c)

bind≈ᵍ : ∀ π₁ π₂ π₁′ π₂′ {X Y : Set} {R : X → X → Set} {R′ : Y → Y → Set}
          {m : M π₁ X} {m′ : M π₁′ X} {k : X → M π₂ Y} {k′ : X → M π₂′ Y}
      → TreeEq∞ R (toT∞ π₁ m) (toT∞ π₁′ m′)
      → (∀ {a b} → R a b → TreeEq∞ R′ (toT∞ π₂ (k a)) (toT∞ π₂′ (k′ b)))
      → TreeEq∞ R′ (toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k)) (toT∞ (π₁′ ·p π₂′) (bindᵍ π₁′ π₂′ m′ k′))
bind≈ᵍ π₁ π₂ π₁′ π₂′ {m = m} {m′} {k} {k′} h c =
  ≈∞-rewrite (toT∞-bindᵍ π₁ π₂ m k) (toT∞-bindᵍ π₁′ π₂′ m′ k′) (≈∞-bind h c)

-- Mapping a pure function over two related computations, at their grades.
fmap≈ : ∀ π π′ {X Y : Set} {R : X → X → Set} {R′ : Y → Y → Set} {m : M π X} {m′ : M π′ X} {f g : X → Y}
      → TreeEq∞ R (toT∞ π m) (toT∞ π′ m′) → (∀ {a b} → R a b → R′ (f a) (g b))
      → TreeEq∞ R′ (toT∞ π (fmapM π f m)) (toT∞ π′ (fmapM π′ g m′))
fmap≈ π π′ {m = m} {m′} {f} {g} h c = ≈∞-rewrite (toT∞-fmapM π f m) (toT∞-fmapM π′ g m′) (≈∞-bind h λ r → retT≈ (c r))

------------------------------------------------------------------------
-- Leaves
------------------------------------------------------------------------

-- A layer of `μ` positions related by `≡` is equal.
LiftF-≡ : ∀ (F : Functor) {X} {x y : Val.⟦ F ⟧F X} → LiftF F _≡_ x y → x ≡ y
LiftF-≡ (K B)   e = e
LiftF-≡ Id      e = e
LiftF-≡ (F ⊕ G) {x = inj₁ x} {inj₁ y} r = cong inj₁ (LiftF-≡ F r)
LiftF-≡ (F ⊕ G) {x = inj₂ x} {inj₂ y} r = cong inj₂ (LiftF-≡ G r)
LiftF-≡ (F ⊕ G) {x = inj₁ _} {inj₂ _} ()
LiftF-≡ (F ⊕ G) {x = inj₂ _} {inj₁ _} ()
LiftF-≡ (F ⊗ G) {x = x , x′} {y , y′} (r , r′) = cong₂ _,_ (LiftF-≡ F r) (LiftF-≡ G r′)

roll-≡ : ∀ {F} (wf : WellFormedF F) {x y} → S (⟦ F ⟧T (μ-type F)) x y → in-valueᵛ wf x ≡ in-valueᵛ wf y
roll-≡ {F} wf s = cong (Val.sem-In F) (LiftF-≡ F (cf-rel (μ-type F) wf s))

-- The primitives' types are base types.
dom-base : ∀ p → IsBaseType (primDom p)
dom-base p-add  = base-Prod base-Int base-Int
dom-base p-sub  = base-Prod base-Int base-Int
dom-base p-mul  = base-Prod base-Int base-Int
dom-base p-div  = base-Prod base-Int base-Int
dom-base p-mod  = base-Prod base-Int base-Int
dom-base p-neg  = base-Int
dom-base p-lt   = base-Prod base-Int base-Int
dom-base p-le   = base-Prod base-Int base-Int
dom-base p-gt   = base-Prod base-Int base-Int
dom-base p-ge   = base-Prod base-Int base-Int
dom-base p-eq   = base-Prod base-Int base-Int
dom-base p-ne   = base-Prod base-Int base-Int
dom-base p-fadd = base-Prod base-Float base-Float
dom-base p-fsub = base-Prod base-Float base-Float
dom-base p-fmul = base-Prod base-Float base-Float
dom-base p-fdiv = base-Prod base-Float base-Float
dom-base p-i2f  = base-Int

cod-base : ∀ p → IsBaseType (primCod p)
cod-base p-add  = base-Int
cod-base p-sub  = base-Int
cod-base p-mul  = base-Int
cod-base p-div  = base-Int
cod-base p-mod  = base-Int
cod-base p-neg  = base-Int
cod-base p-lt   = base-Sum base-Unit base-Unit
cod-base p-le   = base-Sum base-Unit base-Unit
cod-base p-gt   = base-Sum base-Unit base-Unit
cod-base p-ge   = base-Sum base-Unit base-Unit
cod-base p-eq   = base-Sum base-Unit base-Unit
cod-base p-ne   = base-Sum base-Unit base-Unit
cod-base p-fadd = base-Float
cod-base p-fsub = base-Float
cod-base p-fmul = base-Float
cod-base p-fdiv = base-Float
cod-base p-i2f  = base-Float

-- A value contract is read through the membership DECISION, so the typing's
-- membership proof does not matter.
valueOf-irr : ∀ {Σ} (I : Impl Σ) (k : Key) (p p′ : _) → valueOf I k p ≡ valueOf I k p′
valueOf-irr {Σ} I k p p′ = go (k ∈K? valueKeys Σ)
  where
    go : ∀ d → valueOf-at I k p d ≡ valueOf-at I k p′ d
    go (yes _) = refl
    go (no ¬p) = ⊥-elim (¬p p)

-- An FFI reference is related to itself, whichever proofs typed it.
sigop-S : ∀ fmt {Σ} (I : Impl Σ) c {A} (k : IsConcrete A) m m′
        → S A (sigOpRefᵛ fmt Σ I c k m) (sigOpRefᵛ fmt Σ I c k m′)
sigop-S fmt I c (con-base ib) m m′ =
  S-base ib (cong (λ f → injB ib (f tt)) (valueOf-irr I _ _ _))
sigop-S fmt I c (con-fun {k = mk-kind Zero pure} bA bB) m m′ =
  retT≈ (S-base bB (cong (λ f → injB bB (f tt)) (valueOf-irr I _ _ _)))
sigop-S fmt I c (con-fun {k = mk-kind Zero eff} bA bB) m m′ =
  embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind Zero prod} bA bB) m m′ =
  embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind Zero eff⁺} bA bB) m m′ =
  embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind One pure} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = retT≈ (S-base bB (cong (λ f → injB bB (f (prjB bA a′))) (valueOf-irr I _ _ _)))
sigop-S fmt I c (con-fun {k = mk-kind Many pure} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = retT≈ (S-base bB (cong (λ f → injB bB (f (prjB bA a′))) (valueOf-irr I _ _ _)))
sigop-S fmt I c (con-fun {k = mk-kind One eff} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind Many eff} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind One prod} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind Many prod} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind One eff⁺} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = embed-≈ (TreeEq-refl (S-refl-base bB) _)
sigop-S fmt I c (con-fun {k = mk-kind Many eff⁺} bA bB) m m′ a a′ s
  rewrite S-base-≡ bA s = embed-≈ (TreeEq-refl (S-refl-base bB) _)

------------------------------------------------------------------------
-- THE LEMMA
------------------------------------------------------------------------

module _ (fmt : TargetNum) (δ : DefSem) (sd : SameDefs δ) where

  FL : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {t A π π′}
       (d : Γ ⊢[ Ψ ] t ∷ A ! π) (d′ : Γ ⊢[ Ψ′ ] t ∷ A ! π′)
     → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′ → TreeEq∞ (S A) (toT∞ π (⟦ d ⟧ fmt δ x)) (toT∞ π′ (⟦ d′ ⟧ fmt δ x′))

  private
    -- `lam`: the body's head usage is a usage; the bound variable is held on a
    -- side exactly when that side uses it.
    lamS : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A B b π} (q q₁ q₂ : Quantity)
             (le : (q₁ ≤q q) ≡ true) (le′ : (q₂ ≤q q) ≡ true)
             (d : (Γ ,ᶜ A) ⊢[ q₁ ∷ Ψ ] b ∷ B ! π) (d′ : (Γ ,ᶜ A) ⊢[ q₂ ∷ Ψ′ ] b ∷ B ! π)
         → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′
         → S (A ⇒[ mk-kind q π ] B) (⟦ ⊢lam {q = q} le d ⟧ fmt δ x) (⟦ ⊢lam {q = q} le′ d′ ⟧ fmt δ x′)
    lamS {A = A} Zero Zero Zero le le′ d d′ h = FL d d′ (bind00 {A = A} h)
    lamS {A = A} One  Zero Zero le le′ d d′ h = λ a a′ s → FL d d′ (bind00 {A = A} h)
    lamS {A = A} One  Zero One  le le′ d d′ h = λ a a′ s → FL d d′ (bind0ˡ {A = A} One {a′ = a′} h)
    lamS {A = A} One  One  Zero le le′ d d′ h = λ a a′ s → FL d d′ (bind0ʳ {A = A} One {a = a} h)
    lamS {A = A} One  One  One  le le′ d d′ h = λ a a′ s → FL d d′ (bind₂ {A = A} One One {a = a} {a′ = a′} h s)
    lamS {A = A} Many Zero Zero le le′ d d′ h = λ a a′ s → FL d d′ (bind00 {A = A} h)
    lamS {A = A} Many Zero One  le le′ d d′ h = λ a a′ s → FL d d′ (bind0ˡ {A = A} One {a′ = a′} h)
    lamS {A = A} Many Zero Many le le′ d d′ h = λ a a′ s → FL d d′ (bind0ˡ {A = A} Many {a′ = a′} h)
    lamS {A = A} Many One  Zero le le′ d d′ h = λ a a′ s → FL d d′ (bind0ʳ {A = A} One {a = a} h)
    lamS {A = A} Many Many Zero le le′ d d′ h = λ a a′ s → FL d d′ (bind0ʳ {A = A} Many {a = a} h)
    lamS {A = A} Many One  One  le le′ d d′ h = λ a a′ s → FL d d′ (bind₂ {A = A} One One {a = a} {a′ = a′} h s)
    lamS {A = A} Many One  Many le le′ d d′ h = λ a a′ s → FL d d′ (bind₂ {A = A} One Many {a = a} {a′ = a′} h s)
    lamS {A = A} Many Many One  le le′ d d′ h = λ a a′ s → FL d d′ (bind₂ {A = A} Many One {a = a} {a′ = a′} h s)
    lamS {A = A} Many Many Many le le′ d d′ h = λ a a′ s → FL d d′ (bind₂ {A = A} Many Many {a = a} {a′ = a′} h s)
    lamS Zero One  _    () _
    lamS Zero Many _    () _
    lamS Zero Zero One  _ ()
    lamS Zero Zero Many _ ()
    lamS One  Many _    () _
    lamS One  Zero Many _ ()
    lamS One  One  Many _ ()

    appS : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ : Usage n} {A₁ A₂ B q₁ q₂ π π′ π₁ π₂ π₁′ π₂′ f a}
             (e : (A₁ ⇒[ mk-kind q₁ π ] B) ≡ (A₂ ⇒[ mk-kind q₂ π′ ] B))
             (df : Γ ⊢[ Ψ₁ ] f ∷ A₁ ⇒[ mk-kind q₁ π ] B ! π₁) (dx : Γ ⊢[ Ψ₂ ] a ∷ A₁ ! positionGrade q₁ π₂)
             (df′ : Γ ⊢[ Ψ₁′ ] f ∷ A₂ ⇒[ mk-kind q₂ π′ ] B ! π₁′) (dx′ : Γ ⊢[ Ψ₂′ ] a ∷ A₂ ! positionGrade q₂ π₂′)
         → ∀ {x x′} → Agree Γ _ _ x x′
         → TreeEq∞ (S B) (toT∞ _ (⟦ ⊢app df dx ⟧ fmt δ x)) (toT∞ _ (⟦ ⊢app df′ dx′ ⟧ fmt δ x′))
    appS {q₁ = Zero} {π = π} {π₁ = π₁} {π₁′ = π₁′} refl df dx df′ dx′ h =
      bind≈ᵍ π₁ π π₁′ π (FL df df′ (restrict₂ _ _ h)) (λ s → s)
    appS {q₁ = One} {π = π} {π₁ = π₁} {π₂ = π₂} {π₁′ = π₁′} {π₂′ = π₂′} refl df dx df′ dx′ h =
      bind≈ᵍ π₁ _ π₁′ _ (FL df df′ (restrict₂ _ _ h)) λ sf → bind≈ᵍ π₂ π π₂′ π (FL dx dx′ (restrict₂ _ _ h)) λ sx → sf _ _ sx
    appS {q₁ = Many} {π = π} {π₁ = π₁} {π₂ = π₂} {π₁′ = π₁′} {π₂′ = π₂′} refl df dx df′ dx′ h =
      bind≈ᵍ π₁ _ π₁′ _ (FL df df′ (restrict₂ _ _ h)) λ sf → bind≈ᵍ π₂ π π₂′ π (FL dx dx′ (restrict₂ _ _ h)) λ sx → sf _ _ sx

    letS : ∀ {n} {Γ : Ctx n} {Ψ₁ Ψ₂ Ψ₁′ Ψ₂′ : Usage n} {A₁ A₂ B q π₁ π₂ π₁′ π₂′ e b}
             (eq : A₁ ≡ A₂)
             (de : Γ ⊢[ Ψ₁ ] e ∷ A₁ ! positionGrade q π₁) (db : (Γ ,ᶜ A₁) ⊢[ q ∷ Ψ₂ ] b ∷ B ! π₂)
             (de′ : Γ ⊢[ Ψ₁′ ] e ∷ A₂ ! positionGrade q π₁′) (db′ : (Γ ,ᶜ A₂) ⊢[ q ∷ Ψ₂′ ] b ∷ B ! π₂′)
         → ∀ {x x′} → Agree Γ _ _ x x′
         → TreeEq∞ (S B) (toT∞ _ (⟦ ⊢let de db ⟧ fmt δ x)) (toT∞ _ (⟦ ⊢let de′ db′ ⟧ fmt δ x′))
    letS {A₁ = A₁} {q = Zero} refl de db de′ db′ h = FL db db′ (bind00 {A = A₁} (restrict₂ _ _ h))
    letS {A₁ = A₁} {q = One} {π₁ = π₁} {π₂ = π₂} {π₁′ = π₁′} {π₂′ = π₂′} refl de db de′ db′ h =
      bind≈ᵍ π₁ π₂ π₁′ π₂′ (FL de de′ (restrict₂ _ _ h)) λ {v} {v′} s → FL db db′ (bind₂ {A = A₁} One One {a = v} {a′ = v′} (restrict₂ _ _ h) s)
    letS {A₁ = A₁} {q = Many} {π₁ = π₁} {π₂ = π₂} {π₁′ = π₁′} {π₂′ = π₂′} refl de db de′ db′ h =
      bind≈ᵍ π₁ π₂ π₁′ π₂′ (FL de de′ (restrict₂ _ _ h)) λ {v} {v′} s → FL db db′ (bind₂ {A = A₁} Many Many {a = v} {a′ = v′} (restrict₂ _ _ h) s)

    fstS : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A B B′ π π′ p} (eq : (A * B) ≡ (A * B′))
             (d : Γ ⊢[ Ψ ] p ∷ A * B ! π) (d′ : Γ ⊢[ Ψ′ ] p ∷ A * B′ ! π′)
         → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′ → TreeEq∞ (S A) (toT∞ π (⟦ ⊢fst d ⟧ fmt δ x)) (toT∞ π′ (⟦ ⊢fst d′ ⟧ fmt δ x′))
    fstS {π = π} {π′} refl d d′ h = fmap≈ π π′ (FL d d′ h) λ s → proj₁ s

    sndS : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A A′ B π π′ p} (eq : (A * B) ≡ (A′ * B))
             (d : Γ ⊢[ Ψ ] p ∷ A * B ! π) (d′ : Γ ⊢[ Ψ′ ] p ∷ A′ * B ! π′)
         → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′ → TreeEq∞ (S B) (toT∞ π (⟦ ⊢snd d ⟧ fmt δ x)) (toT∞ π′ (⟦ ⊢snd d′ ⟧ fmt δ x′))
    sndS {π = π} {π′} refl d d′ h = fmap≈ π π′ (FL d d′ h) λ s → proj₂ s

    -- `case`: the scrutinees are related, so both take the same arm.
    armS : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A B C qℓ qr π π′ l r}
             (dl : (Γ ,ᶜ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π) (dr : (Γ ,ᶜ B) ⊢[ qr ∷ Ψ ] r ∷ C ! π)
             (dl′ : (Γ ,ᶜ A) ⊢[ qℓ ∷ Ψ′ ] l ∷ C ! π′) (dr′ : (Γ ,ᶜ B) ⊢[ qr ∷ Ψ′ ] r ∷ C ! π′)
           → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′ → (v v′ : ⟦ A + B ⟧ᵛ) → S (A + B) v v′
         → TreeEq∞ (S C)
             (toT∞ π (Data.Sum.[ (λ a → ⟦ dl ⟧ fmt δ (bindᵛ {Γ = Γ} {A = A} qℓ x a))
                              , (λ b → ⟦ dr ⟧ fmt δ (bindᵛ {Γ = Γ} {A = B} qr x b)) ]′ v))
             (toT∞ π′ (Data.Sum.[ (λ a → ⟦ dl′ ⟧ fmt δ (bindᵛ {Γ = Γ} {A = A} qℓ x′ a))
                               , (λ b → ⟦ dr′ ⟧ fmt δ (bindᵛ {Γ = Γ} {A = B} qr x′ b)) ]′ v′))
    armS {A = A} {qℓ = qℓ} dl dr dl′ dr′ h (inj₁ a) (inj₁ a′) s = FL dl dl′ (bind₂ {A = A} qℓ qℓ {a = a} {a′ = a′} h s)
    armS {B = B} {qr = qr} dl dr dl′ dr′ h (inj₂ b) (inj₂ b′) s = FL dr dr′ (bind₂ {A = B} qr qr {a = b} {a′ = b′} h s)
    armS dl dr dl′ dr′ h (inj₁ _) (inj₂ _) ()
    armS dl dr dl′ dr′ h (inj₂ _) (inj₁ _) ()

    caseS : ∀ {n} {Γ : Ctx n} {Ψs Ψ Ψs′ Ψ′ : Usage n} {A A′ B B′ C qℓ qr π₁ π₂ π₁′ π₂′ sc l r}
              (eq : (A + B) ≡ (A′ + B′))
              (ds : Γ ⊢[ Ψs ] sc ∷ A + B ! π₁) (dl : (Γ ,ᶜ A) ⊢[ qℓ ∷ Ψ ] l ∷ C ! π₂) (dr : (Γ ,ᶜ B) ⊢[ qr ∷ Ψ ] r ∷ C ! π₂)
              (ds′ : Γ ⊢[ Ψs′ ] sc ∷ A′ + B′ ! π₁′) (dl′ : (Γ ,ᶜ A′) ⊢[ qℓ ∷ Ψ′ ] l ∷ C ! π₂′)
              (dr′ : (Γ ,ᶜ B′) ⊢[ qr ∷ Ψ′ ] r ∷ C ! π₂′)
          → ∀ {x x′} → Agree Γ _ _ x x′
          → TreeEq∞ (S C) (toT∞ _ (⟦ ⊢case ds dl dr ⟧ fmt δ x)) (toT∞ _ (⟦ ⊢case ds′ dl′ dr′ ⟧ fmt δ x′))
    caseS {π₁ = π₁} {π₂} {π₁′} {π₂′} refl ds dl dr ds′ dl′ dr′ h =
      bind≈ᵍ π₁ π₂ π₁′ π₂′ (FL ds ds′ (restrict₂ _ _ h)) λ {v} {v′} s → armS dl dr dl′ dr′ (restrict₂ _ _ h) v v′ s

    foldS : ∀ {n} {Γ : Ctx n} {Ψa Ψt Ψa′ Ψt′ : Usage n} {F A π π′ π₁ π₂ π₁′ π₂′ alg t}
              (eq : (⟦ F ⟧T A ⇒[ mk-kind Many π ] A) ≡ (⟦ F ⟧T A ⇒[ mk-kind Many π′ ] A))
              (wf wf′ : WellFormedF F) → wf ≡ wf′
           → (da : Γ ⊢[ Ψa ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π ] A ! π₁) (dt : Γ ⊢[ Ψt ] t ∷ μ-type F ! π₂)
              (da′ : Γ ⊢[ Ψa′ ] alg ∷ ⟦ F ⟧T A ⇒[ mk-kind Many π′ ] A ! π₁′) (dt′ : Γ ⊢[ Ψt′ ] t ∷ μ-type F ! π₂′)
          → ∀ {x x′} → Agree Γ _ _ x x′
          → (u : pure ⊑π π) (u′ : pure ⊑π π′)
          → TreeEq∞ (S A) (toT∞ _ (⟦ ⊢fold u wf da dt ⟧ fmt δ x)) (toT∞ _ (⟦ ⊢fold u′ wf′ da′ dt′ ⟧ fmt δ x′))
    foldS {π = π} {π₁ = π₁} {π₂} {π₁′} {π₂′} refl wf .wf refl da dt da′ dt′ h u u′ rewrite ⊑π-unique u′ u =
      bind≈ᵍ π₁ _ π₁′ _ (FL da da′ (restrict₂ _ _ h)) λ {alg} {alg′} salg →
      bind≈ᵍ π₂ π π₂′ π (FL dt dt′ (restrict₂ _ _ h)) λ {v} {v′} e → fold-v alg alg′ salg e
      where
        fold-v : ∀ alg alg′ salg {v v′} → v ≡ v′ → _
        fold-v alg alg′ salg {v} refl = Fold.cata-S u wf alg alg′ salg v

    unfoldS : ∀ {n} {Γ : Ctx n} {Ψc Ψs Ψc′ Ψs′ : Usage n} {F A A′ π π₁ π₂ π₁′ π₂′ c sd}
                (eq : (A ⇒[ mk-kind Many π ] ⟦ F ⟧T A) ≡ (A′ ⇒[ mk-kind Many π ] ⟦ F ⟧T A′))
                (wf wf′ : WellFormedF F) → wf ≡ wf′
             → (dc : Γ ⊢[ Ψc ] c ∷ A ⇒[ mk-kind Many π ] ⟦ F ⟧T A ! π₁) (ds : Γ ⊢[ Ψs ] sd ∷ A ! π₂)
                (dc′ : Γ ⊢[ Ψc′ ] c ∷ A′ ⇒[ mk-kind Many π ] ⟦ F ⟧T A′ ! π₁′) (ds′ : Γ ⊢[ Ψs′ ] sd ∷ A′ ! π₂′)
            → ∀ {x x′} → Agree Γ _ _ x x′
            → TreeEq∞ (S (ν-type F π)) (toT∞ _ (⟦ ⊢unfold wf dc ds ⟧ fmt δ x)) (toT∞ _ (⟦ ⊢unfold wf′ dc′ ds′ ⟧ fmt δ x′))
    unfoldS {π = π} {π₁} {π₂} {π₁′} {π₂′} refl wf .wf refl dc ds dc′ ds′ h =
      bind≈ᵍ π₁ π₂ π₁′ π₂′ (FL dc dc′ (restrict₂ _ _ h)) λ {clo} {clo′} sc →
      fmap≈ π₂ π₂′ (FL ds ds′ (restrict₂ _ _ h)) λ ss → ana-S π wf clo clo′ sc ss

    -- D311: the step, then the seed, then the loop — related steps iterate to
    -- bisimilar trees (`Iter.iter-S`).
    iterS : ∀ {n} {Γ : Ctx n} {Ψf Ψs Ψf′ Ψs′ : Usage n} {A A′ B π₁ π₂ π₁′ π₂′ f sd}
              (eq : (A ⇒[ mk-kind Many eff⁺ ] (B + A)) ≡ (A′ ⇒[ mk-kind Many eff⁺ ] (B + A′)))
            → (df : Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind Many eff⁺ ] (B + A) ! π₁) (ds : Γ ⊢[ Ψs ] sd ∷ A ! π₂)
              (df′ : Γ ⊢[ Ψf′ ] f ∷ A′ ⇒[ mk-kind Many eff⁺ ] (B + A′) ! π₁′) (ds′ : Γ ⊢[ Ψs′ ] sd ∷ A′ ! π₂′)
            → ∀ {x x′} → Agree Γ _ _ x x′
            → TreeEq∞ (S B) (toT∞ _ (⟦ ⊢iter df ds ⟧ fmt δ x)) (toT∞ _ (⟦ ⊢iter df′ ds′ ⟧ fmt δ x′))
    iterS {π₁ = π₁} {π₂} {π₁′} {π₂′} refl df ds df′ ds′ h =
      bind≈ᵍ π₁ _ π₁′ _ (FL df df′ (restrict₂ _ _ h)) λ {step} {step′} sf →
      bind≈ᵍ π₂ prod π₂′ prod (FL ds ds′ (restrict₂ _ _ h)) λ {a} {a′} sa → Iter.iter-S step step′ sf a a′ sa

    outS : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {F F′ π π′ π₁ π₁′ t}
             (eq : ν-type F π ≡ ν-type F′ π′) (wf : WellFormedF F) (wf′ : WellFormedF F′)
             (d : Γ ⊢[ Ψ ] t ∷ ν-type F π ! π₁) (d′ : Γ ⊢[ Ψ′ ] t ∷ ν-type F′ π′ ! π₁′)
         → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′
         → (e : ⟦ F′ ⟧T (ν-type F′ π′) ≡ ⟦ F ⟧T (ν-type F π))
         → TreeEq∞ (S (⟦ F ⟧T (ν-type F π))) (toT∞ (π₁ ·p π) (⟦ ⊢out wf d ⟧ fmt δ x))
                  (toT∞ (π₁′ ·p π′) (subst (λ X → M (π₁′ ·p π′) ⟦ X ⟧ᵛ) e (⟦ ⊢out wf′ d′ ⟧ fmt δ x′)))
    outS {π = π} {π₁ = π₁} {π₁′} refl wf wf′ d d′ h refl rewrite WellFormedF-irrelevant wf′ wf =
      bind≈ᵍ π₁ π π₁′ π (FL d d′ h) λ s → out-S π wf s

    -- `out`'s type `⟦ F ⟧T (ν-type F π)` is not a constructor form, so the
    -- second derivation is inverted at a general type `X` and an equation.
    outL : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {F π π₁ π′ t X} (wf : WellFormedF F)
             (d : Γ ⊢[ Ψ ] t ∷ ν-type F π ! π₁) (d′ : Γ ⊢[ Ψ′ ] out t ∷ X ! π′)
             (e : X ≡ ⟦ F ⟧T (ν-type F π))
         → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′
         → TreeEq∞ (S (⟦ F ⟧T (ν-type F π))) (toT∞ (π₁ ·p π) (⟦ ⊢out wf d ⟧ fmt δ x))
                  (toT∞ π′ (subst (λ X → M π′ ⟦ X ⟧ᵛ) e (⟦ d′ ⟧ fmt δ x′)))
    outL wf d (⊢sub-use p d′) refl h = outL wf d d′ refl (restrictʳ p h)
    outL wf d (⊢sub-eff g d′) refl h = ≈∞-rewrite (≈refl _) (toT∞-subM g _) (outL wf d d′ refl h)
    outL wf d (⊢out wf′ d′) e h = outS (uniq d d′) wf wf′ d d′ h e

    coerceS : ∀ {n} {Γ : Ctx n} {Ψ Ψ′ : Usage n} {A B π π′ t} (p p′ : A <: B) → p ≡ p′
             → (d : Γ ⊢[ Ψ ] t ∷ A ! π) (d′ : Γ ⊢[ Ψ′ ] t ∷ A ! π′)
            → ∀ {x x′} → Agree Γ Ψ Ψ′ x x′
            → TreeEq∞ (S B) (toT∞ π (⟦ ⊢coerce p d ⟧ fmt δ x)) (toT∞ π′ (⟦ ⊢coerce p′ d′ ⟧ fmt δ x′))
    coerceS {π = π} {π′} p .p refl d d′ h =
      ≈∞-rewrite (toT∞-fmapM π ⟦ p ⟧<:ᵛ _) (toT∞-fmapM π′ ⟦ p ⟧<:ᵛ _)
        (≈∞-bind (FL d d′ h) λ s → retT≈ (coerce-S p s))

  FL (⊢sub-use p d) d′ h = FL d d′ (restrictˡ p h)
  FL (⊢sub-eff g d) d′ h = ≈∞-rewrite (toT∞-subM g _) (≈refl _) (FL d d′ h)
  FL (⊢out wf d) d′ h = outL wf d d′ refl h
  {-# CATCHALL #-}
  FL d (⊢sub-use p d′) h = FL d d′ (restrictʳ p h)
  {-# CATCHALL #-}
  FL d (⊢sub-eff g d′) h = ≈∞-rewrite (≈refl _) (toT∞-subM g _) (FL d d′ h)
  FL {Γ = Γ} (⊢var i) (⊢var .i) h = retT≈ (lookup-S Γ i h)
  FL (⊢lam {q = q} {q' = q₁} le d) (⊢lam {q' = q₂} le′ d′) h = retT≈ (lamS q q₁ q₂ le le′ d d′ h)
  FL (⊢app df dx) (⊢app df′ dx′) h = appS (uniq df df′) df dx df′ dx′ h
  FL (⊢let de db) (⊢let de′ db′) h = letS (uniq de de′) de db de′ db′ h
  FL ⊢unit ⊢unit h = retT≈ tt
  FL (⊢pair {π₁ = π₁} {π₂} da db) (⊢pair {π₁ = π₁′} {π₂′} da′ db′) h =
    bind≈ᵍ π₁ π₂ π₁′ π₂′ (FL da da′ (restrict₂ _ _ h)) λ sa →
    fmap≈ π₂ π₂′ (FL db db′ (restrict₂ _ _ h)) λ sb → (sa , sb)
  FL (⊢fst d) (⊢fst d′) h = fstS (uniq d d′) d d′ h
  FL (⊢snd d) (⊢snd d′) h = sndS (uniq d d′) d d′ h
  FL (⊢inl {π = π} d) (⊢inl {π = π′} d′) h = fmap≈ π π′ (FL d d′ h) λ s → s
  FL (⊢inr {π = π} d) (⊢inr {π = π′} d′) h = fmap≈ π π′ (FL d d′ h) λ s → s
  FL (⊢case ds dl dr) (⊢case ds′ dl′ dr′) h = caseS (uniq ds ds′) ds dl dr ds′ dl′ dr′ h
  FL (⊢absurd {π = π} d) (⊢absurd {π = π′} d′) h = bind≈ π π′ (FL d d′ h) λ {v} _ → ⊥-elim v
  FL (⊢roll {π = π} wf d) (⊢roll {π = π′} wf′ d′) h =
    fmap≈ π π′ (FL d d′ h) λ s → (trans (roll-≡ wf s) (cong (λ w → in-valueᵛ w _) (WellFormedF-irrelevant wf wf′)))
  FL (⊢fold u wf da dt) (⊢fold u′ wf′ da′ dt′) h = foldS (uniq da da′) wf wf′ (WellFormedF-irrelevant wf wf′) da dt da′ dt′ h u u′
  FL (⊢unfold wf dc ds) (⊢unfold wf′ dc′ ds′) h = unfoldS (uniq dc dc′) wf wf′ (WellFormedF-irrelevant wf wf′) dc ds dc′ ds′ h
  FL (⊢iter df ds) (⊢iter df′ ds′) h = iterS (uniq df df′) df ds df′ ds′ h
  FL (⊢coerce p d) (⊢coerce p′ d′) h = coerceS p p′ (<:-unique p p′) d d′ h
  FL ⊢lit-int ⊢lit-int h = retT≈ refl
  FL ⊢lit-float ⊢lit-float h = retT≈ refl
  FL (⊢prim {π = π} p d) (⊢prim {π = π′} .p d′) h =
    fmap≈ π π′ (FL d d′ h) λ s → (S-base (cod-base p) (cong (primSem p fmt) (S-base-≡ (dom-base p) s)))
  FL (⊢sigop c k _ _ m) (⊢sigop .c k′ _ _ m′) h
    rewrite IsConcrete-irrelevant k′ k = retT≈ (sigop-S fmt (impl δ) c k m m′)
  FL (⊢ref d τ r) (⊢ref .d .τ r′) h = retT≈ (Same→S (type (Sg !! d) ⟪ τ ⟫) (sd d τ r r′))
