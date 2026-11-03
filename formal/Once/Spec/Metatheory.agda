{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Metatheory — what the language promises about itself.
--
-- Claims about the Spec alone; they mention no compiler. Their proofs are not
-- part of the Spec (`Once.Metatheory` proves them, importing only the Spec);
-- if one cannot be proved, the language is wrong.
--
--   * types       — subtyping and the effect order are partial orders with
--                   one derivation per pair (a conversion has one meaning;
--                   a join, where it exists, is unique);
--   * surface     — the surface judgment's modes agree: a synthesized type is
--                   unique, the domain-given mode is exact and agrees with
--                   synthesis;
--   * effects     — each grade's monad is a monad (up to bisimilarity); the
--                   morphisms along the chain and into `T∞` are monad
--                   morphisms and compose (one lift per pair, P7); a trace
--                   respects bisimilarity;
--   * inhabited   — every signature has a world, every well-formed one a
--                   model: no observation is vacuous;
--   * sameness    — a partial equivalence, respected by `>>=` (the kernel of
--                   observation);
--   * coherence   — a core term's meaning is a function of its judgment, not
--                   of the derivation chosen for it; a coercion along `refl`
--                   is the identity and along a composite the composite;
--   * term model  — substitution is typed, a pure `let` means its
--                   substitution, and typing survives type substitution;
--   * Freyd       — up to what is observed, a computation is central
--                   exactly when it is pure, and only a pure one may be
--                   dropped;
--   * recursion   — the fold is the unique algebra morphism, with fusion; the
--                   unfold is the unique coalgebra morphism into the stream
--                   (the loop is the unfold at `K B ⊕ Id`), and the loop is
--                   observed as its unrolling;
--   * totality    — a definition cannot name itself or a later one; a stream
--                   and a server are typed, the server runs forever, and a
--                   silent loop is never observed doing anything.
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; length)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Purity; Finite; fin; pureᶠ; actᶠ; pure; act; eff; Many; mk-kind; _⊑π_; _·p_; positionGrade; Zero; One)
open import Once.Spec.Name using (CanonicalName; NotGenerator)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩; Unit; Void; Id; μ; ν; _+_; _*_; _⇒[_]_; ⟦_⟧F; at₀)
open import Once.Spec.Delay using (_⇓_)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Signature using (Signature; OneName; WellFormed; Layer; call; Op; op; _∶_)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _+ᵘ_; _*ᵘ_; _⟨_⟩ᶜ)
open import Once.Spec.Core.Syntax
  using (Defs; []; Tm; var; lam; app; let′; unit; pair; fst; snd; inl; inr; case; absurd; roll; fold; unfold; out; ren; ext; wk; _[_]; _⟪_⟫ₜ; _!!_; module Schema)
open import Once.Spec.Core.Derived
  using (idᶜ; terminalᶜ; initialᶜ; fstᶜ; sndᶜ; inlᶜ; inrᶜ; applyᶜ; composeᶜ; pairᶜ; caseᶜ; curryᶜ;
         inᶜ; outᶜ; cataᶜ; anaᶜ; mapᶜ; layerᶜ)
open Schema using (type)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Spec.Surface.Program using (Denotes)
import Once.Spec.Effect as Effect
import Once.Spec.Observation as Observation
open import Once.Spec.Trace using (module Tr; _≈ᵗ⟨_⟩_; returned; Calls)
import Once.Spec.Domain as Domain
import Once.Spec.Equivalence as Equivalence
import Once.Spec.Core.Typing as CoreTyping
import Once.Spec.Core.Meaning as Meaning
import Once.Spec.Core.Program as CoreProgram
import Once.Spec.Surface.Typing as SurfaceTyping
open import Once.Spec.Examples

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

record Types : Set where
  field
    <:-refl   : ∀ {m} (A : Ty m) → A <: A
    <:-trans  : ∀ {m} {A B C : Ty m} → A <: B → B <: C → A <: C
    <:-antisym : ∀ {m} {A B : Ty m} → A <: B → B <: A → A ≡ B
    <:-unique : ∀ {m} {A B : Ty m} (p q : A <: B) → p ≡ q
    ⊑π-refl   : ∀ π → π ⊑π π
    ⊑π-trans  : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
    ⊑π-antisym : ∀ {π π′} → π ⊑π π′ → π′ ⊑π π → π ≡ π′
    ⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h

------------------------------------------------------------------------
-- The surface judgment's modes agree
------------------------------------------------------------------------

-- The names a reference may resolve to are distinct (D249, as a program's
-- `Denotes` requires): each entry of Σ is declared once, definitions have
-- their own names, and none is named as an operation or a generator.
record Distinct (Σ : Signature) {s} (nm : Fin s → CanonicalName) : Set where
  field
    one-name    : OneName Σ
    def-inj     : ∀ {d d′} → nm d ≡ nm d′ → d ≡ d′
    def-not-sig : ∀ d {t} → ¬ ((nm d ∶ t) ∈ Σ)
    def-not-gen : ∀ d → NotGenerator (nm d)

record Surface (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName) : Set where
  open SurfaceTyping Σ S nm
  field
    synth-unique : ∀ {m} {Δ : KCtx m} {n} {L : Locals m n} {e A A′ t t′}
                 → _⊢_⇒_↝_ Δ L e A t → _⊢_⇒_↝_ Δ L e A′ t′ → A ≡ A′
    domain-exact : ∀ {m} {Δ : KCtx m} {n} {L : Locals m n} {e A B B′ π t t′}
                 → _⊢_⇐_⇒[_]↦_↝_ Δ L e A π B t → _⊢_⇐_⇒[_]↦_↝_ Δ L e A π B′ t′ → B ≡ B′
    domain-agrees-synth : ∀ {m} {Δ : KCtx m} {n} {L : Locals m n} {e A B T π t t′}
                        → _⊢_⇐_⇒[_]↦_↝_ Δ L e A π B t → _⊢_⇒_↝_ Δ L e T t′
                        → Σ[ A′ ∈ Ty m ] Σ[ π′ ∈ Purity ] (T ≡ A′ ⇒[ mk-kind Many π′ ] B) × π′ ⊑π π

------------------------------------------------------------------------
-- Effects
------------------------------------------------------------------------

record Effects (Σ : Signature) : Set₁ where
  open Effect Σ
  open Observation Σ using (World; History; trace)
  field
    M-identityˡ : ∀ π {X Y : Set} (x : X) (k : X → M π Y) → EqM π (bind π (return π x) k) (k x)
    M-identityʳ : ∀ π {X : Set} (m : M π X) → EqM π (bind π m (return π)) m
    M-assoc     : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
                → EqM π (bind π (bind π m f) g) (bind π m (λ x → bind π (f x) g))
    sub-return  : ∀ {π π′} (g : π ⊑π π′) {X : Set} (x : X) → EqM π′ (sub g (return π x)) (return π′ x)
    sub-bind    : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
                → EqM π′ (sub g (bind π m k)) (bind π′ (sub g m) (λ x → sub g (k x)))
    -- the lifts compose: one lift from each grade to each larger one (P7)
    sub-∘       : ∀ {π₁ π₂ π₃} (g : π₁ ⊑π π₂) (h : π₂ ⊑π π₃) (k : π₁ ⊑π π₃) {X : Set} (m : M π₁ X)
                → EqM π₃ (sub h (sub g m)) (sub k m)
    toT∞-sub    : ∀ {π π′} (g : π ⊑π π′) {X : Set} (m : M π X) → toT∞ π′ (sub g m) ≈ toT∞ π m
    toT∞-return : ∀ π {X : Set} (x : X) → toT∞ π (return π x) ≈ return∞ x
    toT∞-bind   : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
                → toT∞ π (bind π m k) ≈ (toT∞ π m >>=∞ λ x → toT∞ π (k x))
    toT∞-bindᵍ  : ∀ π₁ π₂ {X Y : Set} (m : M π₁ X) (k : X → M π₂ Y)
                → toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k) ≈ (toT∞ π₁ m >>=∞ λ x → toT∞ π₂ (k x))
    -- bisimilar computations have the same trace
    trace-≈     : ∀ (w : World) (h : History) {X : Set} {m m′ : T∞ X}
                → m ≈ m′ → trace w h m ≈ᵗ⟨ _≡_ ⟩ trace w h m′
    -- a computation that returns at once is traced so
    trace-return : ∀ (w : World) (h : History) {X : Set} (x : X) → Tr.next (trace w h (return∞ x)) ⇓ inj₁ (returned x)

------------------------------------------------------------------------
-- No observation is vacuous
------------------------------------------------------------------------

record Inhabited (Σ : Signature) : Set where
  open Observation Σ using (World; Model)
  field
    -- a world answers whenever an answer exists
    a-world : World
    -- an honest signature can be implemented
    a-model : WellFormed Σ → Model

------------------------------------------------------------------------
-- Sameness: a partial equivalence, the kernel of observation
------------------------------------------------------------------------

record Sameness (Σ : Signature) : Set₁ where
  open Effect Σ using (M; bindᵍ; νM; module νM; toT∞; LayerEq)
  open Domain Σ using (⟦_⟧ᵛ)
  open Equivalence Σ using (Same; SameM; SameStream; OneLayer)
  field
    Same-sym   : ∀ (A : Type) {x y} → Same A x y → Same A y x
    Same-trans : ∀ (A : Type) {x y z} → Same A x y → Same A y z → Same A x z
    -- running the same computations, then the same continuations on the same
    -- values, is the same
    SameM-bind : ∀ π₁ π₂ (A B : Type) {m m′ : M π₁ ⟦ A ⟧ᵛ} {f f′ : ⟦ A ⟧ᵛ → M π₂ ⟦ B ⟧ᵛ}
               → SameM π₁ A m m′ → (∀ {x x′} → Same A x x′ → SameM π₂ B (f x) (f′ x′))
               → SameM (π₁ ·p π₂) B (bindᵍ π₁ π₂ m f) (bindᵍ π₁ π₂ m′ f′)
    -- sameness of streams is what a coinductive sameness would be: a fixed
    -- point of one layer …
    stream-out   : ∀ f (G : SFunctor) {v w} → SameStream f G v w → OneLayer f G (SameStream f G) v w
    stream-in    : ∀ f (G : SFunctor) {v w} → OneLayer f G (SameStream f G) v w → SameStream f G v w
    -- … and the greatest: every relation that one layer preserves lies inside it
    stream-coind : ∀ f (G : SFunctor) (R : νM f G → νM f G → Set) → (∀ {v w} → R v w → OneLayer f G R v w)
                 → ∀ {v w} → R v w → SameStream f G v w

------------------------------------------------------------------------
-- Coherence, and the term model
------------------------------------------------------------------------

module _ (Σ : Signature) (fmt : TargetNum) {s} (S : Defs s) where
  open CoreTyping Σ S
  open Meaning Σ fmt S using (⟦_⟧; DefSem; module DefSem; Env)
  open DefSem using (defs)
  open Domain Σ using (⟦_⟧ᵛ; conv)
  open Equivalence Σ using (Same; SameM)

  -- The definitions' meanings are each the same as itself, whichever proof
  -- shows its instance respects the kinds.
  SameDefs : DefSem → Set
  SameDefs δ = ∀ d τ r r′ → Same (type (S !! d) ⟨ τ ⟩) (defs δ d τ r) (defs δ d τ r′)

  -- An environment whose values are each the same as itself.
  SameEnv : ∀ {m n} (σ : TySub m 0) (Γ : Ctx m n) (Ψ : Usage n) → Env σ Γ Ψ → Set
  SameEnv σ ∅       []         γ       = ⊤
  SameEnv σ (Γ ▸ A) (Zero ∷ Ψ) (γ , v) = SameEnv σ Γ Ψ γ
  SameEnv σ (Γ ▸ A) (One  ∷ Ψ) (γ , v) = SameEnv σ Γ Ψ γ × Same (A ⟨ σ ⟩) v v
  SameEnv σ (Γ ▸ A) (Many ∷ Ψ) (γ , v) = SameEnv σ Γ Ψ γ × Same (A ⟨ σ ⟩) v v

  record Coherence : Set where
    field
      coherent : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t A π} (d d′ : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π)
                   (δ : DefSem) → SameDefs δ → (σ : TySub m 0) (r r′ : Respects Δ ∅ₖ σ)
                   (γ : Env σ Γ Ψ) → SameEnv σ Γ Ψ γ
               → SameM π (A ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r′ γ)
      -- a coercion is functorial: along `refl` the identity, along a
      -- composite the composite (each up to sameness)
      conv-id : ∀ {m} (σ : TySub m 0) {A : Ty m} (p : A <: A) {x x′}
              → Same (A ⟨ σ ⟩) x x′ → Same (A ⟨ σ ⟩) (conv σ p x) x′
      conv-∘  : ∀ {m} (σ : TySub m 0) {A B C : Ty m} (p : A <: B) (q : B <: C) (r : A <: C) {x x′}
              → Same (A ⟨ σ ⟩) x x′ → Same (C ⟨ σ ⟩) (conv σ r x) (conv σ q (conv σ p x′))

  record TermModel : Set where
    field
      subst-⊢ : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψₜ Ψᵤ q π A B t u}
              → Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π
              → Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure
              → Δ ⊩ Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] t [ u ] ∷ B ! π
      -- A pure `let` means its substitution (referential transparency).
      let-β : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψₜ Ψᵤ q π A B t u}
                (dt : Δ ⊩ (Γ ▸ A) ⊢[ q ∷ Ψₜ ] t ∷ B ! π) (du : Δ ⊩ Γ ⊢[ Ψᵤ ] u ∷ A ! pure)
                (dl : Δ ⊩ Γ ⊢[ Ψₜ +ᵘ q *ᵘ Ψᵤ ] let′ q u t ∷ B ! π)
                (δ : DefSem) → SameDefs δ → (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
                (γ : Env σ Γ (Ψₜ +ᵘ q *ᵘ Ψᵤ)) → SameEnv σ Γ _ γ
            → SameM π (B ⟨ σ ⟩) (⟦ subst-⊢ dt du ⟧ δ σ r γ) (⟦ dl ⟧ δ σ r γ)
      -- Typing survives every instance of the type variables that respects
      -- their kinds (a polymorphic definition is typed once).
      ty-subst-⊢ : ∀ {m k n} {Δ : KCtx m} {Δ′ : KCtx k} {Γ : Ctx m n} {Ψ t A π} (σ : TySub m k)
                 → Respects Δ Δ′ σ
                 → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π
                 → Δ′ ⊩ Γ ⟨ σ ⟩ᶜ ⊢[ Ψ ] t ⟪ σ ⟫ₜ ∷ A ⟨ σ ⟩ ! π

------------------------------------------------------------------------
-- The categorical structure, and its internal language
------------------------------------------------------------------------

-- Reasoning about a Once program is equational (GOAL.md): a term may be
-- replaced by one equal to it by a law, and the program means the same.
-- `Categorical` states the structure by its universal properties, on the
-- arrows a program writes (the combinators of `Core.Derived`): the arrows at
-- every grade form a category with coproducts and an initial object (the
-- effectful side of the Freyd category), and the effect-free arrows form a
-- bicartesian closed category. `Equations` is the same structure's internal
-- language: the core is a call-by-value λ-calculus whose `let` is the effect
-- structure's bind (for the pure core, the λ-calculus of a cartesian closed
-- category; with effects, the computational λ-calculus). Each law relates two
-- derivations of ONE judgment; where a law would drop, duplicate or reorder an
-- effect, it asks for the term concerned to be effect-free.

module _ (Σ : Signature) (fmt : TargetNum) {s} (S : Defs s) where
  open CoreTyping Σ S
  open Meaning Σ fmt S using (⟦_⟧; DefSem; Env)
  open Equivalence Σ using (SameM)

  -- Two derivations of one judgment mean the same: at every instance of the
  -- type variables, every meaning of the definitions and every environment,
  -- their computations are the same up to what is observed.
  _≅_ : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ t t′ A π}
      → Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π → Δ ⊩ Γ ⊢[ Ψ ] t′ ∷ A ! π → Set
  _≅_ {m} {Δ = Δ} {Γ} {Ψ} {A = A} {π} d d′ =
    ∀ (δ : DefSem) → SameDefs Σ fmt S δ → (σ : TySub m 0) (r : Respects Δ ∅ₖ σ)
      (γ : Env σ Γ Ψ) → SameEnv Σ fmt S σ Γ Ψ γ
    → SameM π (A ⟨ σ ⟩) (⟦ d ⟧ δ σ r γ) (⟦ d′ ⟧ δ σ r γ)

  -- `t` is effect-free: it has a derivation at grade `pure`.
  Pure : ∀ {m n} (Δ : KCtx m) (Γ : Ctx m n) → Tm S m n → Ty m → Set
  Pure Δ Γ t A = ∃[ Ψ ] (Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! pure)

  -- The structure, by its universal properties (β and η together are each
  -- one): a category at every grade; coproducts and the initial object at
  -- every grade; products, the terminal object and exponentials on the
  -- effect-free arrows. Each type is a functor in a variable on the
  -- effect-free arrows (`mapᶜ`; an effectful one would be a traversal, and
  -- which one is a program's choice, not the language's); `μ F` is the
  -- initial F-algebra and `ν F` with effect-free layers the final
  -- F-coalgebra, stated with `F`'s own action (`layerᶜ`). An arm whose result
  -- a law drops, or that a law evaluates twice, must be effect-free to
  -- evaluate.
  record Categorical : Set where
    field
      compose-idˡ   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B π π₀ f}
                      (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (idᶜ B π) f ∷ A ⇒[ mk-kind Many π ] B ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₀) → d ≅ d′
      compose-idʳ   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B π π₀ f}
                      (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π f (idᶜ A π) ∷ A ⇒[ mk-kind Many π ] B ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] B ! π₀) → d ≅ d′
      -- `h` then `g` then `f`, evaluated and applied in the same order on both sides.
      compose-assoc : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B D π π₀ f g h}
                      (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π f (composeᶜ A π g h) ∷ A ⇒[ mk-kind Many π ] D ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (composeᶜ B π f g) h ∷ A ⇒[ mk-kind Many π ] D ! π₀)
                    → d ≅ d′

      fst-pairᶜ     : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π₀ f g}
                    → Pure Δ Γ g (C ⇒[ mk-kind Many pure ] B)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ C pure (fstᶜ A B pure) (pairᶜ C pure f g) ∷ C ⇒[ mk-kind Many pure ] A ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ C ⇒[ mk-kind Many pure ] A ! π₀) → d ≅ d′
      snd-pairᶜ     : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π₀ f g}
                    → Pure Δ Γ f (C ⇒[ mk-kind Many pure ] A)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ C pure (sndᶜ A B pure) (pairᶜ C pure f g) ∷ C ⇒[ mk-kind Many pure ] B ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] g ∷ C ⇒[ mk-kind Many pure ] B ! π₀) → d ≅ d′
      pair-ηᶜ       : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π₀ h}
                    → Pure Δ Γ h (C ⇒[ mk-kind Many pure ] (A * B))
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] pairᶜ C pure (composeᶜ C pure (fstᶜ A B pure) h)
                                                     (composeᶜ C pure (sndᶜ A B pure) h)
                                         ∷ C ⇒[ mk-kind Many pure ] (A * B) ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] h ∷ C ⇒[ mk-kind Many pure ] (A * B) ! π₀) → d ≅ d′
      terminal-uniqueᶜ : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A π₀ h}
                    → Pure Δ Γ h (A ⇒[ mk-kind Many pure ] Unit)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ A ⇒[ mk-kind Many pure ] Unit ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] terminalᶜ A pure ∷ A ⇒[ mk-kind Many pure ] Unit ! π₀) → d ≅ d′

      case-inlᶜ     : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π π₀ f g}
                    → Pure Δ Γ g (B ⇒[ mk-kind Many π ] C)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A π (caseᶜ A B π f g) (inlᶜ A B π) ∷ A ⇒[ mk-kind Many π ] C ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind Many π ] C ! π₀) → d ≅ d′
      case-inrᶜ     : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π π₀ f g}
                    → Pure Δ Γ f (A ⇒[ mk-kind Many π ] C)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ B π (caseᶜ A B π f g) (inrᶜ A B π) ∷ B ⇒[ mk-kind Many π ] C ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] g ∷ B ⇒[ mk-kind Many π ] C ! π₀) → d ≅ d′
      case-ηᶜ       : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B π π₀}
                      (d : Δ ⊩ Γ ⊢[ Ψ ] caseᶜ A B π (inlᶜ A B π) (inrᶜ A B π) ∷ (A + B) ⇒[ mk-kind Many π ] (A + B) ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] idᶜ (A + B) π ∷ (A + B) ⇒[ mk-kind Many π ] (A + B) ! π₀) → d ≅ d′
      initial-uniqueᶜ : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A π π₀ h}
                    → Pure Δ Γ h (Void ⇒[ mk-kind Many π ] A)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ Void ⇒[ mk-kind Many π ] A ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] initialᶜ A π ∷ Void ⇒[ mk-kind Many π ] A ! π₀) → d ≅ d′

      -- apply ∘ ⟨ curry f ∘ fst , snd ⟩ = f, and the closure of `h`'s calls is `h`.
      curry-βᶜ      : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π₀ f}
                    → Pure Δ Γ f ((A * B) ⇒[ mk-kind Many pure ] C)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (A * B) pure (applyᶜ B C)
                                          (pairᶜ (A * B) pure (composeᶜ (A * B) pure (curryᶜ A B pure pure f) (fstᶜ A B pure))
                                                              (sndᶜ A B pure))
                                         ∷ (A * B) ⇒[ mk-kind Many pure ] C ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ (A * B) ⇒[ mk-kind Many pure ] C ! π₀) → d ≅ d′
      curry-ηᶜ      : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B C π₀ h}
                    → Pure Δ Γ h (A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C))
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] curryᶜ A B pure pure
                                          (composeᶜ (A * B) pure (applyᶜ B C)
                                            (pairᶜ (A * B) pure (composeᶜ (A * B) pure h (fstᶜ A B pure)) (sndᶜ A B pure)))
                                         ∷ A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C) ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] h ∷ A ⇒[ mk-kind Many pure ] (B ⇒[ mk-kind Many pure ] C) ! π₀) → d ≅ d′

      -- A type is a functor in its 0th variable, on the effect-free arrows (`mapᶜ`).
      map-idᶜ       : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ T A π₀}
                      (d : Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A A (idᶜ A pure) ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩ ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] idᶜ (T ⟨ at₀ A ⟩) pure ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ A ⟩ ! π₀)
                    → d ≅ d′
      map-composeᶜ  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ T A B C π₀ f g}
                      (d : Δ ⊩ Γ ⊢[ Ψ ] mapᶜ T A C (composeᶜ A pure f g) ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ C ⟩ ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (T ⟨ at₀ A ⟩) pure (mapᶜ T B C f) (mapᶜ T A B g)
                                         ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many pure ] T ⟨ at₀ C ⟩ ! π₀)
                    → d ≅ d′
      -- `μ F` is the initial F-algebra: `cata alg` is an algebra map from `in` (β) …
      cata-βᶜ       : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ F A π₀ alg}
                    → Pure Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (⟦ F ⟧F (μ F)) pure (cataᶜ F pure alg) (inᶜ F)
                                         ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (⟦ F ⟧F (μ F)) pure alg (layerᶜ F (μ F) A (cataᶜ F pure alg))
                                         ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π₀)
                    → d ≅ d′
      -- … and the only one.
      cata-uniqueᶜ  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ Ψ′ F A π₀ π′ alg h}
                    → Pure Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A) → Pure Δ Γ h (μ F ⇒[ mk-kind Many pure ] A)
                    → (e : Δ ⊩ Γ ⊢[ Ψ′ ] composeᶜ (⟦ F ⟧F (μ F)) pure h (inᶜ F) ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π′)
                      (e′ : Δ ⊩ Γ ⊢[ Ψ′ ] composeᶜ (⟦ F ⟧F (μ F)) pure alg (layerᶜ F (μ F) A h)
                                          ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π′)
                    → e ≅ e′
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] cataᶜ F pure alg ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀)
                    → d ≅ d′
      -- `ν F` (layers effect-free) is the final F-coalgebra: `ana c` is a coalgebra map to `out` (β) …
      ana-βᶜ        : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ F A π₀ c}
                    → Pure Δ Γ c (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A)
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A pure (outᶜ F) (anaᶜ F A pure c)
                                         ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ A pure (layerᶜ F A (ν F pureᶠ) (anaᶜ F A pure c)) c
                                         ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π₀)
                    → d ≅ d′
      -- … and the only one.
      ana-uniqueᶜ   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ Ψ′ F A π₀ π′ c h}
                    → Pure Δ Γ c (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A) → Pure Δ Γ h (A ⇒[ mk-kind Many pure ] ν F pureᶠ)
                    → (e : Δ ⊩ Γ ⊢[ Ψ′ ] composeᶜ A pure (outᶜ F) h ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π′)
                      (e′ : Δ ⊩ Γ ⊢[ Ψ′ ] composeᶜ A pure (layerᶜ F A (ν F pureᶠ) h) c
                                          ∷ A ⇒[ mk-kind Many pure ] ⟦ F ⟧F (ν F pureᶠ) ! π′)
                    → e ≅ e′
                    → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ A ⇒[ mk-kind Many pure ] ν F pureᶠ ! π₀)
                      (d′ : Δ ⊩ Γ ⊢[ Ψ ] anaᶜ F A pure c ∷ A ⇒[ mk-kind Many pure ] ν F pureᶠ ! π₀)
                    → d ≅ d′

  -- The internal language: the laws of the core.
  record Equations : Set where
    field
      -- → : a call is a `let` of its argument (β, by value) …
      app-lam   : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B q π π′ t u}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] app (lam A q π′ t) u ∷ B ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ q u t ∷ B ! π) → d ≅ d′
      -- … and an effect-free function is the λ of its calls (η).
      lam-η     : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B q π π′ f}
                → Pure Δ Γ f (A ⇒[ mk-kind q π′ ] B)
                → (d : Δ ⊩ Γ ⊢[ Ψ ] lam A q π′ (app (wk f) (var zero)) ∷ A ⇒[ mk-kind q π′ ] B ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] f ∷ A ⇒[ mk-kind q π′ ] B ! π) → d ≅ d′

      -- `let` is bind: right unit and associativity (`TermModel.let-β` is the
      -- left unit, for an effect-free term) …
      let-unit  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A q π t}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q t (var zero) ∷ A ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] t ∷ A ! π) → d ≅ d′
      let-assoc : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ C q₁ q₂ π t u v}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q₂ (let′ q₁ t u) v ∷ C ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ q₁ t (let′ q₂ u (ren (ext {S = S} {m = m} suc) v)) ∷ C ! π)
                → d ≅ d′
      -- … and an effect-free computation whose result is unused is dropped.
      let-drop  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B q π t u}
                → Pure Δ Γ t A
                → (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q t (wk u) ∷ B ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] u ∷ B ! π) → d ≅ d′

      -- × : a projection of a pair whose other side is effect-free, and an
      -- effect-free pair is the pair of its projections.
      fst-pair  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B π a b}
                → Pure Δ Γ b B
                → (d : Δ ⊩ Γ ⊢[ Ψ ] fst (pair a b) ∷ A ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] a ∷ A ! π) → d ≅ d′
      snd-pair  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B π a b}
                → Pure Δ Γ a A
                → (d : Δ ⊩ Γ ⊢[ Ψ ] snd (pair a b) ∷ B ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] b ∷ B ! π) → d ≅ d′
      pair-η    : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B π p}
                → Pure Δ Γ p (A * B)
                → (d : Δ ⊩ Γ ⊢[ Ψ ] pair (fst p) (snd p) ∷ A * B ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] p ∷ A * B ! π) → d ≅ d′
      -- Unit is terminal for effect-free terms.
      unit-η    : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ π t}
                → Pure Δ Γ t Unit
                → (d : Δ ⊩ Γ ⊢[ Ψ ] t ∷ Unit ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] unit ∷ Unit ! π) → d ≅ d′

      -- + : β for any scrutinee (its effects run, then one arm), η, and a
      -- `let` around a `case` moves into its arms.
      case-inl  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ B C qℓ qr π a l r}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr (inl B a) l r ∷ C ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ qℓ a l ∷ C ! π) → d ≅ d′
      case-inr  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A C qℓ qr π b l r}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr (inr A b) l r ∷ C ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] let′ qr b r ∷ C ! π) → d ≅ d′
      case-η    : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A B qℓ qr π s}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr s (inl B (var zero)) (inr A (var zero)) ∷ A + B ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] s ∷ A + B ! π) → d ≅ d′
      let-case  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ D q qℓ qr π s l r v}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q (case qℓ qr s l r) v ∷ D ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] case qℓ qr s (let′ q l (ren (ext {S = S} {m = m} suc) v))
                                                 (let′ q r (ren (ext {S = S} {m = m} suc) v)) ∷ D ! π)
                → d ≅ d′
      -- Void is initial: once a Void is computed, nothing after it runs.
      absurd-η  : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ A q π e t}
                  (d : Δ ⊩ Γ ⊢[ Ψ ] let′ q e t ∷ A ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] absurd A e ∷ A ! π) → d ≅ d′
      -- μ, ν: a fold of a `roll` folds the children, then applies the algebra;
      -- forcing an unfold runs the coalgebra, then unfolds the children.
      fold-roll : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ F A π alg t}
                → Pure Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A)
                → (d : Δ ⊩ Γ ⊢[ Ψ ] fold F alg (roll F t) ∷ A ! π)
                  (d′ : Δ ⊩ Γ ⊢[ Ψ ] app alg (app (layerᶜ F (μ F) A (cataᶜ F pure alg)) t) ∷ A ! π)
                → d ≅ d′
      out-unfold : ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ F A π c a}
                 → Pure Δ Γ c (A ⇒[ mk-kind Many pure ] ⟦ F ⟧F A)
                 → (d : Δ ⊩ Γ ⊢[ Ψ ] out (unfold F c a) ∷ ⟦ F ⟧F (ν F pureᶠ) ! π)
                   (d′ : Δ ⊩ Γ ⊢[ Ψ ] app (layerᶜ F A (ν F pureᶠ) (anaᶜ F A pure c)) (app c a) ∷ ⟦ F ⟧F (ν F pureᶠ) ! π)
                 → d ≅ d′

------------------------------------------------------------------------
-- Effects form a Freyd category, up to what is observed
------------------------------------------------------------------------

-- A computation over Σ is one over any larger signature, calling the same
-- operations.
module _ {Σ Σ′ : Signature} (ι : Σ ⊆ Σ′) where
  private
    module E  = Effect Σ
    module E′ = Effect Σ′

  liftOp : Op Σ → Op Σ′
  liftOp (op d) = op (ι d)

  lift      : ∀ {X} → E.T∞ X → E′.T∞ X
  liftBlock : ∀ {X} → E.T (X ⊎ E.T∞ X) → E′.T (X ⊎ E′.T∞ X)
  E′.νM.outν (lift m) = liftBlock (E.force m)
  liftBlock (E.roll (E.done (inj₁ x)))     = E′.roll (E′.done (inj₁ x))
  liftBlock (E.roll (E.done (inj₂ m)))     = E′.roll (E′.done (inj₂ (lift m)))
  liftBlock (E.roll (E.node (call o a k))) = E′.roll (E′.node (call (liftOp o) a (λ b → liftBlock (k b))))

-- Two computations COMMUTE when running them in either order is observed
-- the same.
module _ (Σ : Signature) where
  open Effect Σ
  open Equivalence Σ using (_≃_)

  Commute : ∀ {Y W : Set} → T∞ Y → T∞ W → Set
  Commute m n = (m >>=∞ λ y → n >>=∞ λ w → return∞ (y , w)) ≃ (n >>=∞ λ w → m >>=∞ λ y → return∞ (y , w))

module _ (Σ : Signature) where
  open Effect Σ
  open Equivalence Σ using (_≃_)

  -- A computation is CENTRAL when it commutes with every computation, over Σ
  -- and over every larger signature: being central is a property of the
  -- computation, not of which other operations happen to be declared. (Over
  -- Σ alone a poor signature cannot tell: over `tick : Unit → Unit` every
  -- computation is some ticks, and `tick` commutes with each of them.)
  Central : ∀ {Y : Set} → T∞ Y → Set₁
  Central m = ∀ {Σ′} (ι : Σ ⊆ Σ′) {W : Set} (n : Effect.T∞ Σ′ W) → Commute Σ′ (lift ι m) n

  -- The premonoidal pairing: the first arm runs first.
  pairK : ∀ {X Y Z : Set} → (X → T∞ Y) → (X → T∞ Z) → X → T∞ (Y × Z)
  pairK f g x = f x >>=∞ λ y → g x >>=∞ λ z → return∞ (y , z)

  record Freyd : Set₁ where
    field
      pure-central : ∀ {Y : Set} (y : Y) → Central (return∞ y)
      central-pure : ∀ {Y : Set} (m : T∞ Y) → Central m → Σ[ y ∈ Y ] m ≃ return∞ y
      discard-pure : ∀ {Y : Set} (m : T∞ Y) → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≃ k)
                   → Σ[ y ∈ Y ] m ≃ return∞ y
      pair-β₁ : ∀ {X Y Z : Set} (f : X → T∞ Y) (g : X → T∞ Z) → (∀ x → Central (g x))
              → ∀ x → (pairK f g x >>=∞ λ p → return∞ (proj₁ p)) ≃ f x
      pair-β₂ : ∀ {X Y Z : Set} (f : X → T∞ Y) (g : X → T∞ Z) → (∀ x → Central (f x))
              → ∀ x → (pairK f g x >>=∞ λ p → return∞ (proj₂ p)) ≃ g x
      pair-η  : ∀ {X Y Z : Set} (h : X → T∞ (Y × Z)) → (∀ x → Central (h x))
              → ∀ x → pairK (λ x → h x >>=∞ λ p → return∞ (proj₁ p)) (λ x → h x >>=∞ λ p → return∞ (proj₂ p)) x ≃ h x

------------------------------------------------------------------------
-- Structured recursion
------------------------------------------------------------------------

  record Recursion : Set₁ where
    open Domain Σ using (foldM; traverseM)
    field
      -- the fold runs the children's folds, left to right, then the algebra …
      fold-in     : ∀ π (G : SFunctor) {X : Set} (alg : ⟦ G ⟧SF X → M π X) (x : ⟦ G ⟧SF (μS G))
                  → EqM π (foldM π G alg (inS x)) (bind π (traverseM π G (foldM π G alg) x) alg)
      -- … and it is the only map that does
      fold-unique : ∀ π (G : SFunctor) {X : Set} (alg : ⟦ G ⟧SF X → M π X) (h : μS G → M π X)
                  → (∀ x → EqM π (h (inS x)) (bind π (traverseM π G h x) alg))
                  → ∀ v → EqM π (h v) (foldM π G alg v)
      -- fusion: a function that commutes with the algebras commutes with the
      -- folds. It is a pure function: a fold runs every child's fold before
      -- the layer's algebra, so a computation after the whole fold cannot be
      -- moved in between unless effects commute (over binary trees, `a a b b`
      -- is not `a b a b`).
      fold-fusion : ∀ π (G : SFunctor) {X Y : Set} (alg : ⟦ G ⟧SF X → M π X) (alg′ : ⟦ G ⟧SF Y → M π Y)
                      (g : X → Y)
                  → (∀ l → EqM π (fmap π g (alg l)) (alg′ (sfmap G g l)))
                  → ∀ v → EqM π (fmap π g (foldM π G alg v)) (foldM π G alg′ v)
      -- forcing an unfold runs the coalgebra and unfolds the rest …
      unfold-out  : ∀ (f : Finite) (G : SFunctor) {X : Set} (c : X → Mᶠ f (⟦ G ⟧SF X)) (x : X)
                  → EqM (fin f) (νM.outν (ana f G c x)) (fmap (fin f) (sfmap G (ana f G c)) (c x))
      -- … and it is the only map that does: `νM f G` is the final coalgebra
      -- of `M f ∘ G` (so `T∞ B`, the stream `ν (K B ⊕ Id) act`, is the final
      -- coalgebra of `T (B + −)`, and the loop its anamorphism)
      unfold-unique : ∀ (f : Finite) (G : SFunctor) {X : Set} (c : X → Mᶠ f (⟦ G ⟧SF X)) (g : X → νM f G)
                    → (∀ x → EqLayer f (LayerEq G _≈ν_) (νM.outν (g x)) (fmap (fin f) (sfmap G g) (c x)))
                    → ∀ x → g x ≈ν ana f G c x
      -- where one round ends and the next begins is not observed: the loop
      -- is its unrolling (P12)
      loop-unroll : ∀ {A B : Set} (c : A → T (B ⊎ A)) (a : A)
                  → loop c a ≃ (embed (c a) >>=∞ [ return∞ , loop c ]′)

------------------------------------------------------------------------
-- Total and productive
------------------------------------------------------------------------

private
  noVars : TySub 0 0
  noVars ()
  noResp : Respects ∅ₖ ∅ₖ noVars
  noResp ()

record Totality : Set₁ where
  open Observation using (World; trace)
  field
    -- no general recursion
    no-self-reference    : ∀ {Σ p} → ¬ Denotes [] selfReference Σ p
    no-forward-reference : ∀ {Σ p} → ¬ Denotes [] forwardReference Σ p
    -- a stream that calls an operation in every layer is typed, and its
    -- first layer does call it
    stream-typed : CoreTyping._⊩_⊢[_]_∷_!_ tickΣ [] ∅ₖ ∅ [] ticker (ν Id actᶠ) pure
    stream-emits : ∀ fmt (δ : Meaning.DefSem tickΣ fmt [])
                 → ∃[ o ] ∃[ a ] ∃[ k ]
                   Meaning.⟦_⟧ tickΣ fmt [] (CoreTyping.⊢out Once.Spec.Type.wf-Id stream-typed) δ noVars noResp tt
                   ≡ Effect.roll (Effect.node (call o a k))
    -- a server is typed at `eff` …
    server-typed : CoreTyping._⊩_⊢[_]_∷_!_ echoΣ [] ∅ₖ ∅ [] echoServer Void eff
    -- … and runs forever: in every world it makes as many calls as asked
    server-runs  : ∀ fmt (δ : Meaning.DefSem echoΣ fmt []) (w : World echoΣ) n
                 → ∃[ vs ] (length vs ≡ n
                            × Calls (trace echoΣ w [] (Meaning.⟦_⟧ echoΣ fmt [] server-typed δ noVars noResp tt)) vs)
    -- a silent loop is typed, and is never observed doing anything: nothing
    -- of its trace ever arrives (D317)
    silent-typed : CoreTyping._⊩_⊢[_]_∷_!_ [] [] ∅ₖ ∅ [] silentLoop Void eff
    silent-never : ∀ fmt (δ : Meaning.DefSem [] fmt []) (w : World []) o
                 → ¬ (Tr.next (trace [] w [] (Meaning.⟦_⟧ [] fmt [] silent-typed δ noVars noResp tt)) ⇓ o)

------------------------------------------------------------------------
-- All of it
------------------------------------------------------------------------

record Metatheory : Set₁ where
  field
    types      : Types
    surface    : ∀ (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName) → Distinct Σ nm → Surface Σ S nm
    effects    : ∀ (Σ : Signature) → Effects Σ
    inhabited  : ∀ (Σ : Signature) → Inhabited Σ
    sameness   : ∀ (Σ : Signature) → Sameness Σ
    coherence  : ∀ (Σ : Signature) → OneName Σ → ∀ (fmt : TargetNum) {s} (S : Defs s) → Coherence Σ fmt S
    term-model : ∀ (Σ : Signature) → OneName Σ → ∀ (fmt : TargetNum) {s} (S : Defs s) → TermModel Σ fmt S
    categorical : ∀ (Σ : Signature) → OneName Σ → ∀ (fmt : TargetNum) {s} (S : Defs s) → Categorical Σ fmt S
    equations  : ∀ (Σ : Signature) → OneName Σ → ∀ (fmt : TargetNum) {s} (S : Defs s) → Equations Σ fmt S
    freyd      : ∀ (Σ : Signature) → Freyd Σ
    recursion  : ∀ (Σ : Signature) → Recursion Σ
    totality   : Totality
