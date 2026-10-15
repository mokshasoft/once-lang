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
--                   one derivation per pair (a conversion has one meaning);
--   * surface     — the surface judgment's modes agree: a synthesized type is
--                   unique, the domain-given mode is exact and agrees with
--                   synthesis;
--   * effects     — each grade's monad is a monad, the guard's without a
--                   unit (up to bisimilarity at `eff⁺`, `eff`); the morphisms
--                   along the order and into `T∞` are
--                   monad morphisms; the observation respects bisimilarity;
--   * coherence   — a core term's meaning is a function of its judgment, not
--                   of the derivation chosen for it;
--   * term model  — substitution is typed, a pure `let` means its
--                   substitution, and typing survives type substitution;
--   * Freyd       — a computation is central exactly when it is pure, and
--                   only a pure one may be dropped;
--   * recursion   — the fold is the unique algebra morphism, with fusion; the
--                   unfold's computation law; the server is the unique map
--                   into `T∞` its round determines;
--   * totality    — a behaviour is a prefix family; a definition cannot name
--                   itself or a later one; a stream and a server are typed,
--                   and the server runs forever.
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Fin using (Fin)
open import Data.List using (List; []; length)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Purity; pure; act; eff⁺; eff; Many; mk-kind; _⊑π_; ⊑-pe; _·p_; positionGrade; Zero; One)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩; Unit; Void; Id; ν; _+_; _⇒[_]_)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Signature using (Signature; Layer; call)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _+ᵘ_; _*ᵘ_; _⟨_⟩ᶜ)
open import Once.Spec.Core.Syntax using (Defs; []; Tm; let′; _[_]; _⟪_⟫ₜ; _!!_; module Schema)
open Schema using (type)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Spec.Surface.Program using (Denotes)
import Once.Spec.Effect as Effect
import Once.Spec.Observation as Observation
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
    <:-unique : ∀ {m} {A B : Ty m} (p q : A <: B) → p ≡ q
    ⊑π-refl   : ∀ π → π ⊑π π
    ⊑π-trans  : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
    ⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h

------------------------------------------------------------------------
-- The surface judgment's modes agree
------------------------------------------------------------------------

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
  open Observation Σ using (Interp; History; events)
  field
    M-identityˡ : ∀ {π} (u : pure ⊑π π) {X Y : Set} (x : X) (k : X → M π Y) → EqM π (bind π (return u x) k) (k x)
    M-identityʳ : ∀ {π} (u : pure ⊑π π) {X : Set} (m : M π X) → EqM π (bind π m (return u)) m
    M-assoc     : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
                → EqM π (bind π (bind π m f) g) (bind π m (λ x → bind π (f x) g))
    sub-return  : ∀ {π π′} (u : pure ⊑π π) (g : π ⊑π π′) (u′ : pure ⊑π π′) {X : Set} (x : X)
                → EqM π′ (sub g (return u x)) (return u′ x)
    sub-bind    : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
                → EqM π′ (sub g (bind π m k)) (bind π′ (sub g m) (λ x → sub g (k x)))
    toT∞-return : ∀ {π} (u : pure ⊑π π) {X : Set} (x : X) → toT∞ π (return u x) ≈ return∞ x
    toT∞-bind   : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
                → toT∞ π (bind π m k) ≈ (toT∞ π m >>=∞ λ x → toT∞ π (k x))
    toT∞-bindᵍ  : ∀ π₁ π₂ {X Y : Set} (m : M π₁ X) (k : X → M π₂ Y)
                → toT∞ (π₁ ·p π₂) (bindᵍ π₁ π₂ m k) ≈ (toT∞ π₁ m >>=∞ λ x → toT∞ π₂ (k x))
    obs-≈       : ∀ (ι : Interp) (h : History) {X : Set} {m m′ : T∞ X}
                → m ≈ m′ → ∀ n → events ι h m n ≡ events ι h m′ n
    obs-return  : ∀ (ι : Interp) (h : History) {X : Set} (x : X) n → events ι h (return∞ x) n ≡ []

------------------------------------------------------------------------
-- Coherence, and the term model
------------------------------------------------------------------------

module _ (Σ : Signature) (fmt : TargetNum) {s} (S : Defs s) where
  open CoreTyping Σ S
  open Meaning Σ fmt S using (⟦_⟧; DefSem; module DefSem; Env)
  open DefSem using (defs)
  open Domain Σ using (⟦_⟧ᵛ)
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
-- Effects form a Freyd category
------------------------------------------------------------------------

module _ (Σ : Signature) where
  open Effect Σ

  -- A computation is CENTRAL when it commutes with every computation.
  Central : ∀ {Y : Set} → T∞ Y → Set₁
  Central {Y} m = ∀ {W : Set} (n : T∞ W)
                → (m >>=∞ λ y → n >>=∞ λ w → return∞ (y , w)) ≈ (n >>=∞ λ w → m >>=∞ λ y → return∞ (y , w))

  -- The premonoidal pairing: the first arm runs first.
  pairK : ∀ {X Y Z : Set} → (X → T∞ Y) → (X → T∞ Z) → X → T∞ (Y × Z)
  pairK f g x = f x >>=∞ λ y → g x >>=∞ λ z → return∞ (y , z)

  record Freyd : Set₁ where
    field
      pure-central : ∀ {Y : Set} (y : Y) → Central (return∞ y)
      central-pure : ∀ {Y : Set} (m : T∞ Y) → Central m → Σ[ y ∈ Y ] m ≈ return∞ y
      discard-pure : ∀ {Y : Set} (m : T∞ Y) → (∀ {W : Set} (k : T∞ W) → (m >>=∞ λ _ → k) ≈ k)
                   → Σ[ y ∈ Y ] m ≈ return∞ y
      pair-β₁ : ∀ {X Y Z : Set} (f : X → T∞ Y) (g : X → T∞ Z) → (∀ x → Central (g x))
              → ∀ x → (pairK f g x >>=∞ λ p → return∞ (proj₁ p)) ≈ f x
      pair-β₂ : ∀ {X Y Z : Set} (f : X → T∞ Y) (g : X → T∞ Z) → (∀ x → Central (f x))
              → ∀ x → (pairK f g x >>=∞ λ p → return∞ (proj₂ p)) ≈ g x
      pair-η  : ∀ {X Y Z : Set} (h : X → T∞ (Y × Z)) → (∀ x → Central (h x))
              → ∀ x → pairK (λ x → h x >>=∞ λ p → return∞ (proj₁ p)) (λ x → h x >>=∞ λ p → return∞ (proj₂ p)) x ≈ h x

------------------------------------------------------------------------
-- Structured recursion
------------------------------------------------------------------------

  record Recursion : Set₁ where
    open Domain Σ using (foldM; traverseM; anaM)
    field
      -- the fold is the only map that commutes with the constructor
      fold-unique : ∀ π (e : pure ⊑π π) (G : SFunctor) {X : Set} (alg : ⟦ G ⟧SF X → M π X) (h : μS G → M π X)
                  → (∀ x → EqM π (h (inS x)) (bind π (traverseM π e G h x) alg))
                  → ∀ v → EqM π (h v) (foldM π e G alg v)
      -- fusion: a map that commutes with the algebras commutes with the folds
      fold-fusion : ∀ π (e : pure ⊑π π) (G : SFunctor) {X Y : Set} (alg : ⟦ G ⟧SF X → M π X) (alg′ : ⟦ G ⟧SF Y → M π Y)
                      (f : X → M π Y)
                  → (∀ l → EqM π (bind π (alg l) f) (bind π (traverseM π e G f l) alg′))
                  → ∀ v → EqM π (bind π (foldM π e G alg v) f) (foldM π e G alg′ v)
      -- forcing an unfold runs the coalgebra and unfolds the rest
      unfold-out  : ∀ π (G : SFunctor) {X : Set} (c : X → M π (⟦ G ⟧SF X)) (x : X)
                  → EqM π (νM.outν (anaM π G c x)) (fmap π (sfmap G (anaM π G c)) (c x))
      -- THE SERVER, guarded iteration (D311): `iter∞ f` takes a step of `f` —
      -- it ends at once with a value, or runs a round that begins with an
      -- event, then stops with its answer or runs the next round …
      iter-unfold : ∀ {A B : Set} (f : A → B ⊎ T⁺ (B ⊎ A)) (a : A)
                  → iter∞ f a ≈ [ return∞ , (λ m → forget⁺ m >>=∞ [ return∞ , iter∞ f ]′) ]′ (f a)
      -- … and it is the only map that does: a round that does not end begins
      -- with an event, so the equation fixes the tree one event at a time
      iter-unique : ∀ {A B : Set} (f : A → B ⊎ T⁺ (B ⊎ A)) (g : A → T∞ B)
                  → (∀ a → g a ≈ [ return∞ , (λ m → forget⁺ m >>=∞ [ return∞ , g ]′) ]′ (f a))
                  → ∀ a → g a ≈ iter∞ f a

------------------------------------------------------------------------
-- Total and productive
------------------------------------------------------------------------

private
  noVars : TySub 0 0
  noVars ()
  noResp : Respects ∅ₖ ∅ₖ noVars
  noResp ()

record Totality : Set₁ where
  field
    -- what a program does is a prefix family, at every Interpretation
    observable : ∀ (Σ : Signature) (ι : Observation.Interp Σ) (h : Observation.History Σ) {X : Set}
                   (m : Effect.T∞ Σ X) → Observation.PrefixFamily Σ (Observation.events Σ ι h m)
    -- no general recursion
    no-self-reference    : ∀ {Σ p} → ¬ Denotes [] selfReference Σ p
    no-forward-reference : ∀ {Σ p} → ¬ Denotes [] forwardReference Σ p
    -- a stream that calls an operation in every layer is typed, and its
    -- first layer does call it
    stream-typed : CoreTyping._⊩_⊢[_]_∷_!_ tickΣ [] ∅ₖ ∅ [] ticker (ν Id eff) pure
    stream-emits : ∀ fmt (δ : Meaning.DefSem tickΣ fmt [])
                 → ∃[ o ] ∃[ a ] ∃[ k ]
                   Effect.T∞.force
                     (Meaning.⟦_⟧ tickΣ fmt [] (CoreTyping.⊢out Once.Spec.Type.wf-Id (CoreTyping.⊢sub-eff ⊑-pe stream-typed))
                       δ noVars noResp tt)
                   ≡ Effect.node (call o a k)
    -- a server is typed at `eff` …
    server-typed : CoreTyping._⊩_⊢[_]_∷_!_ echoΣ [] ∅ₖ ∅ [] echoServer Void eff
    -- … and runs forever: at depth `n` it has made `n` calls, at every
    -- Interpretation
    server-runs  : ∀ fmt (δ : Meaning.DefSem echoΣ fmt []) n
                 → length (Observation.events echoΣ (Meaning.DefSem.interp δ) [] (Meaning.⟦_⟧ echoΣ fmt [] server-typed δ noVars noResp tt) n) ≡ n

------------------------------------------------------------------------
-- All of it
------------------------------------------------------------------------

record Metatheory : Set₁ where
  field
    types      : Types
    surface    : ∀ (Σ : Signature) {s} (S : Defs s) (nm : Fin s → CanonicalName) → Surface Σ S nm
    effects    : ∀ (Σ : Signature) → Effects Σ
    coherence  : ∀ (Σ : Signature) (fmt : TargetNum) {s} (S : Defs s) → Coherence Σ fmt S
    term-model : ∀ (Σ : Signature) (fmt : TargetNum) {s} (S : Defs s) → TermModel Σ fmt S
    freyd      : ∀ (Σ : Signature) → Freyd Σ
    recursion  : ∀ (Σ : Signature) → Recursion Σ
    totality   : Totality
