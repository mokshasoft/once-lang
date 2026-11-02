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
--                   and a server are typed, the server runs forever, a
--                   silent loop is never observed doing anything, and no
--                   run of the meaning ever runs out.
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Fin using (Fin)
open import Data.List using (List; []; length)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Purity; Finite; fin; actᶠ; pure; act; eff; Many; mk-kind; _⊑π_; _·p_; positionGrade; Zero; One)
open import Once.Spec.Name using (CanonicalName; NotGenerator)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Type using (Ty; Type; KCtx; ∅ₖ; TySub; Respects; _⟨_⟩; Unit; Void; Id; ν; _+_; _⇒[_]_)
open import Once.Spec.Delay using (_⇓_)
open import Once.Spec.Sub using (_<:_)
open import Once.Spec.Signature using (Signature; OneName; WellFormed; Layer; call; Op; op; _∶_)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.Spec.Polynomial using (SFunctor; ⟦_⟧SF; μS; inS; sfmap)
open import Once.Spec.Context using (Ctx; ∅; _▸_; Usage; []; _∷_; _+ᵘ_; _*ᵘ_; _⟨_⟩ᶜ)
open import Once.Spec.Core.Syntax using (Defs; []; Tm; let′; _[_]; _⟪_⟫ₜ; _!!_; module Schema)
open Schema using (type)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Spec.Surface.Program using (Denotes)
import Once.Spec.Effect as Effect
import Once.Spec.Observation as Observation
open import Once.Spec.Trace using (module Tr; _≈ᵗ⟨_⟩_; returned; exhausted; Calls; Ends)
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
    -- a source run never runs out: the meaning has unlimited memory, so the
    -- trace of every computation, in every world, never ends `exhausted`;
    -- only a compiled run does (D347, D348)
    never-exhausted : ∀ (Σ : Signature) (w : World Σ) h {X} (m : Effect.T∞ Σ X)
                    → ¬ Ends (trace Σ w h m) exhausted

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
    freyd      : ∀ (Σ : Signature) → Freyd Σ
    recursion  : ∀ (Σ : Signature) → Recursion Σ
    totality   : Totality
