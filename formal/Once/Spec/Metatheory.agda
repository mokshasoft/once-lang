-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Metatheory — WHAT THE LANGUAGE PROMISES ABOUT ITSELF (D304).
--
-- A metatheorem is a claim about the Spec ALONE: it mentions no compiler. If
-- one cannot be proved, the LANGUAGE is wrong, not the compiler — D276 made
-- the grades affine precisely so that substitution is typed. So the
-- statements are part of the Spec, read with the definition they constrain;
-- the proofs are not (D140): they live under `Once.Metatheory`, which may
-- import only the Spec and its semantic domain, never the compiler
-- (`scripts/metatheory-gate.sh`). `Once.Certified` carries the proofs, so
-- each statement is on the apex and goes red when the Spec moves.
--
-- Four parts:
--   * `term-model` — for every signature of definitions `S`, the core's TERM
--     MODEL (`Once.Spec.Core.TermModel`): substitution of terms is typed
--     (`subst-⊢`), a pure `let` means its substitution (`let-β`, referential
--     transparency), and substitution of types is typed (`ty-subst-⊢`, D303).
--   * `type-system` — the surface typing judgment (D305): subtyping and the
--     purity order are partial orders whose derivations are unique (so a
--     coercion has one meaning), and a term's usage is a property of the term,
--     not of the mode that typed it — synthesis is unique, checking agrees
--     with it, the domain-given mode is exact.
--   * `effects` — the meaning's effect structure (plan 0.112 E, C4): each
--     grade's `M π` is a monad, subeffecting `subM` and the erasure `toT` to
--     the interaction tree are monad morphisms, and the observation `run`
--     respects return and bind (`then` threads the history).
--   * `recursion` — the fold is the unique algebra morphism out of `μ`, and
--     fusion holds (plan 0.112 D3). STATED, NOT YET PROVED: `Once.Metatheory`
--     postulates both (`Once.Metatheory.Recursion`).
--
-- No type-safety theorem is needed in this setting: the meaning is a TOTAL
-- function on derivations, so every well-typed program means something by
-- construction.
------------------------------------------------------------------------

module Once.Spec.Metatheory where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Contract using (ISig)
open import Once.Spec.Core.PolyTy using (Sig)
open import Once.Spec.Core.TermModel using (TermModel) public
open import Once.Spec.Type.Grade using (Purity; mk-kind; Many)
open import Once.Spec.Type using (Type; _⇒[_]_; μ-type; ⟦_⟧T)
open import Once.Spec.Type.Sub using (_<:_; _⊑π_)
open import Once.Spec.Type.WellFormed using (WellFormedF)
open import Once.Spec.Meaning
  using ( T ; returnT ; _>>=T_ ; Interp ; run ; then ; SigOpEvent
        ; M ; ⟦_⟧ᵛ ; returnM ; bindM ; subM ; toT
        ; in-valueᵛ ; cata-semᵛ ; mapLayerᵛ )
open import Once.Spec.Syntax using (RawExpr)
open import Once.Spec.Typing.Scope using (NamedCtx)
open import Once.Spec.Typing using (_⊢ᵢ_∶_⨾_; _⊢ᶜ_∶_⨾_; _⊢ᵈ_∶_⇒[_]↦_⨾_)
import Once.Spec.Context as Surface

-- The surface typing judgment's laws (D305).
record TypeSystem : Set where
  field
    -- subtyping is a preorder with unique derivations (D226: one judgment)
    <:-refl   : ∀ A → A <: A
    <:-trans  : ∀ {A B C} → A <: B → B <: C → A <: C
    <:-unique : ∀ {A B} (p q : A <: B) → p ≡ q
    -- …and so is the purity order
    ⊑π-refl   : ∀ π → π ⊑π π
    ⊑π-trans  : ∀ {π₁ π₂ π₃} → π₁ ⊑π π₂ → π₂ ⊑π π₃ → π₁ ⊑π π₃
    ⊑π-unique : ∀ {π π′} (g h : π ⊑π π′) → g ≡ h

    -- synthesis is unique
    synth-unique : ∀ {ctx : NamedCtx} {e : RawExpr} {A A′ : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᵢ e ∶ A′ ⨾ Ψ′ → A ≡ A′ × Ψ ≡ Ψ′
    -- checking at one type gives one usage
    check-usage-unique : ∀ {ctx : NamedCtx} {e : RawExpr} {A : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᶜ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ A ⨾ Ψ′ → Ψ ≡ Ψ′
    -- checking agrees with synthesis on usage
    check-agrees-synth : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                       → ctx ⊢ᵢ e ∶ A ⨾ Ψ → ctx ⊢ᶜ e ∶ B ⨾ Ψ′ → Ψ ≡ Ψ′
    -- the domain-given mode agrees with checking at an arrow from its domain
    domain-agrees-check : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : Purity}
                            {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᶜ e ∶ (A ⇒[ mk-kind Many π ] B′) ⨾ Ψ′ → Ψ ≡ Ψ′
    -- a term that synthesizes is domain-given only through its synthesized arrow
    domain-agrees-synth : ∀ {ctx : NamedCtx} {e : RawExpr} {A B S : Type} {π : Purity}
                            {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                        → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵢ e ∶ S ⨾ Ψ′
                        → Σ[ A′ ∈ Type ] Σ[ π′ ∈ Purity ] (S ≡ (A′ ⇒[ mk-kind Many π′ ] B)) × π′ ⊑π π × Ψ ≡ Ψ′
    -- the domain-given mode is exact: its output is determined by its input
    domain-exact : ∀ {ctx : NamedCtx} {e : RawExpr} {A B B′ : Type} {π : Purity}
                     {Ψ Ψ′ : Surface.Usage (NamedCtx.size ctx)}
                 → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B ⨾ Ψ → ctx ⊢ᵈ e ∶ A ⇒[ π ]↦ B′ ⨾ Ψ′ → B ≡ B′ × Ψ ≡ Ψ′

-- The meaning's effect structure (plan 0.112 E, C4).
record Effects : Set₁ where
  field
    -- each grade's `M π` is a monad
    M-identityˡ : ∀ π {X Y : Set} (x : X) (k : X → M π Y) → bindM π (returnM π x) k ≡ k x
    M-identityʳ : ∀ π {X : Set} (m : M π X) → bindM π m (returnM π) ≡ m
    M-assoc     : ∀ π {X Y Z : Set} (m : M π X) (f : X → M π Y) (g : Y → M π Z)
                → bindM π (bindM π m f) g ≡ bindM π m (λ x → bindM π (f x) g)
    -- subeffecting is a monad morphism `M π → M π′`
    subM-return : ∀ {π π′} (g : π ⊑π π′) {X : Set} (x : X) → subM g (returnM π x) ≡ returnM π′ x
    subM-bind   : ∀ {π π′} (g : π ⊑π π′) {X Y : Set} (m : M π X) (k : X → M π Y)
                → subM g (bindM π m k) ≡ bindM π′ (subM g m) (λ x → subM g (k x))
    -- so is the erasure of a grade to the interaction tree
    toT-return  : ∀ π {X : Set} (x : X) → toT π (returnM π x) ≡ returnT x
    toT-bind    : ∀ π {X Y : Set} (m : M π X) (k : X → M π Y)
                → toT π (bindM π m k) ≡ (toT π m >>=T λ x → toT π (k x))
    -- the observation respects return and bind
    run-return  : ∀ (ι : Interp) (h : List SigOpEvent) {X Y : Set} (x : X) (f : X → T Y)
                → then ι h (run ι h (returnT x)) f ≡ run ι h (f x)
    run-bind    : ∀ (ι : Interp) (h : List SigOpEvent) {X Y : Set} (m : T X) (f : X → T Y)
                → run ι h (m >>=T f) ≡ then ι h (run ι h m) f

-- The fold's universal property (plan 0.112 D3).
record Recursion : Set₁ where
  field
    -- `fold alg` is the only `h` that commutes with the constructor
    fold-unique : ∀ π {F A} (wf : WellFormedF F) (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ)
                    (h : ⟦ μ-type F ⟧ᵛ → M π ⟦ A ⟧ᵛ)
                → (∀ x → h (in-valueᵛ wf x) ≡ bindM π (mapLayerᵛ π wf h x) alg)
                → ∀ v → h v ≡ cata-semᵛ π wf alg v
    -- fusion: a map that commutes with the algebras commutes with the folds
    fold-fusion : ∀ π {F A B} (wf : WellFormedF F)
                    (alg : ⟦ ⟦ F ⟧T A ⟧ᵛ → M π ⟦ A ⟧ᵛ) (alg′ : ⟦ ⟦ F ⟧T B ⟧ᵛ → M π ⟦ B ⟧ᵛ)
                    (f : ⟦ A ⟧ᵛ → M π ⟦ B ⟧ᵛ)
                → (∀ y → bindM π (alg y) f ≡ bindM π (mapLayerᵛ π wf f y) alg′)
                → ∀ v → bindM π (cata-semᵛ π wf alg v) f ≡ cata-semᵛ π wf alg′ v

record Metatheory : Set₁ where
  field
    term-model  : ∀ {Fs : ISig} {s : ℕ} (S : Sig Fs s) → TermModel S
    type-system : TypeSystem
    effects     : Effects
    recursion   : Recursion
