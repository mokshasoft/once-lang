{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.SpecTests.Metatheory — rejection witnesses for the hypotheses of
-- `Once.Spec.Metatheory`'s laws (plan 0.142 step 6).
--
-- A restriction that no counterexample needs makes a law weaker than the
-- truth. Each witness here takes one law, lifts one restriction, and
-- refutes the result at a small concrete program, by computation:
--
--   1. uniqueness of the fold (D369): its hypothesis is an equation at the
--      conclusion's usage. At another usage it can hold vacuously, for a
--      context entry no environment fills, and then `h` need not be the
--      fold;
--   2. `map` is effect-free (D369): an effectful `map` at a pair runs
--      `f ∘ g` component by component (`g, f, g, f`), and `map f ∘ map g`
--      runs `g` on both first (`g, g, f, f`), so the functor law fails;
--   3. naturality asks the types strictly positive (D371): at
--      `(a ⇒ a) ⇒ (a ⇒ a)`, where `map` types only for `f : A → A`, the
--      definition `g ↦ g ∘ g` does not commute with it.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.SpecTests.Metatheory (fmt : TargetNum) where

open import Data.Fin using (Fin; zero; suc)
import Data.Nat as ℕ
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Spec.Grade using (Purity; pure; act; Zero; One; Many; mk-kind; 0≤q; 1≤ω; ω≤ω)
open import Once.Spec.Type
  using (Ty; Fun; KCtx; ∅ₖ; any; TySub; _⟨_⟩; at₀; var; K; Unit; Void; _+_; _*_; _⇒[_]_; μ; ⟦_⟧F; wf-K; b-Unit)
open import Once.Spec.Signature using (Signature; _∶_; operation; unit)
open import Once.Spec.Name using (canonical)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Function using (case_of_)
open import Once.Spec.Context using (Ctx; ∅; _▸_; []; _∷_; zeroUsage; _⊑ᵘ_; _⊑∷_)
open import Once.Spec.Core.Syntax
  using (Defs; []; _▷_; _!!_; Schema; schema; Tm; var; lam; app; let′; unit; pair; fst; snd; inl; inr; case; ref; sigop; wk)
open import Once.Spec.Core.Derived using (composeᶜ; cataᶜ; inᶜ; layerᶜ; mapᶜ; mapAtᶜ)
open import Once.Spec.Core.Program using (Tele; []; def; teleSem)
open import Once.Spec.Observation using (Model)
open import Once.Spec.Polynomial using (inS)
open import Once.Spec.Equivalence using (inR; RelM; Same)
open import Once.Spec.Metatheory using (_≅_; Pure; _≅ₚ_; ParamDefs)
import Once.Spec.Core.Typing as CoreTyping
import Once.Spec.Core.Meaning as Meaning
open import Once.Metatheory.Coherence.Relation using (returnRel; returnRel⁻; fromObserved; toObserved; fwd; aWorld)
import Once.Metatheory.Run as Run

------------------------------------------------------------------------
-- The setting: no operations, no definitions
------------------------------------------------------------------------

Σ₀ : Signature
Σ₀ = []

S₀ : Defs 0
S₀ = []

model₀ : Model Σ₀
model₀ = record { constantᵐ = λ () ; valueᵐ = λ () }

Bool : Ty 0
Bool = Unit + Unit

-- A computation of grade `pure` is its value: related exactly when its
-- values are.
obs⁻ : ∀ Σ {X Y : Set} {R : X → Y → Set} {x y} → RelM Σ pure R x y → R x y
obs⁻ Σ o = returnRel⁻ Σ (fromObserved Σ o)

-- (`Bool` is `true + false`.)
false≠true : Same Σ₀ Bool (inj₂ tt) (inj₁ tt) → ⊥
false≠true ()

zero⊑ : ∀ {n} → zeroUsage {n} ⊑ᵘ zeroUsage
zero⊑ {0}       = []
zero⊑ {ℕ.suc n} = 0≤q ⊑∷ zero⊑

------------------------------------------------------------------------
-- 1. The fold's uniqueness, with its hypothesis at another usage
------------------------------------------------------------------------

module Fold where
  open CoreTyping Σ₀ S₀
  open Meaning Σ₀ fmt S₀ using (DefSem)

  -- D369's `cata-uniqueᶜ`, with the hypothesis `h ∘ in = alg ∘ F h` at a
  -- usage `Ψ′` of its own rather than the conclusion's `Ψ`.
  CataUniqueAtAnyUsage : Set
  CataUniqueAtAnyUsage =
    ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ Ψ′ F A π₀ π′ alg h}
    → Pure Σ₀ fmt S₀ Δ Γ alg (⟦ F ⟧F A ⇒[ mk-kind Many pure ] A)
    → Pure Σ₀ fmt S₀ Δ Γ h (μ F ⇒[ mk-kind Many pure ] A)
    → (e : Δ ⊩ Γ ⊢[ Ψ′ ] composeᶜ (⟦ F ⟧F (μ F)) pure h (inᶜ F) ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π′)
      (e′ : Δ ⊩ Γ ⊢[ Ψ′ ] composeᶜ (⟦ F ⟧F (μ F)) pure alg (layerᶜ F (μ F) A h)
                           ∷ ⟦ F ⟧F (μ F) ⇒[ mk-kind Many pure ] A ! π′)
    → _≅_ Σ₀ fmt S₀ e e′
    → (d : Δ ⊩ Γ ⊢[ Ψ ] h ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀)
      (d′ : Δ ⊩ Γ ⊢[ Ψ ] cataᶜ F pure alg ∷ μ F ⇒[ mk-kind Many pure ] A ! π₀)
    → _≅_ Σ₀ fmt S₀ d d′

  -- The counterexample: `Γ = x : Void`, `F = K Unit` (so `μ F` is a single
  -- leaf), `A = Bool`, `alg = const true`, `h = const false`. At usage
  -- `[One]` an environment holds a `Void`, so none exists and the hypothesis
  -- holds vacuously; at `[Zero]` the empty environment exists, and `h` is not
  -- the fold.
  private
    U : Fun 0
    U = K Unit

    ΓV : Ctx 0 1
    ΓV = ∅ ▸ Void

    alg h : ∀ {n} → Tm S₀ 0 n
    alg = lam Unit Many pure (inl Unit unit)
    h   = lam (μ U) Many pure (inr Unit unit)

    ⊢alg : ∀ {n} {Γ : Ctx 0 n} → ∅ₖ ⊩ Γ ⊢[ zeroUsage ] alg ∷ Unit ⇒[ mk-kind Many pure ] Bool ! pure
    ⊢alg = ⊢lam 0≤q (⊢inl ⊢unit)

    ⊢h : ∀ {n} {Γ : Ctx 0 n} → ∅ₖ ⊩ Γ ⊢[ zeroUsage ] h ∷ μ U ⇒[ mk-kind Many pure ] Bool ! pure
    ⊢h = ⊢lam 0≤q (⊢inr ⊢unit)

    -- f ∘ g, for closed f and g (the shape `composeᶜ` unfolds to)
    ⊢∘ : ∀ {A B C : Ty 0} {f g : Tm S₀ 0 1}
       → ∅ₖ ⊩ ΓV ⊢[ zeroUsage ] f ∷ B ⇒[ mk-kind Many pure ] C ! pure
       → ∅ₖ ⊩ ΓV ▸ (B ⇒[ mk-kind Many pure ] C) ⊢[ zeroUsage ] wk g ∷ A ⇒[ mk-kind Many pure ] B ! pure
       → ∅ₖ ⊩ ΓV ⊢[ Zero ∷ [] ] composeᶜ A pure f g ∷ A ⇒[ mk-kind Many pure ] C ! pure
    ⊢∘ df dg = ⊢let {q = One} df (⊢let {q = Many} dg
                 (⊢lam ω≤ω (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))

    ⊢in : ∀ {n} {Γ : Ctx 0 n} → ∅ₖ ⊩ Γ ⊢[ zeroUsage ] inᶜ U ∷ Unit ⇒[ mk-kind Many pure ] μ U ! pure
    ⊢in = ⊢lam 1≤ω (⊢roll (wf-K b-Unit) (⊢var zero))

    ⊢layer : ∀ {Γ : Ctx 0 2} → ∅ₖ ⊩ Γ ⊢[ zeroUsage ] layerᶜ U (μ U) Bool h ∷ Unit ⇒[ mk-kind Many pure ] Unit ! pure
    ⊢layer = ⊢let {Ψ₁ = zeroUsage} {Ψ₂ = zeroUsage} {q = Many} ⊢h (⊢sub-use (0≤q ⊑∷ zero⊑) (⊢lam 1≤ω (⊢var zero)))

    e e′ : ∅ₖ ⊩ ΓV ⊢[ One ∷ [] ] _ ∷ Unit ⇒[ mk-kind Many pure ] Bool ! pure
    e  = ⊢sub-use (0≤q ⊑∷ []) (⊢∘ ⊢h ⊢in)
    e′ = ⊢sub-use (0≤q ⊑∷ []) (⊢∘ ⊢alg ⊢layer)

    -- `cataᶜ U pure alg`: the fold applies the algebra (variable 1) to the tree (0).
    d d′ : ∅ₖ ⊩ ΓV ⊢[ Zero ∷ [] ] _ ∷ μ U ⇒[ mk-kind Many pure ] Bool ! pure
    d  = ⊢h
    d′ = ⊢let {q = Many} ⊢alg (⊢lam 1≤ω (⊢fold (wf-K b-Unit) (⊢var (suc zero)) (⊢var zero)))

    vacuous : _≅_ Σ₀ fmt S₀ e e′
    vacuous δ _ σ r ((_ , ()))

    δ₀ : DefSem
    δ₀ = record { defs = λ () ; model = model₀ }

    -- at the leaf, `h` gives false and the fold true
    differ : ¬ _≅_ Σ₀ fmt S₀ d d′
    differ p = false≠true (obs⁻ Σ₀ (obs⁻ Σ₀ (p δ₀ (λ ()) (λ ()) (λ ()) (tt , tt) tt) (inS tt) (inS tt) (inR tt)))

  cata-unique-at-any-usage : ¬ CataUniqueAtAnyUsage
  cata-unique-at-any-usage law = differ (law (_ , ⊢alg) (_ , ⊢h) e e′ vacuous d d′)

------------------------------------------------------------------------
-- 2. An effectful `map` breaks the functor law
------------------------------------------------------------------------

-- `mapᶜ` at a grade `π` of its own: its body, applying `f` at each
-- occurrence. At `pure` it is `mapᶜ`, and the law below is `map-composeᶜ`.
mapEffᶜ : ∀ {s} {S : Defs s} {m n} → Ty (ℕ.suc m) → Ty m → Ty m → Purity → Tm S m n → Tm S m n
mapEffᶜ T A B π f = let′ Many f (lam (T ⟨ at₀ A ⟩) Many π (mapAtᶜ A B T (var (suc zero)) (var zero)))

-- D369's `map-composeᶜ`, for that `map`, over a signature `Σ`.
MapComposeAnyGrade : Signature → Set
MapComposeAnyGrade Σ = let open CoreTyping Σ S₀ in
  ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ T A B C π π₀ f g}
    (d : Δ ⊩ Γ ⊢[ Ψ ] mapEffᶜ T A C π (composeᶜ A π f g) ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] T ⟨ at₀ C ⟩ ! π₀)
    (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (T ⟨ at₀ A ⟩) π (mapEffᶜ T B C π f) (mapEffᶜ T A B π g)
                       ∷ T ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] T ⟨ at₀ C ⟩ ! π₀)
  → _≅_ Σ fmt S₀ d d′

-- The counterexample: two operations `f, g : Unit → Unit`, `T = a * a`.
-- `map (f ∘ g)` calls `g, f, g, f`; `map f ∘ map g` calls `g, g, f, f`.
private
  fN gN : _
  fN = canonical ("f" ∷ [])
  gN = canonical ("g" ∷ [])

  Σ₂ : Signature
  Σ₂ = (fN ∶ operation unit Many unit) ∷ (gN ∶ operation unit Many unit) ∷ []

module EffMap where
  open CoreTyping Σ₂ S₀
  open Meaning Σ₂ fmt S₀ using (DefSem)
  open Run Σ₂ using (run; rb-call; rb-ret; ra-go)

  private
    U⇒U P : Ty 0
    U⇒U = Unit ⇒[ mk-kind Many act ] Unit
    P   = Unit * Unit
    T₂ : Ty 1
    T₂ = var zero * var zero

    fᵗ gᵗ : ∀ {n} → Tm S₀ 0 n
    fᵗ = sigop fN (operation unit Many unit)
    gᵗ = sigop gN (operation unit Many unit)

    ⊢f : ∀ {n} {Γ : Ctx 0 n} → ∅ₖ ⊩ Γ ⊢[ zeroUsage ] fᵗ ∷ U⇒U ! pure
    ⊢f = ⊢sigop (here refl)
    ⊢g : ∀ {n} {Γ : Ctx 0 n} → ∅ₖ ⊩ Γ ⊢[ zeroUsage ] gᵗ ∷ U⇒U ! pure
    ⊢g = ⊢sigop (there (here refl))

    -- map at a pair: `h` on each component, left first
    ⊢map₀ : ∀ {h} → ∅ₖ ⊩ ∅ ⊢[ [] ] h ∷ U⇒U ! pure
          → ∅ₖ ⊩ ∅ ⊢[ [] ] mapEffᶜ T₂ Unit Unit act h ∷ P ⇒[ mk-kind Many act ] P ! pure
    ⊢map₀ dh = ⊢let {q = Many} dh
      (⊢lam ω≤ω (⊢pair (⊢app (⊢var (suc zero)) (⊢fst (⊢var zero))) (⊢app (⊢var (suc zero)) (⊢snd (⊢var zero)))))

    ⊢map₁ : ∀ {X h} → ∅ₖ ⊩ ∅ ▸ X ⊢[ Zero ∷ [] ] h ∷ U⇒U ! pure
          → ∅ₖ ⊩ ∅ ▸ X ⊢[ Zero ∷ [] ] mapEffᶜ T₂ Unit Unit act h ∷ P ⇒[ mk-kind Many act ] P ! pure
    ⊢map₁ dh = ⊢let {Ψ₁ = Zero ∷ []} {Ψ₂ = Zero ∷ []} {q = Many} dh
      (⊢lam ω≤ω (⊢pair (⊢app (⊢var (suc zero)) (⊢fst (⊢var zero))) (⊢app (⊢var (suc zero)) (⊢snd (⊢var zero)))))

    ⊢∘ : ∀ {A B C : Ty 0} {f g : Tm S₀ 0 0}
       → ∅ₖ ⊩ ∅ ⊢[ [] ] f ∷ B ⇒[ mk-kind Many act ] C ! pure
       → ∅ₖ ⊩ ∅ ▸ (B ⇒[ mk-kind Many act ] C) ⊢[ Zero ∷ [] ] wk g ∷ A ⇒[ mk-kind Many act ] B ! pure
       → ∅ₖ ⊩ ∅ ⊢[ [] ] composeᶜ A act f g ∷ A ⇒[ mk-kind Many act ] C ! pure
    ⊢∘ df dg = ⊢let {q = One} df (⊢let {q = Many} dg
                 (⊢lam ω≤ω (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))

    d d′ : ∅ₖ ⊩ ∅ ⊢[ [] ] _ ∷ P ⇒[ mk-kind Many act ] P ! pure
    d  = ⊢map₀ (⊢∘ {g = gᵗ} ⊢f ⊢g)
    d′ = ⊢∘ {g = mapEffᶜ T₂ Unit Unit act gᵗ} (⊢map₀ ⊢f) (⊢map₁ ⊢g)

    model₂ : Model Σ₂
    model₂ = record { constantᵐ = λ { (here ()) ; (there (here ())) ; (there (there ())) }
                    ; valueᵐ    = λ { (here ()) ; (there (here ())) ; (there (there ())) } }

    δ₂ : DefSem
    δ₂ = record { defs = λ () ; model = model₂ }

    -- In a world, `map (f ∘ g)` at `(tt , tt)` runs to its end calling
    -- `g, f, g, f`; `map f ∘ map g` has no run with those calls: its second
    -- call is `g`.
    differ : ¬ _≅_ Σ₂ fmt S₀ d d′
    differ p =
      case fwd Σ₂ (fromObserved Σ₂ (obs⁻ Σ₂ (p δ₂ (λ ()) (λ ()) (λ ()) tt tt) (tt , tt) (tt , tt) (tt , tt)))
               (aWorld Σ₂) [] 5 (run (rb-call (ra-go (rb-call (ra-go (rb-call (ra-go (rb-call (ra-go rb-ret)))))))))
      of λ { (_ , run (rb-call (ra-go ())) , _) }

  map-compose-any-grade : ¬ MapComposeAnyGrade Σ₂
  map-compose-any-grade law =
    differ (law {Δ = ∅ₖ} {Γ = ∅} {Ψ = []} {T = T₂} {A = Unit} {B = Unit} {C = Unit} {π = act} {π₀ = pure}
                {f = fᵗ} {g = gᵗ} d d′)

------------------------------------------------------------------------
-- 3. Naturality, at a type that is not strictly positive
------------------------------------------------------------------------

-- D371's naturality without `StrictlyPositive F` and `StrictlyPositive G`.
NaturalityAnyType : ∀ {s} → Defs s → Set₁
NaturalityAnyType {s} S = let open CoreTyping Σ₀ S in
  ∀ {m n} {Δ : KCtx m} {Γ : Ctx m n} {Ψ Ψf A B q q′ π π₀ πf f}
    (e : Fin s) (τ : TySub (Schema.arity (S !! e)) (ℕ.suc m)) {F G : Ty (ℕ.suc m)}
  → Schema.type (S !! e) ⟨ τ ⟩ ≡ F ⇒[ mk-kind q π ] G
  → Δ ⊩ Γ ⊢[ Ψf ] f ∷ A ⇒[ mk-kind q′ pure ] B ! πf
  → (d : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (F ⟨ at₀ A ⟩) π (mapᶜ G A B f) (ref e (λ i → τ i ⟨ at₀ A ⟩))
                       ∷ F ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] G ⟨ at₀ B ⟩ ! π₀)
    (d′ : Δ ⊩ Γ ⊢[ Ψ ] composeᶜ (F ⟨ at₀ A ⟩) π (ref e (λ i → τ i ⟨ at₀ B ⟩)) (mapᶜ F A B f)
                       ∷ F ⟨ at₀ A ⟩ ⇒[ mk-kind Many π ] G ⟨ at₀ B ⟩ ! π₀)
  → _≅ₚ_ Σ₀ fmt S d d′

-- The counterexample: `twice : ∀a. (a ⇒ a) ⇒ (a ⇒ a)`, `g ↦ g ∘ g`. `a`
-- occurs in an arrow's domain, where `map` keeps the domain as it is, so
-- `map f` types only for `f : A → A`, and maps a function by
-- post-composing: `map f g = f ∘ g`. At `A = Bool`, `f = not`, `g = id`:
-- `map f (twice g) = not` but `twice (map f g) = not ∘ not = id`.
private
  arr : ∀ {m} → Ty m → Ty m → Ty m
  arr A B = A ⇒[ mk-kind Many pure ] B

  twiceSc : Schema
  twiceSc = schema 1 (λ _ → any) (arr (arr (var zero) (var zero)) (arr (var zero) (var zero)))

  S₁ : Defs 1
  S₁ = [] ▷ twiceSc

  twice : Tm S₀ 1 0
  twice = lam (arr (var zero) (var zero)) Many pure
            (lam (var zero) Many pure (app (var (suc zero)) (app (var (suc zero)) (var zero))))

  module TwiceBody where
    open CoreTyping Σ₀ S₀
    ⊢twice : Schema.kinds twiceSc ⊩ ∅ ⊢[ [] ] twice ∷ Schema.type twiceSc ! pure
    ⊢twice = ⊢lam ω≤ω (⊢lam ω≤ω (⊢app (⊢var (suc zero)) (⊢app (⊢var (suc zero)) (⊢var zero))))

  tl : Tele Σ₀ S₁
  tl = def [] twiceSc twice TwiceBody.⊢twice

  δ₁ : Meaning.DefSem Σ₀ fmt S₁
  δ₁ = teleSem Σ₀ fmt model₀ tl

  -- `twice` is parametric: `g` related to `g′` gives `g ∘ g` related to
  -- `g′ ∘ g′` (what `param-tele` proves of every program, here directly).
  param-twice : ParamDefs Σ₀ fmt S₁ δ₁
  param-twice zero τ τ′ r r′ ρ g g′ rg =
    ret (λ x x′ rx → ret (obs⁻ Σ₀ (rg _ _ (obs⁻ Σ₀ (rg x x′ rx)))))
    where ret : ∀ {X Y : Set} {R : X → Y → Set} {x y} → R x y → RelM Σ₀ pure R x y
          ret r = toObserved Σ₀ (returnRel Σ₀ r)

module Natural where
  open CoreTyping Σ₀ S₁

  private
    BB : Ty 0
    BB = arr Bool Bool

    notᵗ : ∀ {n} → Tm S₁ 0 n
    notᵗ = lam Bool Many pure (case Many Many (var zero) (inr Unit unit) (inl Unit unit))

    -- a `case` arm that ignores its variable, at the arm's usage `Many`
    arm : ∀ {n} {Γ : Ctx 0 n} {X A t} → ∅ₖ ⊩ Γ ▸ X ⊢[ zeroUsage ] t ∷ A ! pure → ∅ₖ ⊩ Γ ▸ X ⊢[ Many ∷ zeroUsage ] t ∷ A ! pure
    arm = ⊢sub-use (0≤q ⊑∷ zero⊑)

    ⊢not₀ : ∅ₖ ⊩ ∅ ⊢[ [] ] notᵗ ∷ BB ! pure
    ⊢not₀ = ⊢lam 1≤ω (⊢case (⊢var zero) (arm (⊢inr ⊢unit)) (arm (⊢inl ⊢unit)))

    ⊢not₁ : ∀ {X} → ∅ₖ ⊩ ∅ ▸ X ⊢[ Zero ∷ [] ] notᵗ ∷ BB ! pure
    ⊢not₁ = ⊢lam 1≤ω (⊢case (⊢var zero) (arm (⊢inr ⊢unit)) (arm (⊢inl ⊢unit)))

    -- map (a ⇒ a) not = g ↦ not ∘ g
    ⊢map₀ : ∅ₖ ⊩ ∅ ⊢[ [] ] mapᶜ (arr (var zero) (var zero)) Bool Bool notᵗ ∷ arr BB BB ! pure
    ⊢map₀ = ⊢let {q = Many} ⊢not₀ (⊢sub-use (1≤ω ⊑∷ [])
              (⊢lam ω≤ω (⊢lam ω≤ω (⊢let {q = Many} (⊢app (⊢var (suc zero)) (⊢var zero))
                                                     (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero))))))

    ⊢map₁ : ∀ {X} → ∅ₖ ⊩ ∅ ▸ X ⊢[ Zero ∷ [] ] mapᶜ (arr (var zero) (var zero)) Bool Bool notᵗ ∷ arr BB BB ! pure
    ⊢map₁ = ⊢let {q = Many} ⊢not₁ (⊢sub-use (1≤ω ⊑∷ 0≤q ⊑∷ [])
              (⊢lam ω≤ω (⊢lam ω≤ω (⊢let {q = Many} (⊢app (⊢var (suc zero)) (⊢var zero))
                                                     (⊢app (⊢var (suc (suc (suc zero)))) (⊢var zero))))))

    ⊢twice₀ : ∅ₖ ⊩ ∅ ⊢[ [] ] ref zero (λ _ → Bool) ∷ arr BB BB ! pure
    ⊢twice₀ = ⊢ref zero (λ _ → Bool) (λ _ ())

    ⊢twice₁ : ∀ {X} → ∅ₖ ⊩ ∅ ▸ X ⊢[ Zero ∷ [] ] ref zero (λ _ → Bool) ∷ arr BB BB ! pure
    ⊢twice₁ = ⊢ref zero (λ _ → Bool) (λ _ ())

    ⊢∘ : ∀ {f g : Tm S₁ 0 0}
       → ∅ₖ ⊩ ∅ ⊢[ [] ] f ∷ arr BB BB ! pure
       → ∅ₖ ⊩ ∅ ▸ arr BB BB ⊢[ Zero ∷ [] ] wk g ∷ arr BB BB ! pure
       → ∅ₖ ⊩ ∅ ⊢[ [] ] composeᶜ BB pure f g ∷ arr BB BB ! pure
    ⊢∘ df dg = ⊢let {q = One} df (⊢let {q = Many} dg
                 (⊢lam ω≤ω (⊢app (⊢var (suc (suc zero))) (⊢app (⊢var (suc zero)) (⊢var zero)))))

    -- map f ∘ twice, and twice ∘ map f
    d d′ : ∅ₖ ⊩ ∅ ⊢[ [] ] _ ∷ arr BB BB ! pure
    d  = ⊢∘ ⊢map₀ ⊢twice₁
    d′ = ⊢∘ ⊢twice₀ ⊢map₁

    -- at `id` and `true`: `not (id (id true)) = false`, `not (not true) = true`
    differ : ¬ _≅ₚ_ Σ₀ fmt S₁ d d′
    differ p = false≠true (obs⁻ Σ₀ (obs⁻ Σ₀ (obs⁻ Σ₀ (p δ₁ param-twice (λ ()) (λ ()) tt tt)
                                            (λ x → x) (λ x → x) (λ a a′ r → toObserved Σ₀ (returnRel Σ₀ r)))
                                  (inj₁ tt) (inj₁ tt) tt))

  naturality-any-type : ¬ NaturalityAnyType S₁
  naturality-any-type law = differ (law zero (λ _ → var zero) refl ⊢not₀ d d′)
