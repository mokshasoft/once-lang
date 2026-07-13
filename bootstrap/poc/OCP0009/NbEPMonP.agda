------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 2 — CANONICAL REALIZATIONS
--
-- Between list types (stage 1's normal forms), a structural morphism is
-- determined by a PERMUTATION of leaves. This stage gives permutations a
-- first-order syntax and realizes them as morphisms:
--
--   * `Ins x xs ys` — inserting leaf `x` into list `xs` yields `ys`;
--     `Perm xs ys` — insertion-sort–shaped permutations between lists
--     (every permutation = insert the head somewhere in a permuted tail).
--   * `insM`/`permM` — the REALIZATIONS: `Ins`/`Perm` as `STm` morphisms,
--     built from `σ` lifted through tensors (`swapHead` = the conjugated
--     transposition `αr ∘ (σ ⊗ id) ∘ αl`).
--   * `applyI`/`applyP` — the intended ACTIONS as leaf pullbacks, defined
--     independently of the syntax.
--   * THE AGREEMENT THEOREM: `wire (permM p) ≡ applyP p`, pointwise — the
--     realization means what the permutation says. This is the hinge stage
--     3 turns on: two realizations with equal wirings will be forced to be
--     the SAME `Perm` (representation uniqueness), hence the same
--     canonical morphism.
--
-- Also here: `IsL` (list-shape evidence) with `isL-norm : IsL (list A)` —
-- stage 1's normal forms are certified list-shaped, so stage 3 may speak
-- of "the permutation of `f`" for every `f` conjugated by `ntop`/`topn`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonP where

open import normalizer.Syntax.Types
  using ( _≡_; refl; trans; cong )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonC
  using ( STm; idm; _∘m_; _⊗m_; αr; αl; σm
        ; Leaf; ℓ₁; ℓ₂; goL; goR; wire )
open import poc.OCP0009.NbEPMonN
  using ( norm; list )

------------------------------------------------------------------------
-- Leaves and list-shape evidence. Stage 1's normal forms are list-shaped.
------------------------------------------------------------------------

data Lf : MTy → Set where
  lf₁ : Lf ι₁
  lf₂ : Lf ι₂

data IsL : MTy → Set where
  lnil  : IsL I
  lcons : ∀ {x xs} → Lf x → IsL xs → IsL (x ⊗ xs)

isL-norm : ∀ A {R} → IsL R → IsL (norm A R)
isL-norm ι₁      r = lcons lf₁ r
isL-norm ι₂      r = lcons lf₂ r
isL-norm I       r = r
isL-norm (A ⊗ B) r = isL-norm A (isL-norm B r)

isL-list : ∀ A → IsL (list A)
isL-list A = isL-norm A lnil

------------------------------------------------------------------------
-- Insertion-based permutations between list types.
------------------------------------------------------------------------

data Ins (x : MTy) : MTy → MTy → Set where
  here  : ∀ {xs} → Ins x xs (x ⊗ xs)
  there : ∀ {y xs ys} → Ins x xs ys → Ins x (y ⊗ xs) (y ⊗ ys)

data Perm : MTy → MTy → Set where
  pnil  : Perm I I
  pcons : ∀ {x xs ys zs} → Perm xs ys → Ins x ys zs → Perm (x ⊗ xs) zs

-- The identity permutation, for every list shape.
pid : ∀ {xs} → IsL xs → Perm xs xs
pid lnil        = pnil
pid (lcons _ r) = pcons (pid r) here

------------------------------------------------------------------------
-- Realization: permutation syntax → structural morphisms. The generator
-- is the conjugated head transposition.
------------------------------------------------------------------------

-- x ⊗ (y ⊗ xs) → y ⊗ (x ⊗ xs)
swapHead : ∀ {x y xs} → STm (x ⊗ (y ⊗ xs)) (y ⊗ (x ⊗ xs))
swapHead = αr ∘m ((σm ⊗m idm) ∘m αl)

insM : ∀ {x xs ys} → Ins x xs ys → STm (x ⊗ xs) ys
insM here      = idm
insM (there i) = (idm ⊗m insM i) ∘m swapHead

permM : ∀ {xs ys} → Perm xs ys → STm xs ys
permM pnil        = idm
permM (pcons p i) = insM i ∘m (idm ⊗m permM p)

------------------------------------------------------------------------
-- The intended action, as a leaf pullback — independent of the syntax.
------------------------------------------------------------------------

applyI : ∀ {x xs ys} → Ins x xs ys → Leaf ys → Leaf (x ⊗ xs)
applyI here      l       = l
applyI (there i) (goL l) = goR (goL l)
applyI (there i) (goR l) with applyI i l
... | goL lx  = goL lx
... | goR lxs = goR (goR lxs)

applyP : ∀ {xs ys} → Perm xs ys → Leaf ys → Leaf xs
applyP pnil        ()
applyP (pcons p i) l with applyI i l
... | goL lx  = goL lx
... | goR lys = goR (applyP p lys)

------------------------------------------------------------------------
-- THE AGREEMENT THEOREM — the realization means what the permutation
-- says: the wiring of `permM p` is exactly `applyP p`.
------------------------------------------------------------------------

wire-insM : ∀ {x xs ys} (i : Ins x xs ys) (l : Leaf ys) →
            wire (insM i) l ≡ applyI i l
wire-insM here      l       = refl
wire-insM (there i) (goL l) = refl
wire-insM (there i) (goR l) with applyI i l | wire-insM i l
... | goL lx  | eq = cong (λ z → wire swapHead (goR z)) eq
... | goR lxs | eq = cong (λ z → wire swapHead (goR z)) eq

wire-permM : ∀ {xs ys} (p : Perm xs ys) (l : Leaf ys) →
             wire (permM p) l ≡ applyP p l
wire-permM pnil        ()
wire-permM (pcons p i) l with applyI i l | wire-insM i l
... | goL lx  | eq = cong (wire (idm ⊗m permM p)) eq
... | goR lys | eq =
  trans (cong (wire (idm ⊗m permM p)) eq)
        (cong goR (wire-permM p lys))

------------------------------------------------------------------------
-- Demo — the 2-element swap, as a `Perm`, realized and computing.
------------------------------------------------------------------------

swapP : Perm (ι₁ ⊗ (ι₂ ⊗ I)) (ι₂ ⊗ (ι₁ ⊗ I))
swapP = pcons (pcons pnil here) (there here)

-- The realized morphism's wiring: the ι₂ output leaf comes from the
-- second input slot, the ι₁ output leaf from the first — a genuine swap.
_ : wire (permM swapP) (goL ℓ₂) ≡ goR (goL ℓ₂)
_ = refl

_ : wire (permM swapP) (goR (goL ℓ₁)) ≡ goL ℓ₁
_ = refl
