------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L3.0 — THE WORLD CATEGORY
--
-- Linear NbE (plan §10, derivation recorded 2026-07-14) evaluates into
-- a Day-convolution model whose WORLDS are resource contexts and whose
-- world maps are structural. The summit's lesson, applied at the
-- ground floor: keep the worlds NORMALIZED from the start — a world is
-- a LIST of `CTy` resources (no ⊗/I world-noise to quotient later),
-- and a world map is an insertion-sort permutation.
--
-- This module is the permutation algebra of stage 3A (`NbEPMonA`),
-- re-founded over lists with ARBITRARY `CTy` elements (the old `Lf`
-- leaf restriction dropped — the proofs never used it):
--
--   * `Ctx`, `_++_`             — worlds and their combination (Day ⊗)
--   * `Ins`/`Perm`/`pid`        — world maps
--   * `ins-swap`/`push`/`_⊙P_`  — the diamond, factorization,
--                                  composition (verbatim recipes)
--   * `padˡ`/`padʳ`             — functoriality of `_++_` in each slot
--   * `insEnd`/`swap++`         — the block transposition: the Day
--     tensor is symmetric ON WORLDS (the `bswap` recipe, re-run)
--   * `⊙P` with `pid` and the `++`-associator being DEFINITIONAL
--     (lists!) — the world category needs no coherence theorems at
--     all. That is why worlds are lists.
--
-- Next (L3.1): `Val` by type recursion over these worlds, `vmap`,
-- eval/reflect/reify for the right-pure fragment.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonT where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; cong )
open import poc.OCP0009.NbEPMonL
  using ( CTy )

------------------------------------------------------------------------
-- Worlds: lists of resources. Combination is concatenation — the Day
-- tensor on worlds, associative and unital DEFINITIONALLY.
------------------------------------------------------------------------

infixr 5 _∷_
infixr 5 _++_

data Ctx : Set where
  ε   : Ctx
  _∷_ : CTy → Ctx → Ctx

_++_ : Ctx → Ctx → Ctx
ε        ++ Δ = Δ
(A ∷ Γ)  ++ Δ = A ∷ (Γ ++ Δ)

++-idʳ : ∀ Γ → (Γ ++ ε) ≡ Γ
++-idʳ ε       = refl
++-idʳ (A ∷ Γ) with Γ ++ ε | ++-idʳ Γ
... | _ | refl = refl

++-assoc : ∀ Γ Δ Θ → ((Γ ++ Δ) ++ Θ) ≡ (Γ ++ (Δ ++ Θ))
++-assoc ε       Δ Θ = refl
++-assoc (A ∷ Γ) Δ Θ with (Γ ++ Δ) ++ Θ | ++-assoc Γ Δ Θ
... | _ | refl = refl

------------------------------------------------------------------------
-- World maps: insertion-sort permutations (stage-2 shape, generalized).
------------------------------------------------------------------------

data Ins (x : CTy) : Ctx → Ctx → Set where
  here  : ∀ {xs} → Ins x xs (x ∷ xs)
  there : ∀ {y xs ys} → Ins x xs ys → Ins x (y ∷ xs) (y ∷ ys)

data Perm : Ctx → Ctx → Set where
  pnil  : Perm ε ε
  pcons : ∀ {x xs ys zs} → Perm xs ys → Ins x ys zs → Perm (x ∷ xs) zs

pid : ∀ Γ → Perm Γ Γ
pid ε       = pnil
pid (A ∷ Γ) = pcons (pid Γ) here

------------------------------------------------------------------------
-- The algebra: diamond, factorization, composition — the 3A recipes,
-- element-type-generic.
------------------------------------------------------------------------

ins-swap : ∀ {x y w₂ w₁ w} → Ins x w₂ w₁ → Ins y w₁ w →
           Σ Ctx (λ w₃ → Σ (Ins y w₂ w₃) (λ _ → Ins x w₃ w))
ins-swap here       here       = _ , (here , there here)
ins-swap here       (there j₀) = _ , (j₀ , here)
ins-swap (there i₀) here       = _ , (here , there (there i₀))
ins-swap (there i₀) (there j₀) with ins-swap i₀ j₀
... | _ , (jy , jx) = _ , (there jy , there jx)

push : ∀ {x ys zs ws} → Ins x ys zs → Perm zs ws →
       Σ Ctx (λ ws' → Σ (Perm ys ws') (λ _ → Ins x ws' ws))
push here      (pcons q j) = _ , (q , j)
push (there i) (pcons q j) with push i q
... | _ , (q' , j') with ins-swap j' j
...   | _ , (jy , jx) = _ , (pcons q' jy , jx)

infixr 9 _⊙P_
_⊙P_ : ∀ {xs ys zs} → Perm xs ys → Perm ys zs → Perm xs zs
pnil      ⊙P q = q
pcons p i ⊙P q with push i q
... | _ , (q' , j) = pcons (p ⊙P q') j

------------------------------------------------------------------------
-- Functoriality of the Day tensor in each slot.
------------------------------------------------------------------------

-- Insertion, shifted past a prefix.
insˡ : ∀ Θ {x xs ys} → Ins x xs ys → Ins x (Θ ++ xs) (Θ ++ ys)
insˡ ε       i = i
insˡ (A ∷ Θ) i = there (insˡ Θ i)

-- Permuting the right factor.
padˡ : ∀ Θ {xs ys} → Perm xs ys → Perm (Θ ++ xs) (Θ ++ ys)
padˡ ε       q = q
padˡ (A ∷ Θ) q = pcons (padˡ Θ q) here

-- Insertion, shifted past a suffix.
insʳ : ∀ Θ {x xs ys} → Ins x xs ys → Ins x (xs ++ Θ) (ys ++ Θ)
insʳ Θ here      = here
insʳ Θ (there j) = there (insʳ Θ j)

-- Permuting the left factor.
padʳ : ∀ {xs ys} Θ → Perm xs ys → Perm (xs ++ Θ) (ys ++ Θ)
padʳ Θ pnil        = pid Θ
padʳ Θ (pcons p i) = pcons (padʳ Θ p) (insʳ Θ i)

-- Both at once.
pad² : ∀ {xs ys zs ws} → Perm xs ys → Perm zs ws →
       Perm (xs ++ zs) (ys ++ ws)
pad² {xs} {ys} {zs} {ws} p q = padʳ zs p ⊙P padˡ ys q

------------------------------------------------------------------------
-- Symmetry of the Day tensor on worlds: the `bswap` recipe, re-run.
------------------------------------------------------------------------

-- Insert at the end of a prefix (carry x past all of Θ).
insEnd : ∀ Θ {x xs} → Ins x (Θ ++ xs) (Θ ++ (x ∷ xs))
insEnd ε       = here
insEnd (A ∷ Θ) = there (insEnd Θ)

-- Γ ++ Δ ⇒ Δ ++ Γ, one head-carry at a time.
swap++ : ∀ Γ Δ → Perm (Γ ++ Δ) (Δ ++ (Γ ++ ε))
swap++ ε       Δ with Δ ++ ε | ++-idʳ Δ
... | _ | refl = pid Δ
swap++ (A ∷ Γ) Δ = pcons (swap++ Γ Δ) (insEnd Δ)

-- The clean-type corollary (the ε-tail transported away).
private
  psubst : ∀ {Γ Δ Δ'} → Δ ≡ Δ' → Perm Γ Δ → Perm Γ Δ'
  psubst refl p = p

bswapW : ∀ Γ Δ → Perm (Γ ++ Δ) (Δ ++ Γ)
bswapW Γ Δ = psubst (cong (Δ ++_) (++-idʳ Γ)) (swap++ Γ Δ)

------------------------------------------------------------------------
-- Demos: composition and symmetry compute.
------------------------------------------------------------------------

private
  open import poc.OCP0009.NbEPMonL using ( ι₁; ι₂; I )

  Γ₀ Δ₀ : Ctx
  Γ₀ = ι₁ ∷ ι₂ ∷ ε
  Δ₀ = I ∷ ε

  -- Round-trip of the world symmetry is the identity permutation.
  _ : (bswapW Γ₀ Δ₀ ⊙P bswapW Δ₀ Γ₀) ≡ pid (Γ₀ ++ Δ₀)
  _ = refl

  -- pid is a unit for ⊙P on this world (definitional computation).
  _ : (pid (Γ₀ ++ Δ₀) ⊙P bswapW Γ₀ Δ₀) ≡ bswapW Γ₀ Δ₀
  _ = refl
