------------------------------------------------------------------------
-- OCP-0009 · SMC coherence, STAGE 3A — the PERMUTATION ALGEBRA (data)
--
-- The key lemma (`f ≈m topn ∘ permM (pOf f) ∘ ntop`, stage 3E) needs `pOf`
-- to be built compositionally — so `Perm` needs an algebra mirroring the
-- morphism formers. This module is that algebra at the DATA level; the
-- `≈m`-compatibility of each operation (that its realization is provably
-- equal to the corresponding composite) is stage 3C.
--
--   * `ins-swap` — the INSERTION DIAMOND: two consecutive insertions
--     commute (insert `y` first, then `x`). Four cases, fully structural.
--   * `push`    — the FACTORIZATION lemma: an insertion followed by a
--     permutation factors as a permutation followed by an insertion —
--     `Ins x ys zs → Perm zs ws → Σ ws' (Perm ys ws' × Ins x ws' ws)`.
--     The `here` case is literally pattern-matching `pcons` apart; the
--     `there` case recurses and closes with the diamond.
--   * `_⊙P_`    — COMPOSITION of permutations, via `push` (terminating on
--     the first argument alone — `push`'s output permutation is fed to the
--     structurally smaller tail).
--   * `padP`    — ACCUMULATOR PADDING: a permutation of the accumulator
--     lifts through `norm B` (fixing `B`'s leaves) — the piece that lets
--     the `_⊗m_` case of the key lemma avoid list-append transport
--     entirely (the Beylin–Dybjer accumulator, once more).
--   * `insAcc`  — insertion into the accumulator, lifted through `norm B`
--     (inserting "at the end", past all of `B`'s leaves).
--   * `bswap`   — the BLOCK TRANSPOSITION `norm A (norm B R) ⇝
--     norm B (norm A R)`: what `σ` denotes on normal forms; built from
--     `padP`/`insAcc`/`⊙P` by recursion on `A`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonA where

open import normalizer.Syntax.Types
  using ( Σ; _,_ )
open import poc.OCP0009.NbEPMon
  using ( MTy; ι₁; ι₂; I; _⊗_ )
open import poc.OCP0009.NbEPMonN
  using ( norm; list )
open import poc.OCP0009.NbEPMonP
  using ( Lf; lf₁; lf₂; IsL; lnil; lcons; isL-norm; isL-list
        ; Ins; here; there; Perm; pnil; pcons; pid )

------------------------------------------------------------------------
-- The insertion diamond: `w₂ —x→ w₁ —y→ w` commutes to `w₂ —y→ w₃ —x→ w`.
------------------------------------------------------------------------

ins-swap : ∀ {x y w₂ w₁ w} → Ins x w₂ w₁ → Ins y w₁ w →
           Σ MTy (λ w₃ → Σ (Ins y w₂ w₃) (λ _ → Ins x w₃ w))
ins-swap here       here       = _ , (here , there here)
ins-swap here       (there j₀) = _ , (j₀ , here)
ins-swap (there i₀) here       = _ , (here , there (there i₀))
ins-swap (there i₀) (there j₀) with ins-swap i₀ j₀
... | _ , (jy , jx) = _ , (there jy , there jx)

------------------------------------------------------------------------
-- Factorization: insertion-then-permutation = permutation-then-insertion.
------------------------------------------------------------------------

push : ∀ {x ys zs ws} → Ins x ys zs → Perm zs ws →
       Σ MTy (λ ws' → Σ (Perm ys ws') (λ _ → Ins x ws' ws))
push here      (pcons q j) = _ , (q , j)
push (there i) (pcons q j) with push i q
... | _ , (q' , j') with ins-swap j' j
...   | _ , (jy , jx) = _ , (pcons q' jy , jx)

------------------------------------------------------------------------
-- Composition (terminating on the first argument).
------------------------------------------------------------------------

infixr 9 _⊙P_
_⊙P_ : ∀ {xs ys zs} → Perm xs ys → Perm ys zs → Perm xs zs
pnil      ⊙P q = q
pcons p i ⊙P q with push i q
... | _ , (q' , j) = pcons (p ⊙P q') j

------------------------------------------------------------------------
-- Padding: accumulator permutations and insertions lift through `norm B`.
------------------------------------------------------------------------

padP : ∀ B {S S'} → Perm S S' → Perm (norm B S) (norm B S')
padP ι₁      q = pcons q here
padP ι₂      q = pcons q here
padP I       q = q
padP (A ⊗ B) q = padP A (padP B q)

insAcc : ∀ B {x S S'} → Ins x S S' → Ins x (norm B S) (norm B S')
insAcc ι₁      i = there i
insAcc ι₂      i = there i
insAcc I       i = i
insAcc (A ⊗ B) i = insAcc A (insAcc B i)

------------------------------------------------------------------------
-- The block transposition: what `σ : A ⊗ B → B ⊗ A` denotes on normal
-- forms. Recursion on `A`: each of `A`'s leaves is carried past `B`'s
-- leaves by an end-insertion; tensors decompose via padding + composition.
------------------------------------------------------------------------

bswap : ∀ A B {R} → IsL R → Perm (norm A (norm B R)) (norm B (norm A R))
bswap ι₁        B r = pcons (pid (isL-norm B r)) (insAcc B here)
bswap ι₂        B r = pcons (pid (isL-norm B r)) (insAcc B here)
bswap I         B r = pid (isL-norm B r)
bswap (A₁ ⊗ A₂) B r = padP A₁ (bswap A₂ B r) ⊙P bswap A₁ B (isL-norm A₂ r)
