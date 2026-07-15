-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CataErased
--
-- Plan 0.52 M2: the FUNCTOR-TRANSPORT lemma isolating the erasure round-trip
-- for the `Cata` recursion scheme. After M2 the IR's `Cata` folds the ERASED
-- functor `⌈eraseF F⌉F` at carrier `⟦⌊A⌋⟧ᴰᴵ` (`evalᴰ (Cata …)` via `wf-⌈⌉`),
-- while the surface/meaning fold runs over `F` at `⟦A⟧ᴰ`. This module proves
-- they coincide once bridged by `liftFn` (grade-blind `cohᴰ` transport) and the
-- SET-level functor round-trip `tF-coh : translateF ⌈eraseF F⌉F ≡ translateF F`.
--
-- The single export `evalᴰ-Cata-erased` lets the relational fold congruences
-- (`CataBridge.cata-bridge`, `CataFold.cata-fold-eq`) stay at the SAME functor
-- `F` and SAME carrier `⟦A⟧ᴰ` — their original proofs are reused unchanged,
-- with this lemma discharging the erasure round-trip up front.
--
-- Own module (minimal, distinct-suffix `⟦_⟧` imports) mirroring `CataFold`/
-- `CataRel`/`CataBridge`, to keep the transport proof clear of `⟦_⟧`-mixfix soup.
------------------------------------------------------------------------

module Once.Adequacy.CataErased where

open import Data.Nat using (ℕ)
open import Data.List using (List; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

open import Once.Semantics.Functor using (SFunctor; μS; cataS; ⟦_⟧SF)
open import Once.Denotation.TraceMonad using (T; projTrace; valueT)
open import Once.IRTy using (IRTy; IRFunctor; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⟦_⟧TI; ⌈⟧TI-commute)
open import Once.Denotation.DenotTrace
  using (⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; evalᴰ; cata-ev-algᴰ)
open import Once.Denotation.Meaning using (cata-ev-algᴰ-D)
open import Once.Semantics.Machine using (⟦_⟧F)
open import Once.Denotation.Trace using (SigOpEvent)
import Once.IR as IR

------------------------------------------------------------------------
-- Generic transport helpers (both by matching the equation to `refl`).
------------------------------------------------------------------------

-- Applying a `subst`-transported computation transports its VALUE half only.
subst-T-apply : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) (n : ℕ)
  → subst T eq h n ≡ (proj₁ (h n) , subst (λ Z → Z) eq (proj₂ (h n)))
subst-T-apply refl h n = refl

-- A `cataS` fold over `G₂` equals the fold over an equal functor `G₁`, with the
-- algebra pre-composed by the (inverse) functor transport and the seed transported.
cataS-subst-functor : ∀ {G₁ G₂ : SFunctor} {A : Set}
    (eq : G₂ ≡ G₁) (alg : ⟦ G₂ ⟧SF A → A) (x : μS G₂)
  → cataS {G₂} alg x
    ≡ cataS {G₁} (λ y → alg (subst (λ G → ⟦ G ⟧SF A) (sym eq) y)) (subst μS eq x)
cataS-subst-functor refl alg x = refl

-- Naturality of `evalᴰ` under a DOMAIN transport: substituting the source
-- object of an IR morphism is the same as back-transporting its argument.
evalᴰ-subst-dom : ∀ {o₁ o₂ : IRTy} {B : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR o₁ B) (z : ⟦ o₂ ⟧ᴰᴵ)
  → evalᴰ (subst (λ o → IR.IR o B) eq m) z ≡ evalᴰ m (subst ⟦_⟧ᴰᴵ (sym eq) z)
evalᴰ-subst-dom refl m z = refl

-- The IR-carrier cata trace-algebra is DEFINITIONALLY the Type-carrier one
-- (`cata-ev-algᴰ-D`) over the embedded functor `⌈F⌉F`, fed the algebra
-- `evalᴰ alg` pre-composed with the `⌈⟧TI-commute` re-embedding. Collapses the
-- IR-vs-meaning fold asymmetry so both sides become uniform `cata-sem` folds.
cata-ev-algᴰ-is-D : ∀ {F : IRFunctor} {C : IRTy} (n : ℕ)
    (alg : IR.IR (⟦ F ⟧TI C) C)
    (fc : ⟦ ⌈ F ⌉F ⟧F (List SigOpEvent × ⟦ C ⟧ᴰᴵ))
  → cata-ev-algᴰ {F} {C} n alg fc
    ≡ cata-ev-algᴰ-D {⌈ F ⌉F} {⌈ C ⌉} n
        (λ z → evalᴰ alg (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F C)) z)) fc
cata-ev-algᴰ-is-D n alg fc = refl
