-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.CataFold
--
-- Plan 0.58: the cata denotational bridge FACTORED as a lemma that takes
-- the ALGEBRA's faithfulness as a hypothesis (`⟦algE⟧ˢ tt ≡ returnT (evalᴰ
-- m-alg)`). No reflexivity, no carrier constraint: the two `cata-ev-alg`s
-- coincide pointwise once `⟦algE⟧ˢ tt` is rewritten (monad-left-id collapses
-- the `>>=T`), `extensionality` lifts that to the algebra FUNCTION equality,
-- and `cong` closes the shared `sem-cata` fold.
--
-- Own module (minimal imports) to escape the `⟦_⟧`-mixfix ambiguity of
-- `RealizeAgrees`. `agree-cata-denotes` there supplies the faithfulness via
-- `extract-morph-eff` and applies `cata-fold-eq`.
------------------------------------------------------------------------

module Once.Adequacy.CataFold where

open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type; Purity; mk-kind; Many; _⇒[_]_)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine using (sem-cata)
open import Once.Denotation.TraceMonad using (T; returnT)
open import Once.Denotation.DenotTrace using (evalᴰ; inject; cata-ev-algᴰ)
open import Once.Surface.Syntax using (Expr; ∅; Ctx; zeroUsage; ⟦_⟧ᶜ)
import Once.Surface.Syntax as Srf
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Postulates using (extensionality)
import Once.IR as IR
import Once.Denotation.SourceDenote as SD

-- The cata denotational bridge, GIVEN the algebra's faithfulness. `forget {μF}`
-- is the identity, so both sides fold the same `x`; the algebras
-- `cata-ev-algˢ n (⟦algE⟧ˢ tt)` and `cata-ev-algᴰ n m-alg` coincide pointwise
-- once `⟦algE⟧ˢ tt` is rewritten to `returnT (evalᴰ m-alg)` (monad-left-id
-- collapses the `>>=T`); `extensionality` + `cong` close each fold.
cata-fold-eq : ∀ {n} {Γ : Ctx n} {F : Functor} {A : Type} {π : Purity}
    (wfF : WellFormedF F)
    (algE : Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
    (m-alg : IR.IR (⟦ F ⟧T A) A)
  → SD.⟦ algE ⟧ˢ tt ≡ returnT (evalᴰ m-alg)
  → ∀ (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ Srf.cata {Γ = Γ} wfF algE ⟧ˢ dγ k
      ≡ SD.⟦ Srf.lift-morphism {Γ = Γ} {π = π} (IR.Cata wfF m-alg) ⟧ˢ dγ k
cata-fold-eq {F = F} {A = A} wfF algE m-alg feq dγ k =
  cong ([] ,_) (extensionality λ x → extensionality λ n →
    cong (λ alg → let r = sem-cata wfF alg x in (proj₁ r , proj₂ r))
      (extensionality λ fc → alg-eq n fc))
  where
    alg-eq : ∀ n fc
           → SD.cata-ev-algˢ {F} {A} n (SD.⟦ algE ⟧ˢ tt) fc
             ≡ cata-ev-algᴰ {F} {A} n m-alg fc
    alg-eq n fc rewrite feq = refl
