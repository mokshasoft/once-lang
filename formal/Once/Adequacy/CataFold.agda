-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.CataFold (fmt : FloatFormat) where

open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Once.IRTy using (⌊_⌋; eraseF; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋)

open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type; Purity; mk-kind; Many; _⇒[_]_)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Semantics.Machine using (sem-cata)
open import Once.Denotation.TraceMonad using (T; returnT)
open import Once.Denotation.DenotTrace using (evalᴰ; inject; cata-ev-algᴰ)
open import Once.Surface.Syntax using (Expr; ∅; Ctx; zeroUsage; ⟦_⟧ᶜ)
import Once.Surface.Syntax as Srf
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ)
open import Once.Postulates using (extensionality)
-- `CataErased` is parameterised by the format (D113); apply it to ours.
open import Once.Adequacy.CataErased fmt using (evalᴰ-Cata-erased)
import Once.IR as IR
import Once.Denotation.SourceDenote as SD

-- The cata denotational bridge, GIVEN the algebra's faithfulness `⟦algE⟧ˢ tt ≡
-- liftD m-alg`. The surface fold's `cata-ev-algˢ n (liftD m-alg)` monad-collapses
-- (`returnT g >>=T f = f g`) to `cata-ev-algᴰ-D n (liftFn m-alg)`, i.e. exactly
-- `cata-sem wfF (liftFn m-alg)`; the erased `Cata` bridges to the same via the
-- shared `evalᴰ-Cata-erased` (Plan 0.52 M2).
cata-fold-eq : ∀ {n} {Γ : Ctx n} {F : Functor} {A : Type} {π : Purity}
    (wfF : WellFormedF F)
    (algE : Expr ∅ zeroUsage (⟦ F ⟧T A ⇒[ mk-kind Many π ] A))
    (m-alg : IR.IR ⌊ ⟦ F ⟧T A ⌋ ⌊ A ⌋)
  → SD.⟦ algE ⟧ˢ fmt tt ≡ SD.liftD fmt m-alg
  → ∀ (dγ : ⟦ ⟦ Γ ⟧ᶜ ⟧ᴰ) (k : ℕ)
  → SD.⟦ Srf.cata {Γ = Γ} wfF algE ⟧ˢ fmt dγ k
      ≡ SD.liftD fmt (IR.Cata (wf-⌊⌋ wfF) (subst (λ o → IR.IR o ⌊ A ⌋) (⌊⟧T-commute F A) m-alg)) k
cata-fold-eq {F = F} {A = A} wfF algE m-alg feq dγ k =
  cong ([] ,_) (extensionality λ x →
    trans (cong (λ g → λ n → let r = sem-cata wfF (SD.cata-ev-algˢ {F} {A} n g) x in (proj₁ r , proj₂ r)) feq)
          (sym (evalᴰ-Cata-erased {A} wfF m-alg x)))
