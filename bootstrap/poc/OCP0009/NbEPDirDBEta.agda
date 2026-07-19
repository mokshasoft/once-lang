------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 23 — (iii) η: FATTENING the definitional equality
--
-- `NbEPDirDBType`'s conversion is β-only, so the `core(Hom)` it realizes is
-- thin (β is irreversible → conversion ≈ α-equality on normal forms). The
-- design's definitional equality wants η too. This module ADDS η — the
-- reversible content that fattens the core — and exhibits genuinely distinct
-- terms it identifies.
--
--   * `_≅η_` — βη-conversion: `NbEPDirDBType`'s β-conversion (`emb`) plus the
--     η rule `t ≅η λx. (wk t) x` (function η-expansion), closed under symmetry
--     and transitivity. This is what a βη-typechecker's `⊢conv` would use.
--   * `fatten` — a concrete witness: `y ≅η λx. y x`, two SYNTACTICALLY DISTINCT
--     normal terms (a variable and a λ-abstraction) now convertible. β-only
--     conversion cannot relate them; η does. The core is genuinely fatter.
--
-- Scope: η is given for Π (functions) — the only formers with introduction
-- TERMS in this syntax. Σ-η (surjective pairing) would need pair/projection
-- term constructors, which `RTm` does not yet have. `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBEta where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs; RTm; var; lam; app; renTm )
open import poc.OCP0009.NbEPDirDBType using ( _≅_ )

private
  variable
    Γ : Cx

------------------------------------------------------------------------
-- βη-conversion: β-conversion embedded, plus function η.
------------------------------------------------------------------------

infix 3 _≅η_
data _≅η_ : {Γ : Cx} → RTm Γ → RTm Γ → Set where
  emb  : {t u : RTm Γ} → t ≅ u → t ≅η u
  η    : (t : RTm Γ) → t ≅η lam (app (renTm vs t) (var vz))
  ηsym : {t u : RTm Γ} → t ≅η u → u ≅η t
  ηtrn : {t u v : RTm Γ} → t ≅η u → u ≅η v → t ≅η v

------------------------------------------------------------------------
-- Fattening, concretely: `y ≅η λx. y x`. The right side is `lam (app (var
-- (vs vz)) (var vz))` — a λ-abstraction; the left is the bare variable `y`.
-- Distinct normal forms, identified only by η.
------------------------------------------------------------------------

fatten : var (vz {ε}) ≅η lam (app (var (vs vz)) (var vz))
fatten = η (var vz)
