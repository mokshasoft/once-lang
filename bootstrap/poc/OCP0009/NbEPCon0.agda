------------------------------------------------------------------------
-- OCP-0009 · Consistency ladder, rung 0 — the CCC IR and the fragment syntax
--
-- THE POINT. Gödel II says a system that interprets enough arithmetic cannot
-- prove its own consistency. This rung sits BELOW that threshold: the CCC
-- morphism language has no internal propositions at all (it cannot even
-- STATE `Con`), so Gödel II does not apply — and its consistency is simply
-- PROVABLE outright in the meta-theory (Agda `--safe`), via the standard
-- Set-model. That is the base of the ladder: absolute (well:
-- relative-to-Agda) consistency for the sub-Gödel rungs, and explicit
-- one-level-up models (`NbEPCon1`, `NbEPCon2`) once the rungs grow
-- expressive enough that Gödel bites.
--
-- Two theorems, both one-liners because the model (`normalizer.Testing.
-- Evaluator`, `--safe`) already exists:
--
--   * `consistency`   — no closed point of the empty type in the IR:
--                       `¬ Term Unit Void`. A term `t` would evaluate to an
--                       Agda inhabitant of `⊥`.
--   * `consistencyTm` — the same for the POC fragment syntax `Tm` (the
--                       object language of the whole principled NbE track),
--                       via its embedding `emb : Tm A B → Term A B`.
--
-- Plus NON-DEGENERACY (the equational face of consistency): the theory does
-- not equate everything — the model separates `inl` from `inr`. Stated
-- pointwise (no funext needed), so this whole module is `--safe`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPCon0 where

open import normalizer.Syntax.Types
  using ( Ty; Unit; Void; _+_; ⊥; ¬_; _≡_; tt )
open import normalizer.Syntax.CCC
  using ( Term; inl; inr )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; eval )
open import poc.OCP0009.NbEPTm
  using ( Tm; emb )

------------------------------------------------------------------------
-- Consistency: no closed point of the initial object.
------------------------------------------------------------------------

-- The IR: a closed morphism `Unit → Void` would be an Agda proof of `⊥`.
consistency : ¬ Term Unit Void
consistency t = eval t tt

-- The fragment syntax `Tm` (the principled track's object language), through
-- its embedding into the IR.
consistencyTm : ¬ Tm Unit Void
consistencyTm t = eval (emb t) tt

------------------------------------------------------------------------
-- Non-degeneracy: the equational theory does not collapse. `inl` and `inr`
-- at `Unit + Unit` are separated by the model — so no sound conversion can
-- ever equate them. (Pointwise statement: this is exactly the older track's
-- `_≋_` unfolded, kept local so the module needs no funext-tainted import.)
------------------------------------------------------------------------

B₂ : Ty
B₂ = Unit + Unit

no-collapse : ((x : ⟦ Unit ⟧T) → eval (inl {Unit} {Unit}) x ≡ eval inr x) → ⊥
no-collapse h with h tt
... | ()
