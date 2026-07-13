------------------------------------------------------------------------
-- OCP-0009 · Consistency ladder, rung 2 — the universe rungs
--
-- Two results, one per universe artifact, bracketing the Gödel line:
--
-- (A) BELOW the line — the first-order Tarski universe (`NbEPEl.Code`)
--     CANNOT EVEN EXPRESS FALSITY: every code decodes to an inhabited type
--     (`point`). So "consistency of the Code-rung" is not merely provable,
--     it is trivial — there is no false proposition to fear. This makes the
--     expressibility/Gödel trade-off concrete: the price of a rung so weak
--     that its consistency is free is that it cannot state anything worth
--     doubting.
--
-- (B) AT the ladder — the stratified hierarchy (`NbEPUnivH`, now with empty
--     codes `⊥₀`/`⊥₁`): the consistency-style statement about level 0,
--
--        `Con₀  ≡  "no uniform inhabitant of ALL small types"
--               ≡  ((A : U₀) → El₀ A) → ⊥
--
--     is EXPRESSIBLE ONLY AT LEVEL 1 — it quantifies over `U₀`, and the only
--     code for `U₀` lives in `U₁` (predicativity: there is deliberately no
--     `` `U₀ : U₀ ``, which is exactly Girard-avoidance). Level 1 then also
--     PROVES it: `con₀ = λ f → f `⊥₀`. This is the Gödel ladder in
--     miniature, internal to our own tower: **each level can state and prove
--     the non-degeneracy of the level below, and no level can do it for
--     itself.** ("Once+" is not a different language — it is the same tower,
--     one universe level up.)
--
-- The anchor of the whole ladder remains the meta-theory: this module is
-- Agda `--safe`, so both results are theorems of Agda — relative
-- consistency, which is the strongest thing Gödel II permits anyone.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPCon2 where

open import normalizer.Syntax.Types
  using ( ⊥; ⊤; tt; _,_; inj₁; ¬_ )
open import normalizer.Testing.Evaluator
  using ( ⟦_⟧T; Fix; fix )
open import poc.OCP0009.NbEPEl
  using ( Code; `unit; `nat; _`×_; _`⇒_; _`Π_; _`Σ_; El )
open import poc.OCP0009.NbEPUnivH
  using ( U₀; `⊥₀; `nat₀; `unit₀; `Π₀; El₀
        ; U₁; `U₀; `⇑; `⊥₁; `Π₁; El₁; _≡₁_; refl₁ )

------------------------------------------------------------------------
-- (A) The first-order Code universe cannot express falsity: every code
-- denotes an inhabited type in the Set-model.
------------------------------------------------------------------------

point : ∀ c → ⟦ El c ⟧T
point `unit    = tt
point `nat     = fix (inj₁ tt)          -- zero : ⟦ μ(One ⊕ Id) ⟧T
point (a `× b) = point a , point b
point (a `⇒ b) = λ _ → point b
point (a `Π b) = λ _ → point b
point (a `Σ b) = point a , point b

-- Immediate corollary: no code decodes to an empty type — falsity is not in
-- this universe's vocabulary. (Sub-Gödel: nothing to prove consistent OF.)
no-falsity : ∀ c → ¬ (⟦ El c ⟧T → ⊥)
no-falsity c empty = empty (point c)

------------------------------------------------------------------------
-- (B) The ladder: level 1 states and proves the non-degeneracy of level 0.
------------------------------------------------------------------------

-- The statement, as a LEVEL-1 code. It needs `` `U₀ `` (quantification over
-- all small types) — inexpressible at level 0, where no such code exists.
`Con₀ : U₁
`Con₀ = `Π₁ (`Π₁ `U₀ (λ A → `⇑ A)) (λ _ → `⊥₁)

-- Sanity: the code decodes to exactly the intended statement.
_ : El₁ `Con₀ ≡₁ (((A : U₀) → El₀ A) → ⊥)
_ = refl₁

-- The proof, at level 1: a uniform inhabitant of all small types would in
-- particular inhabit the small falsity.
con₀ : El₁ `Con₀
con₀ f = f `⊥₀

-- Contrast, for the record: level 0 can state (and prove) statements about
-- its INDIVIDUAL types — e.g. `¬⊥₀` as a small code — but not about ALL of
-- its types at once. The step from "each" to "all" is exactly one universe.
`¬⊥₀ : U₀
`¬⊥₀ = `Π₀ `⊥₀ (λ _ → `⊥₀)

_ : El₀ `¬⊥₀
_ = λ b → b
