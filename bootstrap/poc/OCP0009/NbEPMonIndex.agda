------------------------------------------------------------------------
-- OCP-0009 · THE MONOIDAL/LINEAR TOWER — INDEX AND API
--
-- One entry point for the linear-core results. Importing THIS module
-- (--safe) brings the headline theorems into scope; its import closure
-- is machine-checked escape-hatch-free.
--
-- THE RESULTS, in dependency order:
--
--  1. THE STRUCTURAL CORE IS DECIDED (`NbEPMonC` → `NbEPMonE`):
--     `_≈m_` is the free-SMC theory; `wire` its complete invariant.
--       dec≈     : ∀ f g → Dec (f ≈m g)
--       complete : wire f ≗ wire g → f ≈m g        (coherence proper)
--     Climb: NbEPMonN/P/A/U (normal forms, realizations, uniqueness) →
--     R/Y/I/Q (swapHead toolkit, YANG–BAXTER, algebra realized) →
--     G/K/S/H/Z (generator squares, Kelly lemmas, nt-σ) → E (summit).
--
--  2. CONVERSION IS NORMALIZATION (`NbEPMonD`):
--       nf f ≡ nf g  ⟺  f ≈m g       (nf-sound / nf-complete)
--     plus the groupoid theorem (`invS`) and the kernel universe where
--     `` `conv f g `` is a TYPE deciding by `refl` on closed programs.
--
--  3. THE AXIOMS ARE REDUNDANT (`NbEPMonO`): pentagon, triangle,
--     hexagon, Yang–Baxter — each re-derived from `complete` in one
--     line. The kernel's trust surface is `wire`/`≈m-sound`/`complete`.
--
--  4. THE CLOSED CORE (`NbEPMonL`/`NbEPMonV`/`NbEPMonX`): `_≈c_` is
--     the free-SMCC theory (β⊸/η⊸); the decided fragment embeds
--     (`embE`); linearity SURVIVES closure (`bal` — duplication,
--     discard, and the K combinator refuted in-core); extensional
--     soundness gives the refutation oracle (`ExtModel.soundE`).
--
--  5. LINEAR NbE (`NbEPMonT`/`NbEPMonW` → `NbEPMonF`): a TOTAL,
--     placement-canonical normalizer for the free SMCC —
--       NF : CTm A B → CTm A B
--     over a Day-convolution model whose world category is the
--     decided structural core. β⊸, η⊸, let-splits of neutral pairs,
--     unit-uses, and the structural theory all compute away; demos
--     decide higher-order equalities by `refl`.
--     (Evolution: NbEPMonM right-pure → B pairs → J units/total → F
--     hoisting; import F.)
--
-- OPEN (recorded in plan §10): L3.4a part 2 (same-boundary node order
-- + λ-boundary commutation — the proof-net core) and L3.4b (adequacy
-- of NF w.r.t. `_≈c_` — derivation recorded, NbEPFund-scale climb).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonIndex where

-- 1. The decided structural core.
open import poc.OCP0009.NbEPMonC public
  using ( STm; _≈m_; wire; ≈m-sound; conv?; conv-refutes )
open import poc.OCP0009.NbEPMonE public
  using ( pOf; keySq; canon; complete; dec≈ )

-- 2. Conversion as normalization; the kernel universe.
open import poc.OCP0009.NbEPMonD public
  using ( nf; nf-sound; nf-complete; invS; inv-l; inv-r
        ; U; El; `conv; `shom; mk-conv; use-conv; Fam; transp )

-- 3. The axioms, re-derived by decision.
open import poc.OCP0009.NbEPMonO public
  using ( pentagon′; triangle′; hexagon′; σ-invol′; YB′; ŝ-invol′ )

-- 4. The closed linear core: theory, bridge, linearity, refutation.
open import poc.OCP0009.NbEPMonL public
  using ( CTy; CTm; _≈c_; emb; embT; embE )
open import poc.OCP0009.NbEPMonV public
  using ( bal; no-dupC; no-discardC; no-dup⊸; no-weakenC )
open import poc.OCP0009.NbEPMonX as X public
  using ( no-σc-id )
module ExtModel = X.ExtModel

-- 5. Linear NbE: the total, placement-canonical normalizer.
open import poc.OCP0009.NbEPMonF public
  using ( Val; evalV; reify; reflectTy; NF )
