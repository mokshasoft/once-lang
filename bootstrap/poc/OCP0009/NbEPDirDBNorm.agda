------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 22 — (i) DECIDING CONVERSION BY NbE FORCES INTRINSIC
--                            TYPING: the raw calculus is not normalizing
--
-- The design (§1) wants definitional equality = `core(Hom)` DECIDED BY NbE.
-- The typing+conversion kernel (`NbEPDirDBType`, dHoTT-21) is declarative;
-- making conversion DECIDABLE means a normalizer `nf` with `nf t ≅ t` and
-- `t ≅ u → nf t ≡ nf u`. This module records the load-bearing obstruction to
-- doing that on the RAW syntax, and hence the forced next architectural step.
--
-- A total β-normalizer cannot exist on `RTm`: the syntax admits NON-
-- NORMALIZING terms. Concretely `Ω = (λx. x x)(λx. x x)` β-reduces TO ITSELF
-- (`Ω-loops : Ω ⟶ Ω`), so it has an infinite reduction sequence and no normal
-- form. Any `nf : RTm Γ → RTm Γ` landing in normal forms is therefore not a
-- total function — deciding conversion by NbE is IMPOSSIBLE at this level.
--
-- CONCLUSION (a real design result, not a gap): the "decided by NbE" half of
-- the design is only available on WELL-TYPED terms, where strong normalization
-- holds (standard). So the NbE decision procedure must be built over the
-- `_⊢_∷_` judgment (intrinsic/typed NbE), not over raw `RTm`. The experiment
-- (dHoTT-20) and typing (dHoTT-21) got us the strict dependent kernel; THIS is
-- the precise reason the next slice must move to typed normalization.
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBNorm where

open import poc.OCP0009.NbEPDirDBPi using ( ε; RTm; var; vz; lam; app )
open import poc.OCP0009.NbEPDirDBType using ( _⟶_; β )

-- The self-application combinator and Ω.
δ : RTm ε
δ = lam (app (var vz) (var vz))

Ω : RTm ε
Ω = app δ δ

-- Ω β-reduces to itself: `(λx. x x)(λx. x x) ⟶ (λx. x x)(λx. x x)`. The
-- contractum `(x x)[δ/x]` is `δ δ = Ω` definitionally, so this typechecks as
-- `Ω ⟶ Ω`. An infinite reduction — no normal form — so no total `nf` on `RTm`.
Ω-loops : Ω ⟶ Ω
Ω-loops = β (app (var vz) (var vz)) δ
