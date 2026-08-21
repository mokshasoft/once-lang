------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★★★★★ GAP B, CLOSED:  gcd MEETS ITS SPEC.
--
--       gcd (a , b) ∣ a     and     gcd (a , b) ∣ b
--
--   at an ARBITRARY pair, through `amrec-ind`.
--
-- ★ THIS IS `amrec-ind`'s FIRST REAL CLIENT.  Everything it owes is
--   discharged here and nowhere else:
--     `StepExt`  — `gcdStepExt` (gap A, 2026-08-17)
--     `IndStep`  — `gcdIndStep` (`…GcdDvdA`)
--     the motive — `gcdP`, a `⌜Σ⌝` CODE
--   and the combinator supplies the induction.
--
-- ⚠ THE TWO CONJUNCTS COME FROM **ONE** PASS.  They are projections of a
--   single `⌜Σ⌝`, not two independent proofs — neither is provable alone
--   by this recursion (GAP-B-LAYER2-PLAN §1).  ⇒ for the three-customer
--   criterion these count as ONE customer, and that is a fact about the
--   mathematics, not about the encoding.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdSpec where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs; RTm; El; var; fst; snd; app; ⌜Nat⌝; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; single; _⊢_∷_; ⊢⌜Nat⌝ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBLibDvd using ( dvdT )
open import poc.OCP0009.NbEPDirDBLibDvdArith using ( QCode; QCode-sub; ⊢Q-fst; ⊢Q-snd )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( Prv; prvOk; prv-cast; module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibAmrecInd using ( module Stmt; module Concl )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( msr; ⊢msr; gcdStp; ⊢gcdStp )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtA using ( gcdStepExt )
open import poc.OCP0009.NbEPDirDBExamplesGcdDvdA using ( gcdP; ⊢gcdP; gcdIndStep )

module GcdS (Δ : Ctx) = Stmt  Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp
module GcdC (Δ : Ctx) = Concl Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp
module GcdT (Δ : Ctx) = AmTΠ  Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp

-- ★ gcd itself — the recursor at gcd's step.
gcdTm : (Δ : Ctx) → RTm ⌊ Δ ⌋
gcdTm Δ = GcdT.amrecTm Δ

-- ⚠ the last peel: `amrec-ind` states its conclusion through `IndAt`,
--   which fills the RESULT slot with `valAt = app (w amrec) (var vz)`.
--   Two `QCode-sub`s and one `wk-single` turn it into the readable form.
IndAt-gcd : {Δ : Ctx} (x : RTm ⌊ Δ ⌋) →
            GcdS.IndAt Δ gcdP x
          ≡ El (QCode (fst x) (snd x) (app (gcdTm Δ) x))
IndAt-gcd {Δ} x =
  cong El
    (trans (cong (subTm (single x))
                 (QCode-sub {σ = single (GcdS.valAt Δ)}
                    (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
           (trans (QCode-sub {σ = single x}
                     (fst (var vz)) (snd (var vz)) (GcdS.valAt Δ))
                  (cong (λ t → QCode (fst x) (snd x) (app t x))
                        (wk-single {v = x} (gcdTm Δ)))))

------------------------------------------------------------------------
-- ★★★★★★★ THE THEOREM.
------------------------------------------------------------------------

gcdSpec : {Δ : Ctx} {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ PairT →
          Prv Δ (El (QCode (fst x) (snd x) (app (gcdTm Δ) x)))
gcdSpec {Δ} {x} dx =
  prv-cast (IndAt-gcd x)
           (GcdC.amrecInd Δ gcdStepExt ⊢gcdP gcdIndStep dx)

-- ★★ …and its two projections.
gcd∣fst : {Δ : Ctx} {x : RTm ⌊ Δ ⌋} → (dx : Δ ⊢ x ∷ PairT) →
          Δ ⊢ fst _ ∷ dvdT (app (gcdTm Δ) x) (fst x)
gcd∣fst dx = ⊢Q-fst (prvOk (gcdSpec dx))

gcd∣snd : {Δ : Ctx} {x : RTm ⌊ Δ ⌋} → (dx : Δ ⊢ x ∷ PairT) →
          Δ ⊢ snd _ ∷ dvdT (app (gcdTm Δ) x) (snd x)
gcd∣snd dx = ⊢Q-snd (prvOk (gcdSpec dx))
