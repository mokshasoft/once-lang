------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `lkp`/`∋lkp`: VARIABLE LOOKUP, COMPUTED.
--
-- ★ THE WF AXIS, GENERALISED.  The axis's essence is not orders: it
--   replaces an inductive RELATION with a COMPUTING function plus an
--   equation, so discharging it becomes CONVERSION.  `_∋_∷_` is such a
--   relation, and its `there`-tower is a UNARY ENCODING OF A NUMBER:
--
--       here  : (Γ ▹ A) ∋ vz ∷ renTy vs A
--       there : Γ ∋ x ∷ A → (Γ ▹ B) ∋ vs x ∷ renTy vs A
--
-- ⚠ MEASURED, and it is why this module exists.  The Knot's wf files
--   (`RedWfA` + `RedWfB` + `TyRedWf` + `Wf`, 9 944 lines ≈ 19% of the
--   Knot) hold **14 256 `there`/`here` tokens across 3 101 `⊢var`
--   sites** — 75% of the whole wf proof burden — at an average tower
--   depth of ~4.6.  Only 24% is genuine typing.
--   ⇒ replacing a TOWER by its NUMBER is the whole migration.
--
-- ★★ ELIGIBILITY — the criterion that predicted this would work where
--   so much else did not:
--
--       THE AXIS-STYLE MOVE WORKS EXACTLY WHERE THE SUBJECT IS CONCRETE.
--
--   Adequacy quantifies over an abstract `t`, which is what defeated the
--   normaliser (`Lib/Eval` sticks on an abstract head), `decTm`, and the
--   equation-shaped restatement.  wf rows are about CONCRETE contexts,
--   so the computation runs.
--
-- ⚠ THE OBLIGATION THIS MODULE DISCHARGES is the DERIVATION-LEVEL
--   BRIDGE, which was NOT implied by the term-level result: `vsⁿ` shows
--   the computed VARIABLE equals the hand-counted one, but producing an
--   `_∋_∷_` DERIVATION is a different claim.  `∋lkp` is that claim, and
--   `tmp/LkpCompute.agda` pins it — `∋lkp Γ4 (vs (vs (vs vz)))` is
--   `refl`-equal to `there (there (there here))`, with a control at the
--   wrong depth failing `vz != vs vz`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Lkp where

open import DirectedHoTT.Spec.Syntax using ( Cx; Var; vz; vs; RTy; renTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; _∋_∷_; here; there )

-- the type at a variable, COMPUTED
lkp : (Γ : Ctx) (x : Var ⌊ Γ ⌋) → RTy ⌊ Γ ⌋
lkp (Γ ▹ A) vz     = renTy vs A
lkp (Γ ▹ B) (vs x) = renTy vs (lkp Γ x)

-- ★ the derivation, PRODUCED rather than written out as a tower
∋lkp : (Γ : Ctx) (x : Var ⌊ Γ ⌋) → Γ ∋ x ∷ lkp Γ x
∋lkp (Γ ▹ A) vz     = here
∋lkp (Γ ▹ B) (vs x) = there (∋lkp Γ x)

------------------------------------------------------------------------
-- ★ AND THE VARIABLE ITSELF AS A NUMBER (`KNOT-LESSONS` §9).
--   `vsⁿ k vz` is refl-equal to the hand-counted `vs (vs (… vz))`, so a
--   tower on BOTH sides — the variable and its derivation — becomes `k`.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax using ( _∙ )

_+∙_ : Cx → ℕ → Cx
Γ +∙ zero  = Γ
Γ +∙ suc n = (Γ +∙ n) ∙

vsⁿ : ∀ {Γ} (k : ℕ) → Var Γ → Var (Γ +∙ k)
vsⁿ zero    x = x
vsⁿ (suc k) x = vs (vsⁿ k x)
