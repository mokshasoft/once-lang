------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE **POINTWISE SPECIFICATIONS** OF THE
-- RENAMING AND SUBSTITUTION VALUES.
--
-- `PLAN-RENAMING.md` §5: once a renaming is a VALUE rather than a fold
-- with its choice inlined, its specification is pointwise and small —
--
--     app ⌈σ⌉ ⌈vz⌉   ⟶*  ⌈ σ vz ⌉
--     app ⌈σ⌉ ⌈vs x⌉ ⟶*  ⌈ σ (vs x) ⌉
--
-- and `Knot/Wk.wkK` CANNOT BE GIVEN ONE AT ALL, because it is not a
-- function you can apply: it is a fold with the renaming baked in.  That
-- is the difference the whole arc turns on, and this module is the half
-- of it that can be written down.
--
-- ★★ AND IT IS THE SHAPE THE NORMALIZER ALREADY USES.  On
--   `origin/plan-0.76-context-indexed-composition`,
--   `Theory/Spec/AlgebraSpec` states its laws as
--   `alg ∘ inj-N ⟶* In ∘ inj-N` — per position, pointwise, a REDUCTION.
--   `SatisfiesSpec` discharges all fifteen in 78 lines, 14 of them
--   trivial.  `PLAN-RENAMING.md` §11.4/§11.5.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenSpec where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; app; lam; var; vz; vs; renTm; nsuc; pair )
open import DirectedHoTT.Spec.Typing
  using ( _⟶*_; done; step; β; single; wk-single )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vsK )
open import DirectedHoTT.Examples.Knot.RenTm using ( vsRenK )

------------------------------------------------------------------------
-- ★★★ `vs`, AND IT IS ONE β-STEP.
--
--     vsRenK n = lam (Var-vsK (w n) (var vz))
--
-- ⚠ ONE LAW, NOT TWO.  `vsRenK` does not CASE on its argument — it is
--   the renaming `x ↦ vs x`, uniformly — so `vz` and `vs y` are the same
--   clause.  `single`/`extR`/`nrs` all case, and each owes two.
--
-- ★★★ AND THIS IS EXACTLY WHAT `Knot/Wk.wkK` CANNOT SAY.  There is no
--   `app wkK x` to reduce: `wkK` is `ielim`, and its renaming exists
--   only as the shape of `Lib/IWk`'s 53 derived methods.  ⇒ the defect
--   was not that the law went unproved; it was that the law was
--   UNSTATABLE.
------------------------------------------------------------------------

vsRenK-app : {Γ : Cx} (n x : RTm Γ) →
             app (vsRenK n) x ⟶* Var-vsK n x
vsRenK-app n x =
  ⟶*-castᵣ (cong (λ z → Var-vsK z x) (wk-single {v = x} n))
           (step (β _ _) done)
