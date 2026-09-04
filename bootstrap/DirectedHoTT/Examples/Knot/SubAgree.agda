------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ STEP 3: `subTm`'s AGREEMENT, AND THE
-- RELATION THAT MAKES IT STATABLE.
--
-- ⚠⚠ THE OBVIOUS STATEMENT CANNOT BE WRITTEN.  One wants
--
--     sub-agree : subTmAtK … ⌈σ⌉ ⌈t⌉ ⟶* ⌈ subTm σ t ⌉
--
--   and there is no `⌈σ⌉`: a `Sub Γ Δ` is an AGDA FUNCTION
--   (`Var Γ → RTm Δ`, `Spec/Syntax:330`), and `Knot/Map` encodes
--   SYNTAX, not functions.  `enTm`/`enVar` have nothing to say about it.
--
-- ★★★ SO THE ENCODED SUBSTITUTION IS RELATED, NOT COMPUTED:
--
--     Represents σ s  =  ∀ x → app s ⌈x⌉ ⟶* ⌈ σ x ⌉
--
--   — and THAT IS EXACTLY STEP 2'S POINTWISE LAW.  `Knot/RenSpec`'s
--   `singleK-vz`/`singleK-vs` say precisely `Represents (single u)
--   (singleK n ⌈u⌉)`; `vsRenK-app` says it for `vs`.  ⇒ the laws written
--   in step 2 are not preparation for step 3, they ARE its hypothesis.
--
-- ★★ AND THIS IS WHY `Knot/Wk.wkK` COULD NEVER JOIN.  `Represents` is a
--   statement about APPLYING `s`.  `wkK` is an `ielim` with its renaming
--   inlined — there is no `s` to apply, so it cannot even be RELATED to
--   a meta-level substitution, let alone proved equal to one.
--   `PLAN-RENAMING.md` §15.1.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubAgree where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Var; vz; vs; Sub; app; lam; var; pair
        ; subTm; extS )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; single )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len )
open import DirectedHoTT.Examples.Knot.Single using ( singleK )
open import DirectedHoTT.Examples.Knot.RenSpec using ( singleK-vz; singleK-vs )

------------------------------------------------------------------------
-- ★ THE REPRESENTATION RELATION.
--
-- ⚠ `s` LIVES IN AN ARBITRARY OBJECT CONTEXT `Θ`, not in `Δ`.  The
--   encoding is context-agnostic (`enTm : RTm Γ → RTm Γ'`), so the
--   object-level substitution is a CLOSED-ish term describing σ, not a
--   term living where σ's results do.
------------------------------------------------------------------------

Represents : {Γ Δ Θ : Cx} → Sub Γ Δ → RTm Θ → Set
Represents {Γ = Γ} σ s = (x : Var Γ) → app s (enVar x) ⟶* enTm (σ x)

------------------------------------------------------------------------
-- ★★★ AND STEP 2'S LAWS DISCHARGE IT, ON THE NOSE.
--
-- ⚠ `single u` cases on the variable and so does `Knot/RenSpec`'s pair
--   of laws — `vz` gives `u`, `vs x` gives `var x` — which is `single`'s
--   definition (`Spec/Typing`) read back.  ⇒ the two lemmas ARE the two
--   clauses, and the proof is `λ { vz → … ; (vs x) → … }`.
------------------------------------------------------------------------

single-Represents : {Γ Θ : Cx} (n : RTm Θ) {u : RTm Γ} →
                    Represents {Γ = Γ ∙} (single u) (singleK n (enTm u))
single-Represents {Γ = Γ} n {u = u} vz     = singleK-vz n (enTm u) (num (len Γ))
single-Represents {Γ = Γ} n {u = u} (vs x) =
  singleK-vs n (enTm u) (num (len Γ)) (enVar x)
