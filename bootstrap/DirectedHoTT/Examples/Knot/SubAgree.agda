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
  using ( Cx; ε; _∙; RTm; RTy; Var; vz; vs; Sub; Ren; app; lam; var; pair
        ; subTm; extS; extR )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; single )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enVar )
open import DirectedHoTT.Examples.Knot.Sorts using ( num; len )
open import DirectedHoTT.Examples.Knot.Single using ( singleK )
open import DirectedHoTT.Examples.Knot.Nrs using ( nrsSubK )
open import DirectedHoTT.Spec.Typing using ( nrs )
open import DirectedHoTT.Examples.Knot.RenSpec
  using ( singleK-vz; singleK-vs; extRNK-vz; extRNK-vs; inVsX; nrsK-vz; nrsK-vs )
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK )

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

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

------------------------------------------------------------------------
-- ★★★ THE RENAMING'S REPRESENTATION RELATION.
--
-- ⚠ AT THE `Var` SORT, not `Tm`.  `Knot/SubAgree.Represents` relates a
--   `Sub` to a term that produces ENCODED TERMS; a renaming produces
--   encoded VARIABLES, and step 2's laws (`extRNK-vz`/`extRNK-vs`) land
--   on `Var-vzK`/`Var-vsK`.  ⇒ two relations, one per sort, and the
--   renaming one is what `ren-agree` will carry.
------------------------------------------------------------------------

RepresentsR : {Γ Δ Θ : Cx} → Ren Γ Δ → RTm Θ → Set
RepresentsR {Γ = Γ} ρ r = (x : Var Γ) → app r (enVar x) ⟶* enVar (ρ x)

------------------------------------------------------------------------
-- ★★★ EXTENSION PRESERVES IT — the one structural step `Knot/SzAgree`
-- has no analogue for, because a fold never crosses a binder.
--
-- ⚠ THE TARGET DEPTH IS FORCED TO `num (len Δ)`.  `extRNK-vz` lands on
--   `Var-vzK n`, and the goal is `enVar {Δ ∙} vz = Var-vzK (num (len Δ))`.
--   So `n` is not free: the lemma may only be stated at the depth the
--   ENCODING uses.  Passing `n` as a parameter would make it unprovable.
------------------------------------------------------------------------

extR-Represents :
  {Γ Δ Θ : Cx} {ρ : Ren Γ Δ} {r : RTm Θ} (d : RTm Θ) →
  RepresentsR ρ r → RepresentsR (extR ρ) (extRNK d (num (len Δ)) r)
extR-Represents d h vz     = extRNK-vz d _ _ _
extR-Represents d h (vs x) = extRNK-vs d _ _ _ _ » inVsX (h x)

------------------------------------------------------------------------
-- ★★★ AND `nrs`'s HALF — the RAISING substitution.
--
--     nrs vz     = nsuc (var (vs vz))
--     nrs (vs x) = var (vs (vs x))
--
-- ★ THE TWO LAWS WERE PROVED IN STEP 2 (`Knot/RenSpec.nrsK-vz`/`-vs`, the
--   row that was parked at eight attempts).  This is only their
--   PACKAGING as `Represents` — the same three lines `single-Represents`
--   is, and the reason the laws were worth the fight.
--
-- ⚠ THE DEPTHS ARE FORCED, and differ from `single`'s: `nrs` raises, so
--   the outer `Var-vsK` carries `⌈Γ ∙⌉` while the inner carries `⌈Γ⌉`.
--   Passing one depth would not typecheck.
------------------------------------------------------------------------

nrs-Represents : {Γ Θ : Cx} →
                 Represents {Γ = Γ ∙} {Θ = Θ} nrs (nrsSubK (num (len (Γ ∙))))
nrs-Represents {Γ} vz     = nrsK-vz (num (len (Γ ∙))) (num (len Γ))
nrs-Represents {Γ} (vs x) = nrsK-vs (num (len (Γ ∙))) (num (len Γ)) (enVar x)
