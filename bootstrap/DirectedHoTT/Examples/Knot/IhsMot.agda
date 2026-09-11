------------------------------------------------------------------------
-- OCP-0009 · KNOT — `ihsK` PART 1: motive, the `dι` row, and the hoisted body.
--
--     ihs : Desc → RTm Γ → DCon → RTm Γ → RTm Γ     -- `Spec/Syntax:981`
--     ihs D ms dι       p = unit
--     ihs D ms (dρ C)   p = pair (elim D ms (fst p)) (ihs D ms C (snd p))
--     ihs D ms (dκ A C) p = ihs D ms C (snd p)
--
-- ⚠⚠ NEEDS THE COMPACTING COLLECTOR.  Measured: without `-c` this module
--   is KILLED at the 5.5 GB cgroup cap; with it, 4.9 GB and rc=0 in
--   2:23.  `sweep.sh`'s `needs_c` greps the first 40 lines for
--   "COMPACTING COLLECTOR", so this paragraph is the mechanism, not a
--   note — `agda-oom-is-a-gc-choice`, and the collector was worth more
--   here than any restructuring of the program.
--
-- ★ RAW TERMS AGAIN — `unit`/`pair`/`elim`/`fst`/`snd` are all RTm
--   CONSTRUCTORS, so the result sort is `sTm` throughout and the motive
--   is CONSTANT in the scrutinee, exactly as for `selK`.
--
-- ★ THREE PASSENGERS: `D`, `ms`, `p`.  `D`/`ms` are fixed across the
--   recursion and `p` shrinks, but a method is a CLOSED term, so all
--   three ride as `Π`s in the motive.
--
-- ⚠ THE BINDER ARITHMETIC IS THE RISK.  `conSMotK` has ONE `Π` and
--   reads the index at `vs² vz`; each further `Π` pushes it one deeper,
--   so the four occurrences here sit at `vs¹`, `vs²`, `vs³`, `vs⁴`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IhsMot where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; snd; Π; Nat; εwkTy; IMu )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; _⊢_∷_; ⊢var; here; there; ⊢snd; ty-Π; ty-IMu
        ; ⊢lam; imethTy; ty-Nat )
open import DirectedHoTT.Spec.Syntax using ( lam )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.Desc using ( cDCon-i; cDCon-rho; cDCon-kap )
open import DirectedHoTT.Examples.Knot.Wf using ( cDCon-iWf; cDCon-rhoWf; cDCon-kapWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagDCon-i; tagDCon-rho; tagDCon-kap )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-unitK; Tm-pairK; Tm-elimK; Tm-fstK; Tm-sndK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-unitKv; ⊢Tm-pairKv; ⊢Tm-elimKv; ⊢Tm-fstKv; ⊢Tm-sndKv )
open import DirectedHoTT.Spec.Syntax using ( app; fst; isingle; iext; iρ; iκ; iι; ⌜Id⌝; ⌜Nat⌝; nzero )
open import DirectedHoTT.Spec.Typing using ( ⊢app )
open import DirectedHoTT.Lib.IPay using ( ⊢ihHere; ⊢ihSkipρ )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sDesc; ⊢sDesc; sDCon; ⊢sDCon; sTy; ⊢sTy; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

-- ★★★ THE DEPTH RIDES AS A PASSENGER — `Knot/IPayTyMot`'s idiom.
--
-- ⚠ MY FIRST VERSION READ THE AMBIENT INDEX FOUR TIMES, once per `Π`
--   level, at `vs¹`…`vs⁴`.  That does NOT survive `⊢methLam`'s
--   `renTy (extR (extR vs))`: `extR² vs` fixes only the top TWO
--   variables, so the deeper occurrences SHIFT and the method's
--   codomain stops matching.  `lookupMotK` gets away with one
--   occurrence at `vs²`; four do not.
--
-- ★ `ipayTyMotK` shows the fix: bind the depth ONCE as a `Π Nat`
--   passenger and let every later slot read that motive-LOCAL binder.
--   Here nothing needs the ambient index at all — `ihs`'s result sits
--   at whatever depth `D`/`ms`/`p` do — so the motive is closed in the
--   2-var context and the caller ties `n` to `snd ⟨i⟩`.
ihsMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
ihsMotK =
  Π Nat
   (Π (K (pair sDesc (var vz)))
    (Π (K (pair sTm (var (vs vz))))
     (Π (K (pair sTm (var (vs (vs vz)))))
        (K (pair sTm (var (vs (vs (vs vz))))))))) 

⊢ihsMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty ihsMotK
⊢ihsMotK =
  ty-Π ty-Nat
   (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
    (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
     (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
        (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★ ROW `dι` — `ihs D ms dι p = unit`.  SEVEN lams: `⊢methLam`'s three
--   then the motive's four passengers (n, D, ms, p).
------------------------------------------------------------------------

ihsIota : {Γ : Cx} → RTm Γ
ihsIota = lam (lam (lam (lam (lam (lam (lam Tm-unitK))))))

⊢ihsIota : {Γ : Ctx} →
           Γ ⊢ ihsIota ∷ imethTy KnotD IPair tagDCon-i cDCon-i ihsMotK
⊢ihsIota =
  ⊢methLam KnotD IPair tagDCon-i cDCon-i KnotWf cDCon-iWf ⊢IPair ⊢ihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sDesc (⊢var here)))
        (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
            (⊢Tm-unitKv (var (vs (vs (vs vz)))) (⊢var (there (there (there here)))))))))

------------------------------------------------------------------------
-- ★ ROW `dρ` — `ihs D ms (dρ C) p = pair (elim D ms (fst p)) (ihs D ms C (snd p))`.
--
-- ⚠ SEVEN LAMS, so the IH tuple is `vs⁴`, the payload `vs⁵`, the index
--   `vs⁶` — `⊢lookupCons`'s depths plus three.
--
-- ⚠⚠ EVERY DEPTH ARGUMENT WRITTEN OUT, NOT `_`.  With five `_`s this
--   module climbed 1.7 GB → 5.2 GB in two minutes and hit the cgroup
--   cap.  A `_` here is not a placeholder for a value Agda already has —
--   it is a COMPUTATION re-run at every occurrence
--   (`meta-standing-for-a-computation`, and that one was six `_`s and
--   5.5 GB too).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★ THE BODY, HOISTED — and the hoist is MEASURED, not guessed.
--
--   same row, same 7 lams, TRIVIAL body   →   8.8s, rc=0
--   same row, same 7 lams, the real body  →   1.6 GB … 5.5 GB cap, killed
--
-- ⇒ CONTEXT DEPTH IS NOT THE COST and neither is the row's telescope;
--   the BODY is, all of it.  ⚠ I first blamed depth (`agda-cost-is-
--   context-depth`, ~1.7×/slot) and would have "fixed" it by bundling
--   `D`/`ms` into one passenger — a worse PROGRAM for a cost that does
--   not exist.  The probe cost one minute and killed that plan.
--
-- ★ So the four `⊢Tm-*Kv` towers are elaborated ONCE here, at an
--   ABSTRACT context and abstract terms, and the row applies the Def.
--   `agda-cost-is-elaborated-term-size`: split into Def-backed lemmas.
------------------------------------------------------------------------

⊢ihsStep : {Γ : Ctx} {n D ms p f : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ Nat →
           Γ ⊢ D ∷ K (pair sDesc n) → Γ ⊢ ms ∷ K (pair sTm n) →
           Γ ⊢ p ∷ K (pair sTm n) → Γ ⊢ f ∷ K (pair sTm n) →
           Γ ⊢ Tm-pairK (Tm-elimK D ms (Tm-fstK p)) f ∷ K (pair sTm n)
⊢ihsStep {n = n} dn dD dms dp df =
  ⊢Tm-pairKv n dn (⊢Tm-elimKv n dn dD dms (⊢Tm-fstKv n dn dp)) df

