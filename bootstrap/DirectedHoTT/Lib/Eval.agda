------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ `ev1`/`evN`, THE EVALUATOR.  PLAN-NF Phase 0/1.
--
-- ★ WHY THIS EXISTS.  `KNOT-LESSONS` §10: the Knot's proofs are not
--   `refl` because `_⟶_` is a RELATION and nothing RUNS it, so every
--   computation step is WITNESSED instead of PERFORMED --
--   **14 702 hand-built reduction steps against 209 `refl`s**, and the
--   β-family alone is ~2 925 of them.  Agda does not have that burden
--   because its conversion checker RUNS its functions.  This module is
--   the missing function.
--
-- ⚠⚠ THE OBVIOUS FORMULATION DOES NOT WORK, and the failure is the
--   whole design.  With `ev1 : RTm Γ → RTm Γ` and a separate
--   `ev1-sound`, the clause `ev1-sound (app f a)` CANNOT CLOSE:
--   `ev1 (app f a)` is STUCK on an abstract `f`, because `ev1`'s β
--   clause must first learn whether `f` is a `lam`.  That is precisely
--   the stuck-on-abstract problem the Knot suffers everywhere, and it
--   reappears in the tool built to remove it.
--
-- ★★★ THE FIX: RETURN THE TERM WITH ITS CHAIN (`Red t`).  Soundness is
--   then CONSTRUCTION rather than a lemma, nothing has to reduce to be
--   proved, and the catch-all is a pair we BUILD.  ⇒ prefer this shape
--   for anything that must both compute and carry evidence.
--
-- ⚠ FUEL IS NOT A COMPROMISE.  `evN` takes a step count because that is
--   what makes it COMPUTE, which is the entire point.  `snorm`
--   (`Metatheory/Fundamental:2008`) already proves `SN` for every
--   well-typed term, so a fuel-free `nf` is derivable -- PLAN-NF
--   Phase 2, and explicitly NOT a blocker for Phase 1.
--
-- ⚠ COVERAGE: β, βfst, βsnd plus congruence for lam/app/pair/fst/snd.
--   That is the β-family, the ~2 925.  The remaining computation rules
--   (`ι-ielim`, `ι-elim`, `natrec-*`, `jsub-refl`, `tr-J-*`, `ap-J`,
--   `ordtr-*`) are Phase 1 and each is one more clause plus one more
--   line of chain.  ⛔ Do NOT claim this evaluates the kernel.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.Eval where

open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( Σ; _,_; _≡_; refl )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; RTm; var; vz; lam; app; pair; fst; snd; subTm; unit )
open import DirectedHoTT.Spec.Typing
  using ( _⟶_; _⟶*_; done; step; β; βfst; βsnd; single )
open import DirectedHoTT.Metatheory.RedCong
  using ( ⟶*-trans; ⟶*-lam; ⟶*-appˡ; ⟶*-appʳ
        ; ⟶*-pairˡ; ⟶*-pairʳ; ⟶*-fst; ⟶*-snd )

-- a term together with a chain reaching it: SOUND BY CONSTRUCTION
Red : {Γ : Cx} → RTm Γ → Set
Red {Γ} t = Σ (RTm Γ) (λ u → t ⟶* u)

------------------------------------------------------------------------
-- ONE parallel pass: fire every β-redex, descend everywhere else.
------------------------------------------------------------------------

ev1 : {Γ : Cx} (t : RTm Γ) → Red t
ev1 (app (lam t) u)  = subTm (single u) t , step (β t u) done
ev1 (fst (pair a b)) = a , step (βfst a b) done
ev1 (snd (pair a b)) = b , step (βsnd a b) done
ev1 (lam t)   = let (t' , p) = ev1 t in lam t' , ⟶*-lam p
ev1 (app f a) = let (f' , pf) = ev1 f
                    (a' , pa) = ev1 a
                in app f' a' , ⟶*-trans (⟶*-appˡ pf) (⟶*-appʳ pa)
ev1 (pair a b) = let (a' , pa) = ev1 a
                     (b' , pb) = ev1 b
                 in pair a' b' , ⟶*-trans (⟶*-pairˡ pa) (⟶*-pairʳ pb)
ev1 (fst t) = let (t' , p) = ev1 t in fst t' , ⟶*-fst p
ev1 (snd t) = let (t' , p) = ev1 t in snd t' , ⟶*-snd p
ev1 t = t , done

------------------------------------------------------------------------
-- ★★★ SPINE-ONLY REDUCTION — fire β along the APPLICATION SPINE, and
--   NEVER descend into an argument.
--
-- ⚠⚠ MEASURED, and this is why it exists.  `evN` is a PARALLEL pass: it
--   also reduces inside arguments.  Feeding `evN 3` to the three-β
--   prologue closed `SzAgree` (29/29) and `PwAgree` and `StkAAgree`,
--   but BROKE `StkCAgree` and `PwBodyAgree` — `enTm y0 != …`,
--   `enVar y0 != …`.  Those rows' continuations expect the payload in
--   its UN-normalised form, and a parallel pass had already reduced it.
--   ⇒ OVER-REDUCTION IS A REAL FAILURE MODE, not a theoretical one.
--
-- ★ `evSpine` reduces exactly the head applications the ι-rule leaves
--   behind (`ifields` = three curried `app`s, §7) and touches nothing
--   else, so it cannot over-reduce an argument.
------------------------------------------------------------------------

evSpine1 : {Γ : Cx} (t : RTm Γ) → Red t
evSpine1 (app (lam t) u) = subTm (single u) t , step (β t u) done
evSpine1 (app f a)       = let (f' , p) = evSpine1 f in app f' a , ⟶*-appˡ p
evSpine1 t               = t , done

evSpine : {Γ : Cx} → ℕ → (t : RTm Γ) → Red t
evSpine zero    t = t , done
evSpine (suc n) t = let (u , p) = evSpine1 t
                        (v , q) = evSpine n u
                    in v , ⟶*-trans p q

------------------------------------------------------------------------
-- FUEL.  ⚠ Not a compromise: it COMPUTES, which is the entire point.
--   `snorm` (Fundamental:2008) says the bound exists -- PLAN-NF Phase 2.
------------------------------------------------------------------------

evN : {Γ : Cx} → ℕ → (t : RTm Γ) → Red t
evN zero    t = t , done
evN (suc n) t = let (u , p) = ev1 t
                    (v , q) = evN n u
                in v , ⟶*-trans p q

------------------------------------------------------------------------
-- ★★★ THE GATE: DOES IT COMPUTE?  If `evN` runs inside Agda's conversion
--   checker, an adequacy row becomes `refl` (§10.3).  If it is stuck,
--   this whole plan is wrong.
------------------------------------------------------------------------

val : {Γ : Cx} {t : RTm Γ} → Red t → RTm Γ
val (u , _) = u

-- ★ the chain, for feeding straight into an existing `⟶*` obligation.
chainOf : {Γ : Cx} {t : RTm Γ} (r : Red t) → t ⟶* val r
chainOf (_ , p) = p

-- `fst (pair (app (lam (var vz)) unit) unit)`
--   --βfst-->  app (lam (var vz)) unit
--   --β----->  unit
t0 : RTm ε
t0 = fst (pair (app (lam (var vz)) unit) unit)

runs-to-unit : val (evN 2 t0) ≡ unit
runs-to-unit = refl

-- nested under a binder and a pair, three redexes deep
t1 : RTm ε
t1 = snd (pair unit (fst (pair (app (lam (var vz)) unit) unit)))

runs-nested : val (evN 3 t1) ≡ unit
runs-nested = refl

-- ★ and the CHAIN comes out for free -- this is `⟶*`, not a claim
chain0 : {u : RTm ε} → Red t0
chain0 = evN 2 t0
