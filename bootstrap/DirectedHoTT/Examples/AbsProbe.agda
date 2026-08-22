------------------------------------------------------------------------
-- OCP-0009 — WHERE THE `irrAt` COST LIVES, AND THE ONE REMEDY THAT WORKS.
--
-- ★ THE TECHNIQUE.  Vary a candidate cause by making it a MODULE PARAMETER
--   — a variable Agda cannot unfold — rather than by supplying a somewhat
--   larger concrete term.  `IrrProbe` rung 2 did the latter and returned a
--   null that retired the CORRECT mechanism for half a day.
--
-- ★★ THE LADDER.  Same `irrSplit` rung throughout (one split combining two
--    ex-falso leaves), cold, differing only in what is abstract:
--
--      variant   stp        ext          total    marginal
--      ------------------------------------------------------
--      (Q)       ABSTRACT   ABSTRACT      5.4s    —  (overhead)
--      (R)       ABSTRACT   ABSTRACT      7.1s    1.7s   ← THIS MODULE
--                then INSTANTIATED at gcdStp and FORCED
--      (P)       gcdStp     ABSTRACT     17.5s   12.1s
--      (A)       gcdStp     gcdStepExt   15.3s    9.9s
--
-- ⇒ THE EXT PROOF IS NOT THE COST.  (P) removes it entirely and the number
--   does not move.  Shrinking `gcdStepExt` — ~600 lines over ten modules —
--   would have bought NOTHING.  That target is retired.
--
-- ⇒ THE COST IS THE CONCRETE STEP TERM, IN THE TYPE.  `irrT` mentions
--   `auxAt`, `auxAt` mentions `auxS x`, `auxS` carries the step.  In (P)
--   there are no expensive proof VALUES left at all, yet merely stating and
--   converting `irrT θ x y n₁ n₂` at a concrete `gcdStp` costs 17.5s.
--
-- ⭐ AND THE REMEDY MEASURES POSITIVE — the first one that has.  Check the
--   assembly ONCE at an abstract step, then instantiate: marginal cost
--   falls 9.9s → 1.7s, ~5.8×.  This is NOT the opacity family: nothing is
--   asked to refrain from unfolding; the expensive elaboration simply
--   happens once, generically, instead of at every concrete use.
--
-- ⚠ WHAT THIS DOES NOT SHOW.  This rung is ONE `irrSplit` over two ex-falso
--   leaves.  `irr-ind` is two `irrSplit`s, four leaves and an outer
--   `⊢natrec`.  A 5.8× on the rung does not by itself turn `irrAt`'s OOM
--   green — it establishes DIRECTION, not sufficiency.
--
-- ★ THE THREE FORCING RUNGS, weakest to strongest.  `forced` states the
--   concrete type and `forcedOk` projects with `prvOk`, but BOTH may unify
--   syntactically without evaluating.  `forcedApp` is `⊢app (prvOk …)` with
--   its result type left as `_`, so there is no ascription to match against
--   and Agda must whnf the type to a `Π` and substitute.  It is the only
--   one of the three that cannot dodge the work.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AbsProbe where
open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTy; El; Id; RTm; app; ⌜Nat⌝
        ; Ren; renTm; renTy; subTm; subTy; extR; nrs )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; _⊢_∷_; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( Ren⊢ )
open import DirectedHoTT.Lib.Rec using ( aIHTat )
open import DirectedHoTT.Lib.Amrec using ( prvTm; prvOk; StepPW )
open import DirectedHoTT.Lib.Pair using ( PairT )
open import DirectedHoTT.Examples.Gcd.Step using ( gcdStp; msr )
open import DirectedHoTT.Examples.Gcd.StepExtA using ( gcdStepExt )
open import DirectedHoTT.Lib.Amrec using ( module AmTΠ; Prv; wR )
open import DirectedHoTT.Spec.Typing using ( ◇; _⊢ty_; ⊢nzero; ⊢nsuc; ⊢var; here; there )
open import DirectedHoTT.Spec.Syntax using ( nzero; nsuc; var; vs; vz; Π; Nat )
open import DirectedHoTT.Lib.Wk using ( w )
open import DirectedHoTT.Lib.Pair using ( ⊢PairT )
open import DirectedHoTT.Spec.Typing using ( ⊢⌜Nat⌝ )
open import DirectedHoTT.Examples.Gcd.Step using ( ⊢msr; ⊢gcdStp )
open import DirectedHoTT.Lib.Amrec using ( StepExt; aStepT )
open import DirectedHoTT.Spec.Typing using ( ⊢app )

-- ★ HoistQ's module VERBATIM: the assembly checked once at an ABSTRACT
--   step (measured 5.4s = bare overhead).
module LeafAt (Δ : Ctx) (stp : RTm ⌊ Δ ⌋)
              (⊢stp : Δ ⊢ stp ∷ aStepT PairT ⌜Nat⌝ msr)
              (ext : StepExt Δ PairT ⌜Nat⌝ msr stp) where

  open AmTΠ Δ PairT ⌜Nat⌝ msr stp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢stp public
    using ( irr-zz; irr-zs; irrT; vsθ; irrSplit )

  splitZP : {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT) →
            Prv (Δ ▹ Nat) (irrT vs x y nzero (var vz))
  splitZP dx dy =
    irrSplit there dx dy ⊢nzero
             (irr-zz ext there dx dy)
             (irr-zs ext (wR (wR there)) dx dy (⊢var (there here)))

------------------------------------------------------------------------
-- ★★★ THE MILESTONE: INSTANTIATE THAT ABSTRACT ASSEMBLY AT `gcdStp`.
--
--   HoistQ (abstract, never instantiated)   5.4s
--   HoistA (assembly checked AT gcdStp)    15.3s
--
--   If this lands near 5s, the refactor WINS: the assembly is checked once
--   generically and instantiation is cheap.  If it lands near 17s, the
--   instantiation re-pays the whole cost and abstracting the slots buys
--   NOTHING — which kills the plan before `LibAmrec` is touched.
------------------------------------------------------------------------

module Inst (Δ : Ctx) where

  open LeafAt Δ gcdStp ⊢gcdStp gcdStepExt public

  forced : {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT) →
           Prv (Δ ▹ Nat) (irrT vs x y nzero (var vz))
  forced dx dy = splitZP dx dy

  -- ⚠ `forced` alone may NOT force: it matches the same generic Def applied
  --   to the same args, which is syntactic.  `prvOk` PATTERN-MATCHES on
  --   `Prv`, which is what `irrAt` really does — this is the honest rung.
  forcedOk : {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT) →
             (Δ ▹ Nat) ⊢ prvTm (splitZP dx dy) ∷ irrT vs x y nzero (var vz)
  forcedOk dx dy = prvOk (splitZP dx dy)

  -- ★★ THE REAL CLIENT SHAPE.  `irrAt` is `⊢app (prvOk (irr-ind …)) n₂`.
  --    An `⊢app` must whnf the function's type to a `Π` and SUBSTITUTE into
  --    its codomain — that is the work `forced`/`forcedOk` might dodge by
  --    unifying syntactically.  This one cannot dodge it.
  forcedApp : {x y : RTm ⌊ Δ ⌋} {a : RTm (⌊ Δ ⌋ ∙)}
              (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
              (da : (Δ ▹ Nat) ⊢ a ∷ renTy vs PairT) → _
  forcedApp dx dy da = ⊢app (prvOk (splitZP dx dy)) da
