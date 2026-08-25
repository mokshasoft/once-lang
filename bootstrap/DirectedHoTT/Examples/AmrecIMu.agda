------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `⊢amrec` AT AN `IMu` CARRIER.
--
-- HANDOFF-2026-08-25 step 1a.  ARCHITECTURE.md asserts that `⊢amrec`
-- applies to `prog`/`usplit`/`trS`/`ordtrS` "VERBATIM the moment `RTm` is
-- a kernel type and `sz` is definable".  Both preconditions are met —
-- `Examples/Scoped` is a syntax as an indexed description and `size` is
-- an `ielim` over it — but NOTHING HAD TESTED THE CLAIM.  This file is
-- the smallest thing that does, at a scale that fits one session and
-- before 53 constructors are riding on it.
--
--     A  := Tm 0                     an `IMu`, not a `Nat` and not a `Σ'`
--     cM := ⌜Nat⌝                    the CONSTANT motive
--     m  := size 0 x                 an `ielim`, under the carrier binder
--     stp                            ignores its IH and returns 0
--
-- ★ WHAT IS AND IS NOT SETTLED HERE, stated precisely.  The step term is
--   CONSTANT, so nothing below shows a recursive call descending a
--   syntax.  That is step 1b, and it needs `size f < size (app f a)` IN
--   THE OBJECT LANGUAGE (`Lib/ArithLe`).  What a constant step CANNOT
--   dodge is the interface question itself: `AmTΠ` must accept a carrier
--   that is an `IMu` and a measure that is an `ielim`, and it must build
--   its auxiliary's `natrec` spine over them.  That is what this checks.
--
-- ⚠ AND IT NEEDED ONE EDIT UPSTREAM, already located by the handoff:
--   `Scoped.⊢msize`/`⊢size` were pinned at `◇`, but `AmTΠ`'s measure
--   premise is `dm : (Δ ▹ A) ⊢ m ∷ Nat` — typed UNDER the carrier's
--   binder.  Their components were `{Γ : Ctx}`-generic already, so
--   generalising the two assembled forms was a signature change and not
--   a proof.
--
-- ★★ RESULT.  The instantiation is the DivLib shape unchanged: four
--   data, four derivations, one `open`.  The carrier being an inductive
--   FAMILY costs nothing at the interface — `renTy ρ (IMu D I i) =
--   IMu D I (renTm ρ i)` and `D`/`I` are closed, so every weakening the
--   combinator performs on the carrier is the identity on the
--   description and moves only the index.  ⇒ ARCHITECTURE.md's "VERBATIM"
--   holds for the CARRIER; §12–§14 already settled the description side.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AmrecIMu where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Nat; U
        ; RTm; var; lam; app; nzero; nsuc; ⌜Nat⌝
        ; Π; subTy; renTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢⌜Nat⌝
        ; _⊢ty_; ty-Nat; ty-Hom; ty-El; ty-Π; ty-IMu
        ; _⟶*_; done; step; β; ξ-appˡ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk; ren-ty )
open import DirectedHoTT.Lib.Wk    using ( ⊢wkᶠ )
open import DirectedHoTT.Lib.Rec   using ( aIHT )
open import DirectedHoTT.Lib.Amrec using ( aStepT; module AmTΠ )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; size; ⊢size; toI; idTm; ⊢idTm; size-id )

------------------------------------------------------------------------
-- 1. THE CARRIER — a closed instance of the indexed family.
--
-- ⚠ `Tm nzero`, not `Tm n` for a variable `n`.  `AmTΠ`'s carrier is a
--   SINGLE TYPE (`A : RTy ⌊ Δ ⌋`), and an indexed family is not one.
--   Pinning the index is exactly what the handoff checked item 7 does
--   NOT need to go beyond: `prog`/`usplit` live at `RTm ε` outright.
------------------------------------------------------------------------

A : RTy ε
A = Tm nzero

⊢A : ◇ ⊢ty A
⊢A = ty-IMu TmWf (toI ⊢nzero)

------------------------------------------------------------------------
-- 2. THE MEASURE — an `ielim`, at the carrier's binder.
--
-- ★ This is the slot the whole file exists to fill.  Under `AmTΠ` the
--   measure is PRE-APPLIED: `m : RTm (⌊ Δ ⌋ ∙)` with `dm` at `Δ ▹ A`, so
--   `μ x` IS `m` with no `app` and no β-redex.  Here that reads
--   `size 0 x` for the carrier variable `x` — the recursor over the
--   syntax, run at the ambient index.
------------------------------------------------------------------------

msr : RTm (ε ∙)
msr = size nzero (var vz)

⊢msr : (◇ ▹ A) ⊢ msr ∷ Nat
⊢msr = ⊢size (toI ⊢nzero) (⊢var here)

------------------------------------------------------------------------
-- 3. THE IH TYPE AND THE STEP.
--
-- `aIHT A ⌜Nat⌝ msr = (y : Tm 0) → size 0 y < size 0 x → El ⌜Nat⌝`, and
-- it types by the `⊢gcdIH` idiom: `⊢wkᶠ` for the measure at the INNER
-- binder (the family keeps pointing at its own carrier) and `⊢wk` for it
-- at the outer one.
--
-- ⚠ `⊢wkᶠ`, not `⊢wk`, for the first — the two produce terms that look
--   interchangeable and are not (Lib/Wk's P1).
------------------------------------------------------------------------

⊢ihT : (◇ ▹ A) ⊢ty aIHT A ⌜Nat⌝ msr
⊢ihT =
  ty-Π (ren-ty ⊢A there)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢wkᶠ ⊢msr)) (⊢wk ⊢msr))
          (ty-El ⊢⌜Nat⌝))

-- the CONSTANT step: takes the carrier and the IH, ignores both.
stp : RTm ε
stp = lam (lam nzero)

⊢stp : ◇ ⊢ stp ∷ aStepT A ⌜Nat⌝ msr
⊢stp = ⊢lam ⊢A (⊢lam ⊢ihT (toI ⊢nzero))

------------------------------------------------------------------------
-- 4. ★★★ THE USE SITE — one `open`, and the claim is tested.
------------------------------------------------------------------------

open AmTΠ ◇ A ⌜Nat⌝ msr stp ⊢A ⊢⌜Nat⌝ ⊢msr ⊢stp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt; amrec-step-s )

amrecTmT : RTm ε
amrecTmT = amrecTm

-- ★★★ THE MILESTONE: `◇ ⊢ amrecTm ∷ Π (Tm 0) (El ⌜Nat⌝)`.
⊢amrecTmT : ◇ ⊢ amrecTmT ∷ Π (Tm nzero) (El ⌜Nat⌝)
⊢amrecTmT = ⊢amrecΠ

-- ★ and POINTWISE at a real inhabitant of the family — `λx. x`, the
--   smallest term that uses the binder shift.  No cast at the use site.
⊢amrecTmT-at : ◇ ⊢ app amrecTmT idTm ∷ subTy (single idTm) (El ⌜Nat⌝)
⊢amrecTmT-at = ⊢amrecPt ⊢idTm

------------------------------------------------------------------------
-- 5. ★★★ …AND IT RUNS.  THE FORCING RUNG.
--
-- ⚠ WHY THIS AND NOT THE TWO ASCRIPTIONS ABOVE.  `⊢amrecΠ` and
--   `⊢amrecPt` are ascribed to the types the module already states, so
--   Agda MAY discharge them by unifying the same `Def` against the same
--   arguments — `AbsProbe`'s point about `forced`/`forcedOk`.  A REDUCTION
--   cannot dodge: `amrec-step-s`'s premise is
--   `subTm (single x) m ⟶* nsuc k`, and supplying `Scoped.size-id` for it
--   forces the substitution INTO the measure to compute, i.e. forces
--   `subTm (single idTm) (ielim TmD 0 msize (var vz))` to become
--   `size 0 idTm` — the exact place an `ielim` measure could have failed
--   to be one.
--
-- ★ THE RUN.  `size 0 (λx. x) ⟶* 2`, so the auxiliary peels at the
--   bound `suc 1` and hands the step its IH; the step is constant, so the
--   answer is `0`.  Trivial arithmetic, non-trivial plumbing: this is the
--   combinator DRIVING ITS `natrec` SPINE off a recursor over an indexed
--   family.
--
-- ⇒ step 1a is answered YES: `AmTΠ` accepts an `IMu` carrier and an
--   `ielim` measure, and computes with them.  What remains untested is
--   the RECURSIVE step (1b) — `size f < size (app f a)` in the object
--   language, from `Lib/ArithLe`.
------------------------------------------------------------------------

-- the constant step, run: `app (app stp idTm) ih ⟶* 0`, for ANY `ih`.
stp-run : (ih : RTm ε) → app (app stp idTm) ih ⟶* nzero
stp-run ih = step (ξ-appˡ (β (lam nzero) idTm)) (step (β nzero ih) done)

-- ★★★ `amrec (λx. x) ⟶* 0`, through a measure that is an `ielim`.
run-idTm : app amrecTmT idTm ⟶* nzero
run-idTm = amrec-step-s idTm (nsuc nzero) size-id stp-run
