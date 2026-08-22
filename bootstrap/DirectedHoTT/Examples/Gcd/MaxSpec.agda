------------------------------------------------------------------------
-- DirectedHoTT · EXAMPLES — ★★★★★★★ gcd IS THE GREATEST COMMON DIVISOR.
--
--       ∀ e.  e ∣ a  →  e ∣ b  →  e ∣ gcd (a , b)
--
--   at an ARBITRARY pair, through `amrec-ind`.
--
-- ★★ THIS IS `amrec-ind`'s SECOND CUSTOMER, AND IT IS STRUCTURALLY
--   DIFFERENT FROM THE FIRST.  Divisibility (`Gcd/Spec`) is a `⌜Σ⌝`
--   motive whose leaves PROJECT the induction hypothesis' two conjuncts;
--   maximality is a `⌜Π⌝` motive whose leaves DECODE the hypothesis to a
--   function type and APPLY it.  Nothing about that difference reaches the
--   plumbing.
--
-- ★ WHAT THIS FILE SUPPLIES, and it is the whole point: the STATEMENT and
--   the `amrecInd` call.  `IndStep` comes from `Plumb maxMotive` — the
--   same three nested `natrec`s, four leaves and two split-boundary
--   conversions that `Plumb dvdMotive` gives divisibility.  The customer
--   contributed six facts about `MaxCode` and four leaf derivations, in
--   `Lib/Max` and `Examples/Gcd/Motives`, and nothing else.
--
-- ⚠ `StepExt` is SHARED with divisibility — `gcdStepExt` is a fact about
--   gcd's STEP, not about either motive, so it is proved once (gap A) and
--   spent twice.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Gcd.MaxSpec where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; vz; vs; RTm; El; var; fst; snd; app; ⌜Nat⌝; subTm; Nat )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; single; _⊢_∷_; ⊢⌜Nat⌝; wk-single )
open import DirectedHoTT.Lib.Pair using ( PairT; ⊢PairT )
open import DirectedHoTT.Lib.Max
  using ( MaxCode; ⊢MaxCode; MaxCode-sub; MaxT; El-max; ⊢MaxElim )
open import DirectedHoTT.Lib.Dvd using ( dvdT )
open import DirectedHoTT.Spec.Typing using ( ⊢conv )
open import DirectedHoTT.Metatheory.Injectivity using ( red→≅ᵀ )
open import DirectedHoTT.Lib.Amrec using ( Prv; prv; prvOk; prv-cast )
open import DirectedHoTT.Lib.AmrecInd using ( module Concl )
open import DirectedHoTT.Examples.Gcd.Step using ( msr; ⊢msr; gcdStp; ⊢gcdStp )
open import DirectedHoTT.Examples.Gcd.StepExtA using ( gcdStepExt )
open import DirectedHoTT.Examples.Gcd.Motives using ( maxMotive; module MaxPlumb )

module MaxC (Δ : Ctx) = Concl Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp

-- gcd itself — re-exported from the one instantiation (see Gcd/Spec).
gcdTm : (Δ : Ctx) → RTm ⌊ Δ ⌋
gcdTm Δ = MaxC.amrecTm Δ

-- ⚠ the last peel, exactly as in `Gcd/Spec`: `amrec-ind` states its
--   conclusion through `IndAt`, which fills the RESULT slot with
--   `valAt = app (w amrec) (var vz)`.
IndAt-max : {Δ : Ctx} (x : RTm ⌊ Δ ⌋) →
            MaxC.IndAt Δ MaxPlumb.gP x
          ≡ El (MaxCode (fst x) (snd x) (app (gcdTm Δ) x))
IndAt-max {Δ} x =
  cong El
    (trans (cong (subTm (single x))
                 (MaxCode-sub {σ = single (MaxC.valAt Δ)}
                    (fst (var (vs vz))) (snd (var (vs vz))) (var vz)))
           (trans (MaxCode-sub {σ = single x}
                     (fst (var vz)) (snd (var vz)) (MaxC.valAt Δ))
                  (cong (λ t → MaxCode (fst x) (snd x) (app t x))
                        (wk-single {v = x} (gcdTm Δ)))))

------------------------------------------------------------------------
-- ★★★★★★★ THE THEOREM.
------------------------------------------------------------------------

gcdMax : {Δ : Ctx} {x : RTm ⌊ Δ ⌋} → Δ ⊢ x ∷ PairT →
         Prv Δ (El (MaxCode (fst x) (snd x) (app (gcdTm Δ) x)))
gcdMax {Δ} {x} dx =
  prv-cast (IndAt-max x)
           (MaxC.amrecInd Δ gcdStepExt MaxPlumb.⊢gP MaxPlumb.indStep dx)

------------------------------------------------------------------------
-- ★★ …AND ELIMINATED, which is the half that makes it a THEOREM YOU CAN
--    USE rather than one you can merely state.
--
-- ⚠ `gcdMax` above produces `El (MaxCode …)` — a CODE.  `⊢MaxElim` wants
--   the decoded `MaxT`, so `El-max` bridges them.  Without this, `Lib/Max`'s
--   `⊢MaxElim` has NO CLIENT and maximality is `lexrec` all over again:
--   derived, green, `--safe`, and never applied to anything.
--   (Standing rule: every library branch is exercised by an Example.)
------------------------------------------------------------------------

-- ⚠⚠ RETURNS `Prv`, AND THAT IS NOT COSMETIC.  Stating the conclusion as
--   `Δ ⊢ app (app (app _ e) h₁) h₂ ∷ dvdT …` OOM-KILLED the module (220s,
--   uncontended, under `-c`): the `_` must be solved to the ENTIRE
--   `amrec-ind` proof term, and Agda then carries that term inside the
--   TYPE, under three applications.  `Prv` is the named existential that
--   exists to stop exactly this — the term is packaged, not stated.
--   ⭐ `gcdSpec` returns `Prv` for the same reason; `gcd∣fst`/`gcd∣snd`
--     get away with `fst _` only because one constructor is cheap.
gcdGreatest : {Δ : Ctx} {x e h₁ h₂ : RTm ⌊ Δ ⌋} →
              Δ ⊢ x ∷ PairT → Δ ⊢ e ∷ Nat →
              Δ ⊢ h₁ ∷ dvdT e (fst x) → Δ ⊢ h₂ ∷ dvdT e (snd x) →
              Prv Δ (dvdT e (app (gcdTm Δ) x))
gcdGreatest {Δ} {x} dx de d1 d2 =
  prv _ (⊢MaxElim (⊢conv (prvOk (gcdMax dx))
                         (red→≅ᵀ (El-max (fst x) (snd x) (app (gcdTm Δ) x))))
                  de d1 d2)
