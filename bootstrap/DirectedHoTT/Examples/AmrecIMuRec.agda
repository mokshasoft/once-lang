------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ STEP 1b: THE STEP CALLS ITS IH ON A
-- SUBTERM OF THE SYNTAX.
--
-- `Examples/AmrecIMu` answered the INTERFACE question with a constant
-- step.  This one answers the honest version: the step SPLITS the
-- carrier and recurses.
--
-- ★★ THE ONE STRUCTURAL FACT THAT SHAPES EVERYTHING.  The carrier is a
--   SINGLE TYPE (`Tm 0`), so the only subterms the recursion may descend
--   into are the ones at the SAME index.  Of the three constructors:
--
--     var : Fin n → Tm n          no recursive field       — return 0
--     lam : Tm (suc n) → Tm n     field at a DIFFERENT type — return 0
--     app : Tm n → Tm n → Tm n    fields at the AMBIENT index — RECURSE
--
--   ⚠ `lam` is not a defect and not a gap: its body lives at depth 1, a
--   different type, and no measure recursion at a fixed carrier can
--   reach it.  That is precisely why step 2's family is indexed by
--   depth.  What IS testable at a fixed carrier is `app`, and that is
--   what this file tests.
--
-- ★★★ THE SPLIT IS AN `ielim` INSIDE THE `amrec` STEP, and the motive is
--   the shape `DivLib` uses for its `natrec`:
--
--       M  =  (ih : (y : Tm i) → size i y < size i s → Nat) → Nat
--
--   i.e. the two-slot motive over the INDEX `i` and the SCRUTINEE `s`,
--   whose value is "a function from the amrec IH to the answer".  The
--   step then reads: split first, take the IH second.
--
-- ⚠⚠ AND THE MOTIVE MUST MENTION THE INDEX SLOT.  Writing `nzero` for
--   the index throughout type-checks at the `⊢ielim` boundary — `iinst`
--   fixes the slot to `nzero` there either way — but makes the METHODS
--   unusable: §9.1's method QUANTIFIES over the index, so inside it
--   `app`'s fields are `Tm n` for a BOUND `n`, and an IH demanding
--   `Tm 0` cannot be applied to them.  This is "one method tuple serves
--   every recursive index" seen from the caller's side, and it is the
--   only place that design constrains a caller.
--
-- ★ WHAT THE RECURSIVE LEAF COSTS: ONE `⊢desc-app` (the object-language
--   arithmetic, in `Examples/ScopedSize`) and NOTHING ELSE — no cast at
--   all.  The `wk-single` residues one expects never appear, because
--   every index in sight is a VARIABLE by the time the payload's type
--   has been renamed into the method's context, and `single` on a
--   variable COMPUTES.  ⇒ the `subst` `Scoped.⊢tapp` pays is a cost of
--   building a term at a CONCRETE index, not of consuming one.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.AmrecIMuRec where
open import Agda.Builtin.Nat using ( zero; suc )
open import normalizer.Syntax.Types using ( _,_; Σ )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans; ⟶*-appˡ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( dρ-step )
open import DirectedHoTT.Lib.Amrec using ( aStepT; module AmTΠ )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; conₗ; methₗ; MethK; selF; selF-β; nth-z; nth-s
        ; PerK; []ₘ; _∷ₘ_; ⊢methₗ; ιₗ )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmTs; TmD; ⊢TmD; TmOK; varT; lamT; appT; varOK; lamOK; appOK
        ; Tm; size; ⊢size; toI; fromI; idTm; tapp )
open import DirectedHoTT.Examples.ScopedSize using ( appNode; descAppTm; ⊢desc-app )
open import DirectedHoTT.Examples.AmrecIMu using ( A; ⊢A; msr; ⊢msr )

------------------------------------------------------------------------
-- 1. THE `ielim` MOTIVE — "a function from the amrec IH to the answer",
--    at an ARBITRARY index `i` and scrutinee `s`.
------------------------------------------------------------------------

-- `(y : Tm i) → size i y < size i s → El ⌜Nat⌝`
ihT : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
ihT i s =
  Π (IMu ⌜Nat⌝ TmD i)
    (Π (Hom Nat (nsuc (size (renTm vs i) (var vz)))
                (size (renTm vs i) (renTm vs s)))
       (El ⌜Nat⌝))

⊢ihT : {Γ : Ctx} {i s : RTm ⌊ Γ ⌋} →
       Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ s ∷ Tm i → Γ ⊢ty ihT i s
⊢ihT di ds =
  ty-Π (ty-IMu ⊢⌜Nat⌝ ⊢TmD di)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢size (⊢wk di) (⊢var here)))
                         (⊢size (⊢wk di) (⊢wk ds)))
          (ty-El ⊢⌜Nat⌝))

MotAt : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
MotAt i s = Π (ihT i s) (El ⌜Nat⌝)

-- ★ the two-slot motive: index = `var (vs vz)`, scrutinee = `var vz`.
Mot : {Γ : Cx} → RTy ((Γ ∙) ∙)
Mot = MotAt (var (vs vz)) (var vz)

⊢Mot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ IMu ⌜Nat⌝ TmD (var vz)) ⊢ty Mot
⊢Mot = ty-Π (⊢ihT (⊢var (there here)) (⊢var here)) (ty-El ⊢⌜Nat⌝)

------------------------------------------------------------------------
-- 2. THE THREE METHODS, each against its hypotheses' NORMAL FORM.
--
-- Each is FOUR binders — the index, the payload, the structural
-- hypotheses, and then the amrec IH the motive's codomain asks for.
-- ★ D074: `app`'s fields sit at the fibre's OWN index `i`, so the amrec
--   IH (at `Tm i`) applies to them as they are — no transport.
------------------------------------------------------------------------

mVar mLam mApp : {Γ : Cx} → RTm Γ
mVar = lam (lam (lam (lam nzero)))
mLam = lam (lam (lam (lam nzero)))
mApp = lam (lam (lam (lam
         (app (app (var vz) (fst (var (vs (vs vz)))))
              (descAppTm (var (vs (vs (vs vz)))) (var (vs (vs vz))))))))

-- ⚠ EACH PIECE AT ITS OWN NAMED TYPE.  Written as one expression, the
--   unifier solves the pieces' types against the UNFOLDED description and
--   motive — measured 66 s / 4.4 GB for `var`'s method alone; with every
--   intermediate typed by a named lemma it is well under a second.  (The
--   Def-backed-name lesson again: a name shares, an inferred meta re-runs.)

-- the method's context for constructor `T`, and its scrutinee
HC : (Γ : Ctx) → Tel (⌊ Γ ⌋ ∙) → Ctx
HC Γ T = HypCtx Γ ⌜Nat⌝ TmD Mot T

-- `var`
scrV : {Γ : Ctx} → HC Γ varT ⊢ conₗ zero (var (vs vz)) ∷ Tm (var (vs (vs vz)))
scrV = ⊢conₜ ⊢⌜Nat⌝ TmOK nthᵗ-z (⊢var (there (there here))) (⊢var (there here))

bodyV : {Γ : Ctx} → HC Γ varT ⊢ lam nzero ∷ MotAt (var (vs (vs vz))) (conₗ zero (var (vs vz)))
bodyV = ⊢lam (⊢ihT (⊢var (there (there here))) scrV) (toI ⊢nzero)

⊢mVar : {Γ : Ctx} → Γ ⊢ mVar ∷ MethK ⌜Nat⌝ TmD Mot ⌜ varT ⌝ᵗ zero
⊢mVar = ⊢methT {T = varT} {s = conₗ zero (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢Mot varOK bodyV

-- `lam`: its body is at `suc i`, a DIFFERENT type — no amrec call
scrL : {Γ : Ctx} → HC Γ lamT ⊢ conₗ (suc zero) (var (vs vz)) ∷ Tm (var (vs (vs vz)))
scrL = ⊢conₜ ⊢⌜Nat⌝ TmOK (nthᵗ-s nthᵗ-z) (⊢var (there (there here))) (⊢var (there here))

bodyL : {Γ : Ctx} → HC Γ lamT ⊢ lam nzero ∷ MotAt (var (vs (vs vz))) (conₗ (suc zero) (var (vs vz)))
bodyL = ⊢lam (⊢ihT (⊢var (there (there here))) scrL) (toI ⊢nzero)

⊢mLam : {Γ : Ctx} → Γ ⊢ mLam ∷ MethK ⌜Nat⌝ TmD Mot ⌜ lamT ⌝ᵗ (suc zero)
⊢mLam = ⊢methT {T = lamT} {s = conₗ (suc zero) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢Mot lamOK bodyL

-- ★★★ `app`: THE RECURSIVE LEAF — the amrec IH at the first field, with
--   the descent certificate.
scrA : {Γ : Ctx} → HC Γ appT ⊢ conₗ (suc (suc zero)) (var (vs vz)) ∷ Tm (var (vs (vs vz)))
scrA = ⊢conₜ ⊢⌜Nat⌝ TmOK (nthᵗ-s (nthᵗ-s nthᵗ-z)) (⊢var (there (there here))) (⊢var (there here))

-- the context under the amrec IH's binder
HCA : Ctx → Ctx
HCA Γ = HC Γ appT ▹ ihT (var (vs (vs vz))) (conₗ (suc (suc zero)) (var (vs vz)))

-- the payload's two recursive fields, at the fibre's own index
fstA : {Γ : Ctx} → HCA Γ ⊢ fst (var (vs (vs vz))) ∷ Tm (var (vs (vs (vs vz))))
fstA = Σ.fst (Σ.snd (Σ.snd (dρ-step dC (⊢var (there (there here))))))
  where dC = ⊢tel ⊢⌜Nat⌝ (ok-ρ (⊢var (there (there (there here)))) (ok-ρ (⊢var (there (there (there here)))) ok-ι))

sndA : {Γ : Ctx} → HCA Γ ⊢ fst (snd (var (vs (vs vz)))) ∷ Tm (var (vs (vs (vs vz))))
sndA = Σ.fst (Σ.snd (Σ.snd (dρ-step (Σ.fst (Σ.snd s₁)) (Σ.snd (Σ.snd (Σ.snd s₁))))))
  where
    dC = ⊢tel ⊢⌜Nat⌝ (ok-ρ (⊢var (there (there (there here)))) (ok-ρ (⊢var (there (there (there here)))) ok-ι))
    s₁ = dρ-step dC (⊢var (there (there here)))

callA : {Γ : Ctx} → HCA Γ ⊢ app (app (var vz) (fst (var (vs (vs vz)))))
                              (descAppTm (var (vs (vs (vs vz)))) (var (vs (vs vz))))
                        ∷ El ⌜Nat⌝
callA = ⊢app (⊢app (⊢var here) fstA) (⊢desc-app (⊢var (there (there (there here)))) fstA sndA)

bodyA : {Γ : Ctx} → HC Γ appT ⊢ lam (app (app (var vz) (fst (var (vs (vs vz)))))
                                      (descAppTm (var (vs (vs (vs vz)))) (var (vs (vs vz)))))
                              ∷ MotAt (var (vs (vs vz))) (conₗ (suc (suc zero)) (var (vs vz)))
bodyA = ⊢lam (⊢ihT (⊢var (there (there here))) scrA) callA

⊢mApp : {Γ : Ctx} → Γ ⊢ mApp ∷ MethK ⌜Nat⌝ TmD Mot ⌜ appT ⌝ᵗ (suc (suc zero))
⊢mApp = ⊢methT {T = appT} {s = conₗ (suc (suc zero)) (var (vs vz))} ⊢⌜Nat⌝ ⊢TmD ⊢Mot appOK bodyA

------------------------------------------------------------------------
-- 3. THE ONE METHOD, AND THE STEP.
------------------------------------------------------------------------

RecMs : {Γ : Cx} → Cons Γ 3
RecMs = mVar ∷ (mLam ∷ (mApp ∷ []))

mRecs : {Γ : Cx} → RTm Γ
mRecs = methₗ RecMs

⊢mRecs : {Γ : Ctx} → Γ ⊢ mRecs ∷ MethTy ⌜Nat⌝ TmD Mot
⊢mRecs = ⊢methₗ ⊢⌜Nat⌝ (allD (⊢wk ⊢⌜Nat⌝) TmOK) ⊢Mot
           ( (selF-β {Cs = ⌜ TmTs ⌝ₛ} nth-z , ⊢mVar)
          ∷ₘ ((selF-β {Cs = ⌜ TmTs ⌝ₛ} (nth-s nth-z) , ⊢mLam)
          ∷ₘ ((selF-β {Cs = ⌜ TmTs ⌝ₛ} (nth-s (nth-s nth-z)) , ⊢mApp) ∷ₘ []ₘ)))

-- ★ SPLIT FIRST, TAKE THE IH SECOND — `DivLib`'s `lam (natrec …)` with
--   the `natrec` replaced by an `ielim` over the syntax.
stpR : RTm ε
stpR = lam (ielim TmD nzero mRecs (var vz))

⊢stpR : ◇ ⊢ stpR ∷ aStepT A ⌜Nat⌝ msr
⊢stpR = ⊢lam ⊢A (⊢ielim ⊢⌜Nat⌝ ⊢TmD ⊢Mot ⊢mRecs (toI ⊢nzero) (⊢var here))

------------------------------------------------------------------------
-- 4. ★★★ THE USE SITE.
------------------------------------------------------------------------

open AmTΠ ◇ A ⌜Nat⌝ msr stpR ⊢A ⊢⌜Nat⌝ ⊢msr ⊢stpR
  using ( amrecTm; ⊢amrecΠ )

amrecTmR : RTm ε
amrecTmR = amrecTm

-- ★★★ `◇ ⊢ amrecTm ∷ Π (Tm 0) (El ⌜Nat⌝)`, with a step that RECURSES.
⊢amrecTmR : ◇ ⊢ amrecTmR ∷ Π (Tm nzero) (El ⌜Nat⌝)
⊢amrecTmR = ⊢amrecΠ

------------------------------------------------------------------------
-- 5. ★★★ …AND THE RECURSIVE CALL IS REACHED.  THE FORCING RUNG.
--
-- ⚠ THE PAYLOAD IS CONCRETE HERE, and for a reason worth recording: at
--   an ABSTRACT `p` the two inner binders leave `subTm … (w (w p))`
--   where the statement wants `p`, and the descent WITNESS `descAppTm`
--   does not commute with substitution definitionally either — it hides
--   a `w` inside `trHomˡ`, exactly the residue `ArithComm`'s
--   substitution-naturality section exists to absorb.  Closing that at
--   an abstract payload is a naturality chain (`trHomˡ-sub`,
--   `plus0Tm-sub`, …) and buys nothing this rung needs: `⊢desc-app` is
--   already proved at an abstract `p`, which is where it matters.
--
-- ⚠ WHY A SEPARATE LEMMA AND NOT `amrec-step-s`.  That combinator's
--   continuation is `(ih : RTm ⌊ Δ ⌋) → app (app stp x) ih ⟶* P` with
--   `P` FIXED — the IH is passed in continuation position precisely so
--   the answer may not mention it.  A step that RECURSES produces an
--   answer that does mention it, which is the same fact `Lib/Amrec`'s
--   own note records: a recursive call never lands back on `amrecTm`, it
--   lands on `auxIH x k`, and chaining it needs the re-entrant
--   `aux-step-s` layer.  Not attempted here.
--
-- ★ WHAT IS SHOWN instead is the half that is about THIS step: at an
--   `app` node the assembled `ielim` selects the third method and
--   delivers the IH APPLIED TO `fst p` with the descent certificate —
--   nine steps, one `ι-ielim`, three to select the method, five βs.  So
--   the recursive call is not merely well-typed, it is REACHED.
------------------------------------------------------------------------

-- the payload of `(λx. x) (λx. x)`, CONCRETE — see the note below.
selfPay : RTm ε
selfPay = pair idTm (pair idTm unit)

stpR-app : (ih : RTm ε) →
           app (app stpR (tapp idTm idTm)) ih
             ⟶* app (app ih (fst selfPay)) (descAppTm nzero selfPay)
stpR-app ih =
  step (ξ-appˡ (β _ (tapp idTm idTm)))
  (⟶*-trans (⟶*-appˡ (ιₗ {D = TmD} {i = nzero} {p = selfPay} {ms = RecMs} (nth-s (nth-s nth-z))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (β _ nzero))))
  (step (ξ-appˡ (ξ-appˡ (β _ selfPay)))
  (step (ξ-appˡ (β _ _))
  (step (β _ ih) done)))))
