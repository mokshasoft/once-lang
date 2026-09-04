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
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; IMu
        ; RTm; var; lam; app; pair; fst; snd; unit; nzero; nsuc; ⌜Nat⌝
        ; icon; ielim; renTm; Π
        ; hereID; thereID )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc; ⊢lam; ⊢app
        ; _⟶*_; done; step; β; βfst; βsnd; ξ-appˡ; ξ-fst; ξ-snd; ι-ielim
        ; ⊢pair; ⊢fst; ⊢snd; ⊢unit; ⊢⌜Nat⌝; ⊢icon; ⊢ielim
        ; imethTy; imethsTy
        ; _⊢ty_; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Σ; ty-Unit; ty-IMu )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk )
open import DirectedHoTT.Lib.Amrec using ( aStepT; module AmTΠ )
open import DirectedHoTT.Examples.Scoped
  using ( INat; TmD; TmWf; Tm; size; ⊢size; toI; fromI
        ; varC; lamC; appC; tyPayVar; tyPayLam; tyPayApp
        ; idTm; tapp )
open import DirectedHoTT.Examples.ScopedSize using ( appNode; descAppTm; ⊢desc-app )
open import DirectedHoTT.Examples.AmrecIMu using ( A; ⊢A; msr; ⊢msr )

------------------------------------------------------------------------
-- 1. THE `ielim` MOTIVE — "a function from the amrec IH to the answer",
--    at an ARBITRARY index `i` and scrutinee `s`.
------------------------------------------------------------------------

-- `(y : Tm i) → size i y < size i s → El ⌜Nat⌝`
ihT : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
ihT i s =
  Π (IMu TmD INat i)
    (Π (Hom Nat (nsuc (size (renTm vs i) (var vz)))
                (size (renTm vs i) (renTm vs s)))
       (El ⌜Nat⌝))

⊢ihT : {Γ : Ctx} {i s : RTm ⌊ Γ ⌋} →
       Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ s ∷ Tm i → Γ ⊢ty ihT i s
⊢ihT di ds =
  ty-Π (ty-IMu TmWf di)
    (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢size (⊢wk di) (⊢var here)))
                         (⊢size (⊢wk di) (⊢wk ds)))
          (ty-El ⊢⌜Nat⌝))

MotAt : {Γ : Cx} → RTm Γ → RTm Γ → RTy Γ
MotAt i s = Π (ihT i s) (El ⌜Nat⌝)

⊢MotAt : {Γ : Ctx} {i s : RTm ⌊ Γ ⌋} →
         Γ ⊢ i ∷ El ⌜Nat⌝ → Γ ⊢ s ∷ Tm i → Γ ⊢ty MotAt i s
⊢MotAt di ds = ty-Π (⊢ihT di ds) (ty-El ⊢⌜Nat⌝)

-- ★ the two-slot motive: index = `var (vs vz)`, scrutinee = `var vz`.
Mot : {Γ : Cx} → RTy ((Γ ∙) ∙)
Mot = MotAt (var (vs vz)) (var vz)

⊢Mot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ IMu TmD INat (var vz)) ⊢ty Mot
⊢Mot = ⊢MotAt (⊢var (there here)) (⊢var here)

------------------------------------------------------------------------
-- 2. THE THREE METHODS.
--
-- Each is FOUR binders — the index, the payload, the structural IH
-- tuple, and then the amrec IH the motive's codomain asks for.
------------------------------------------------------------------------

mVar mLam mApp : {Γ : Cx} → RTm Γ
mVar = lam (lam (lam (lam nzero)))
mLam = lam (lam (lam (lam nzero)))

-- ★★★ THE RECURSIVE LEAF.  `ih (fst p) ⟨descent⟩`, with the payload and
--   the index both BOUND VARIABLES — which is why `⊢desc-app` had to be
--   proved at an abstract payload.
mApp = lam (lam (lam (lam
         (app (app (var vz) (fst (var (vs (vs vz)))))
              (descAppTm (var (vs (vs (vs vz)))) (var (vs (vs vz))))))))

-- `var`: no recursive field, so the structural IH tuple is `Unit`.
tyMethVar : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat zero varC Mot
tyMethVar =
  ty-Π (ty-El ⊢⌜Nat⌝)
    (ty-Π tyPayVar
      (ty-Π ty-Unit
        (⊢MotAt (⊢var (there (there here)))
                (⊢icon TmWf hereID (⊢var (there (there here)))
                                   (⊢var (there here))))))

⊢mVar : {Γ : Ctx} → Γ ⊢ mVar ∷ imethTy TmD INat zero varC Mot
⊢mVar =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayVar
      (⊢lam ty-Unit
        (⊢lam (⊢ihT (⊢var (there (there here)))
                    (⊢icon TmWf hereID (⊢var (there (there here)))
                                       (⊢var (there here))))
              (toI ⊢nzero))))

-- `lam`: ONE structural IH, at the SHIFTED index `suc n` — and the
-- amrec IH cannot be applied to the body, whose type is `Tm (suc n)`.
tyMethLam : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat (suc zero) lamC Mot
tyMethLam =
  ty-Π (ty-El ⊢⌜Nat⌝)
    (ty-Π tyPayLam
      (ty-Π (ty-Σ (⊢MotAt (toI (⊢nsuc (fromI (⊢var (there here)))))
                          (⊢fst (⊢var here)))
                  ty-Unit)
        (⊢MotAt (⊢var (there (there here)))
                (⊢icon TmWf (thereID hereID) (⊢var (there (there here)))
                                             (⊢var (there here))))))

⊢mLam : {Γ : Ctx} → Γ ⊢ mLam ∷ imethTy TmD INat (suc zero) lamC Mot
⊢mLam =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayLam
      (⊢lam (ty-Σ (⊢MotAt (toI (⊢nsuc (fromI (⊢var (there here)))))
                          (⊢fst (⊢var here)))
                  ty-Unit)
        (⊢lam (⊢ihT (⊢var (there (there here)))
                    (⊢icon TmWf (thereID hereID) (⊢var (there (there here)))
                                                 (⊢var (there here))))
              (toI ⊢nzero))))

-- `app`: TWO structural IHs, both at the ambient index — and both
-- fields are at the carrier's own type, so the amrec IH applies.
tyMethApp : {Γ : Ctx} → Γ ⊢ty imethTy TmD INat (suc (suc zero)) appC Mot
tyMethApp =
  ty-Π (ty-El ⊢⌜Nat⌝)
    (ty-Π tyPayApp
      (ty-Π (ty-Σ (⊢MotAt (⊢var (there here)) (⊢fst (⊢var here)))
                  (ty-Σ (⊢MotAt (⊢wk (⊢var (there here)))
                                (⊢wk (⊢fst (⊢snd (⊢var here)))))
                        ty-Unit))
        (⊢MotAt (⊢var (there (there here)))
                (⊢icon TmWf (thereID (thereID hereID))
                            (⊢var (there (there here)))
                            (⊢var (there here))))))

⊢mApp : {Γ : Ctx} → Γ ⊢ mApp ∷ imethTy TmD INat (suc (suc zero)) appC Mot
⊢mApp =
  ⊢lam (ty-El ⊢⌜Nat⌝)
    (⊢lam tyPayApp
      (⊢lam (ty-Σ (⊢MotAt (⊢var (there here)) (⊢fst (⊢var here)))
                  (ty-Σ (⊢MotAt (⊢wk (⊢var (there here)))
                                (⊢wk (⊢fst (⊢snd (⊢var here)))))
                        ty-Unit))
        (⊢lam (⊢ihT (⊢var (there (there here)))
                    (⊢icon TmWf (thereID (thereID hereID))
                                (⊢var (there (there here)))
                                (⊢var (there here))))
          -- ★★★ THE RECURSIVE CALL, and the whole point of step 1b.
          (⊢app (⊢app (⊢var here) (⊢fst (⊢var (there (there here)))))
                (⊢desc-app (⊢var (there (there (there here))))
                           (⊢fst (⊢var (there (there here))))
                           (⊢fst (⊢snd (⊢var (there (there here))))))))))

------------------------------------------------------------------------
-- 3. THE METHOD TUPLE, AND THE STEP.
------------------------------------------------------------------------

mRecs : {Γ : Cx} → RTm Γ
mRecs = pair mVar (pair mLam (pair mApp unit))

⊢mRecs : {Γ : Ctx} → Γ ⊢ mRecs ∷ imethsTy TmD INat Mot TmD
⊢mRecs =
  ⊢pair (ty-Σ tyMethLam (ty-Σ tyMethApp ty-Unit)) ⊢mVar
    (⊢pair (ty-Σ tyMethApp ty-Unit) ⊢mLam
      (⊢pair ty-Unit ⊢mApp ⊢unit))

-- ★ SPLIT FIRST, TAKE THE IH SECOND — `DivLib`'s `lam (natrec …)` with
--   the `natrec` replaced by an `ielim` over the syntax.
stpR : RTm ε
stpR = lam (ielim TmD nzero mRecs (var vz))

⊢stpR : ◇ ⊢ stpR ∷ aStepT A ⌜Nat⌝ msr
⊢stpR = ⊢lam ⊢A (⊢ielim TmWf ⊢Mot (toI ⊢nzero) ⊢mRecs (⊢var here))

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
  (step (ξ-appˡ (ι-ielim TmD nzero mRecs (suc (suc zero)) selfPay))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-appˡ
          (ξ-fst (ξ-snd (βsnd mVar (pair mLam (pair mApp unit)))))))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-appˡ
          (ξ-fst (βsnd mLam (pair mApp unit)))))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (ξ-appˡ (βfst mApp unit)))))
  (step (ξ-appˡ (ξ-appˡ (ξ-appˡ (β _ nzero))))
  (step (ξ-appˡ (ξ-appˡ (β _ selfPay)))
  (step (ξ-appˡ (β _ _))
  (step (β _ ih) done))))))))
