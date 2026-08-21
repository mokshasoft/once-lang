------------------------------------------------------------------------
-- OCP-0009 — D4 AT A PAIR CARRIER.  The second use site, and the first
-- that is not at ℕ.
--
-- ⚠ WHY THIS AND NOT THE REAL DOGFOODING.  The persuasive use site would
--   be the POC's own `sz`-bounded recursions (`prog`/`usplit`/`trS`/
--   `ordtrS`), but `RTy` has NO user-defined inductive types, so a
--   recursion on `RTm` needs the inductive-types axis first.  `Σ'` is the
--   closest available non-ℕ carrier, and there is no miniature — a
--   term-like carrier cannot be encoded from `Σ`/`Π` without type-level
--   recursion.
--
-- ⚠ AND WHY NOT gcd.  gcd's descent needs monotonicity of `+` under `≤`
--   and its strict form — a real arithmetic development that would test
--   the ARITHMETIC, not the abstraction.  This probe isolates what is
--   actually new at a pair carrier:
--
--     * the carrier is `Σ' Nat Nat` — a TYPE under D4, where AmrecC must
--       take `El (⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝)`, which only REDUCES to `Σ'`;
--     * the measure is a PROJECTION, `fst x`, not the carrier variable;
--     * the recursive call must BUILD A PAIR — the very move the 2026-08-07
--       handoff records as impossible under `Γ₅` ("Ackermann's step must
--       build pairs, which needs the carrier concrete").
--
-- THE FUNCTION: `f (a , b) = case a of 0 → b; suc a' → f (a' , suc b)`.
-- Deliberately trivial mathematics (it computes `a + b`); the point is the
-- plumbing around it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesPairLib where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U; Σ'
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Π; renTy; renTm; subTy; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢conv; ⊢nzero; ⊢nsuc; ⊢natrec
        ; ⊢lam; ⊢app; ⊢pair; ⊢fst; ⊢snd; ⊢⌜Nat⌝; _⊢ty_
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Σ
        ; _≅ᵀ_; csymᵀ; ctrnᵀ; El-⌜Nat⌝; Hom-Nat-ss
        ; _⟶_; _⟶*_; done; step; βfst; βsnd; β; natrec-zero; natrec-suc
        ; ξ-nsuc; ξ-Homˡ; ξ-Homʳ; ξ-appˡ )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBLibStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibRec   using ( aIHT; aIHTat )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( aStepT; module AmTΠ )
-- ⚠ `measure-evals` moved to `…LibAmrecClosed` 2026-08-21: it is the
--   CLOSED-CARRIER layer and the only thing that needed `natEval`, whose
--   proof drags the canonicity stack.  This use site is at `◇`, so it is
--   the right client for it.
open import poc.OCP0009.NbEPDirDBLibAmrecClosed using ( measure-evals )
open import poc.OCP0009.NbEPDirDBLibNatVal using ( NatVal; nv-zero; nv-suc )

------------------------------------------------------------------------
-- ★ THE INSTANTIATION.  The carrier is a TYPE, so there is no code, no
--   `El`, and — the point of this file — `⊢fst`/`⊢snd` apply DIRECTLY.
------------------------------------------------------------------------

PairT : {Γ : Cx} → RTy Γ
PairT = Σ' Nat Nat

⊢PairT : {Γ : Ctx} → Γ ⊢ty PairT
⊢PairT = ty-Σ ty-Nat ty-Nat

-- the measure: the FIRST component of the carrier variable
msr : {Γ : Cx} → RTm (Γ ∙)
msr = fst (var vz)

⊢msr : {Γ : Ctx} → (Γ ▹ PairT) ⊢ msr ∷ Nat
⊢msr = ⊢fst (⊢var here)

elNat : {Γ : Cx} → El (⌜Nat⌝ {Γ}) ≅ᵀ Nat
elNat = red→≅ᵀ (stepᵀ El-⌜Nat⌝ doneᵀ)

asP : {Γ : Ctx} {t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Nat → Γ ⊢ t ∷ El ⌜Nat⌝
asP d = ⊢conv d (csymᵀ elNat)

------------------------------------------------------------------------
-- THE STEP.  Split on `fst x`; the motive abstracts the IH's BOUND, so
-- the recursive call's descent is at `suc a'` and discharges by
-- reflexivity once `fst (pair a' _)` reduces.
------------------------------------------------------------------------

fMot : RTy (ε ∙ ∙)
fMot = Π (aIHTat PairT ⌜Nat⌝ msr (var vz)) (El ⌜Nat⌝)

⊢ihTat : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
         Γ ⊢ty aIHTat PairT ⌜Nat⌝ msr b
⊢ihTat db =
  ty-Π ⊢PairT
    (ty-Π (ty-Hom ty-Nat (⊢nsuc ⊢msr) (⊢wk db)) (ty-El ⊢⌜Nat⌝))

⊢fMot : ((◇ ▹ PairT) ▹ Nat) ⊢ty fMot
⊢fMot = ty-Π (⊢ihTat (⊢var here)) (ty-El ⊢⌜Nat⌝)

-- a = 0: the answer is the second component; the IH is discarded.
fZ : RTm (ε ∙)
fZ = lam (snd (var (vs vz)))

⊢fZ : (◇ ▹ PairT) ⊢ fZ ∷ subTy (single nzero) fMot
⊢fZ = ⊢lam (⊢ihTat ⊢nzero) (asP (⊢snd (⊢var (there here))))

-- a = suc a': recurse at `(a' , suc b)`.  ★ THE PAIR IS BUILT HERE.
fS : RTm (ε ∙ ∙ ∙)
fS =
  lam (app (app (var vz) (pair (var (vs (vs vz))) (nsuc (snd (var (vs (vs (vs vz))))))))
           (reflTm (var (vs (vs vz)))))

⊢fS : (((◇ ▹ PairT) ▹ Nat) ▹ fMot) ⊢ fS ∷ subTy nrs fMot
⊢fS =
  ⊢lam (⊢ihTat (⊢nsuc (⊢var (there here))))
    (⊢app (⊢app (⊢var here) dPair) dDesc)
  where
    dPair = ⊢pair ty-Nat (⊢var (there (there here)))
                  (⊢nsuc (⊢snd (⊢var (there (there (there here))))))
    -- ★ `fst (pair a' _)` REDUCES to `a'`, so the descent is `a' ≤ a'`.
    dDesc = ⊢conv (⊢le-refl (⊢var (there (there here))))
                  (csymᵀ (ctrnᵀ (red→≅ᵀ (stepᵀ (ξ-Homˡ (ξ-nsuc (βfst _ _))) doneᵀ))
                                (red→≅ᵀ (stepᵀ (Hom-Nat-ss _ _) doneᵀ))))

fStp : RTm ε
fStp = lam (natrec fZ fS msr)

⊢fStp : ◇ ⊢ fStp ∷ aStepT PairT ⌜Nat⌝ msr
⊢fStp = ⊢lam ⊢PairT (⊢natrec ⊢fMot ⊢fZ ⊢fS ⊢msr)

------------------------------------------------------------------------
-- THE USE SITE.
------------------------------------------------------------------------

open AmTΠ ◇ PairT ⌜Nat⌝ msr fStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢fStp
  using ( amrecTm; ⊢amrecΠ; ⊢amrecPt )

fTm : RTm ε
fTm = amrecTm

⊢f : ◇ ⊢ fTm ∷ Π PairT (El ⌜Nat⌝)
⊢f = ⊢amrecΠ

------------------------------------------------------------------------
-- ★★ AND IT COMPUTES.  Type-correct is not the same as correct — this
--    session found `⊢gcd-descend` certifying a recursion that was not gcd
--    — so the step's defining equations are checked here as REDUCTIONS.
--
-- ⚠ These are the USER's half.  The combinator's half — how `amrecTm`
--   unfolds to the step — is `amrec-unfold-z`/`-s` in LibAmrec, already
--   proven there.  Together they cover `app fTm x`.
------------------------------------------------------------------------

-- ★ `f (0 , 1) = 1` — the zero equation, end to end at concrete values.
--   ⚠ concrete rather than an arbitrary `b`: for an open `b` the final β
--   leaves `subTm (single ih) (w b)`, which is `b` only PROPOSITIONALLY
--   (`wk-single`).  At a numeral it computes.
f-computes-zero : (ih : RTm ε) →
                  app (app fStp (pair nzero (nsuc nzero))) ih ⟶* nsuc nzero
f-computes-zero ih =
  step (ξ-appˡ (β _ (pair nzero (nsuc nzero))))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst nzero (nsuc nzero)) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-zero _ _) done))
        (step (β _ ih)
          (step (βsnd nzero (nsuc nzero)) done))))

-- ★★ THE SUCCESSOR EQUATION — the one that matters.  `f (1 , 0)` really
--    does recurse at `(0 , suc 0)`: the pair is BUILT and handed to the
--    IH, with the descent alongside.  A gcd-class spec error — a recursion
--    that typechecks but recurses at the wrong argument — would show here
--    and nowhere else.
f-computes-suc : (ih : RTm ε) →
                 app (app fStp (pair (nsuc nzero) nzero)) ih
               ⟶* app (app ih (pair nzero (nsuc (snd (pair (nsuc nzero) nzero)))))
                      (reflTm nzero)
f-computes-suc ih =
  step (ξ-appˡ (β _ (pair (nsuc nzero) nzero)))
    (⟶*-trans (⟶*-appˡ (⟶*-natrecⁿ (step (βfst (nsuc nzero) nzero) done)))
      (⟶*-trans (⟶*-appˡ (step (natrec-suc _ _ nzero) done))
        (step (β _ ih) done)))

------------------------------------------------------------------------
-- ★★ AND THE UNFOLDING'S PREMISE IS DISCHARGED, NOT ASSUMED.
--
-- This use site is at `◇`, so `measure-evals` supplies what
-- `amrec-unfold-z`/`-s` need.  Nothing here proves that `fst x` reaches a
-- numeral — the library does, from canonicity.
--
-- ⚠ `NbEPDirDBExamplesDivLib` would NOT get this: its ambient context carries the
--   divisor `k` as a free variable, so its measure normalises to a NEUTRAL
--   and the premise is genuine caller information.  Same library, two
--   domains.
------------------------------------------------------------------------

msr-evals : (x : RTm ε) → ◇ ⊢ x ∷ PairT → NatVal (subTm (single x) msr)
msr-evals = measure-evals PairT msr ⊢msr

-- ★ concretely: the measure at `(1 , 0)` really does reach a numeral, and
--   the library — not this file — is what knows it.
msr-evals-at : NatVal (subTm (single (pair (nsuc nzero) nzero)) msr)
msr-evals-at =
  msr-evals (pair (nsuc nzero) nzero)
            (⊢pair ty-Nat (⊢nsuc ⊢nzero) ⊢nzero)
