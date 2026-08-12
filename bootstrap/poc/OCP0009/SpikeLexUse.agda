------------------------------------------------------------------------
-- OCP-0009 — ★★★ LEXREC'S FIRST USE SITE.  A PAIR CARRIER, AND `rec₂`.
--
-- ⚠ WHY THIS FILE EXISTS AND WHAT IT SETTLES.  The `Γ₅` `⊢lexrec` was
--   also "derived end to end" and is UNCALLABLE — its premise
--   `Γ₅ ⊢ x ∷ El cA` cannot be satisfied (WF-LIBRARY D2).  A typing
--   derivation is therefore not evidence of a usable combinator, and the
--   only thing that settles it is instantiating the interface and
--   writing a step.  That is all this file does.
--
-- THE FUNCTION, deliberately trivial mathematics:
--
--     f (a , 0)      = a
--     f (a , suc b') = f (a , b')          -- μ₁ HELD, μ₂ DOWN → rec₂
--
--   so `f (a , b) = a`.  The point is the plumbing, exactly as in
--   `SpikePairT`: what is exercised is the LEXICOGRAPHIC descent, where
--   the μ₁ obligation is discharged by REFLEXIVITY (`fst y ≤ fst x`
--   because the recursive call keeps the first component) and the μ₂
--   obligation is a real strict descent.  That pairing — one `≤`, one
--   `<` — is precisely what `rec₂` is and what `amrec` cannot state.
--
-- ⚠ HONEST SCOPE: this uses `rec₂` only.  `rec₁` is `aIHT`, which
--   `SpikePairT` already exercises at this very carrier through `amrec`,
--   so nothing about it is untested — but a function using BOTH is a
--   better demo and is not this one.  Ackermann is that function (#9).
--
-- ★ AND THE CASE SPLIT LANDS ON THE MEASURE, NOT THE CARRIER (D8): the
--   `natrec` is on `snd x`, so the IH's μ₂-bound is the natrec VARIABLE
--   rather than `μ₂ x`, and `rec2Tat` is what can say that.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeLexUse where

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
        ; ξ-nsuc; ξ-Homˡ; βfst; βsnd )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; stepᵀ; doneᵀ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibPair
  using ( PairT; ⊢PairT; msr₁; msr₂; ⊢msr₁; ⊢msr₂; elNat; asP; holdˡ; dropʳ )
open import poc.OCP0009.SpikeLexT using ( rec1T; rec2Tat; lStepT )
open import poc.OCP0009.SpikeLexAsm using ( module LxΠ )

-- ★ THE INSTANTIATION comes from `NbEPDirDBLibPair` — carrier, both
--   measures, and the `El ⌜Nat⌝`/`Nat` crossings.  Nothing to write.

------------------------------------------------------------------------
-- the two recursor types at an ARBITRARY bound, well-formed.  ★ `rec₂`
-- needs BOTH bounds nameable; that is `rec2Tat`, D8's twin.
------------------------------------------------------------------------

⊢rec1Tat : {Γ : Ctx} {b : RTm ⌊ Γ ⌋} → Γ ⊢ b ∷ Nat →
           Γ ⊢ty aIHTat PairT ⌜Nat⌝ msr₁ b
⊢rec1Tat db =
  ty-Π ⊢PairT (ty-Π (ty-Hom ty-Nat (⊢nsuc ⊢msr₁) (⊢wk db)) (ty-El ⊢⌜Nat⌝))

⊢rec2Tat : {Γ : Ctx} {b₁ b₂ : RTm ⌊ Γ ⌋} → Γ ⊢ b₁ ∷ Nat → Γ ⊢ b₂ ∷ Nat →
           Γ ⊢ty rec2Tat PairT ⌜Nat⌝ msr₁ msr₂ b₁ b₂
⊢rec2Tat db₁ db₂ =
  ty-Π ⊢PairT
    (ty-Π (ty-Hom ty-Nat ⊢msr₁ (⊢wk db₁))
      (ty-Π (ty-Hom ty-Nat (⊢nsuc (⊢wk ⊢msr₂)) (⊢wk (⊢wk db₂)))
            (ty-El ⊢⌜Nat⌝)))

------------------------------------------------------------------------
-- THE STEP.  Split on `snd x`; the motive abstracts rec₂'s μ₂-BOUND, so
-- the recursive call's descent is at `suc b'` and discharges by
-- reflexivity once `snd (pair _ b')` reduces.
--
-- ⚠ rec₁'s bound stays CONCRETE (`fst x`) — we do not split on μ₁, and
--   the motive must not abstract what the split does not move.
------------------------------------------------------------------------

fMot : RTy (ε ∙ ∙)
fMot =
  Π (renTy vs (rec1T PairT ⌜Nat⌝ msr₁))
    (Π (rec2Tat PairT ⌜Nat⌝ msr₁ msr₂ (fst (var (vs (vs vz)))) (var (vs vz)))
       (El ⌜Nat⌝))

⊢fMot : ((◇ ▹ PairT) ▹ Nat) ⊢ty fMot
⊢fMot =
  ty-Π (⊢rec1Tat (⊢fst (⊢var (there here))))
    (ty-Π (⊢rec2Tat (⊢fst (⊢var (there (there here)))) (⊢var (there here)))
          (ty-El ⊢⌜Nat⌝))

-- b = 0: the answer is the first component; both recursors are discarded.
fZ : RTm (ε ∙)
fZ = lam (lam (fst (var (vs (vs vz)))))

⊢fZ : (◇ ▹ PairT) ⊢ fZ ∷ subTy (single nzero) fMot
⊢fZ =
  ⊢lam (⊢rec1Tat (⊢fst (⊢var here)))
    (⊢lam (⊢rec2Tat (⊢fst (⊢var (there here))) ⊢nzero)
          (asP (⊢fst (⊢var (there (there here))))))

-- b = suc b': recurse at `(fst x , b')` through rec₂.
-- ★ THE PAIR IS BUILT HERE, and both descents are discharged alongside it:
--     μ₁  fst (pair (fst x) b') ⟶ fst x, so `fst x ≤ fst x` — REFLEXIVITY,
--         which is what "μ₁ held" means;
--     μ₂  snd (pair (fst x) b') ⟶ b', so `b' < suc b'` — the real descent.
fS : RTm (ε ∙ ∙ ∙)
fS =
  lam (lam (app (app (app (var vz)
                          (pair (fst (var (vs (vs (vs (vs vz))))))
                                (var (vs (vs (vs vz))))))
                     (reflTm (fst (var (vs (vs (vs (vs vz))))))))
                (reflTm (var (vs (vs (vs vz)))))))

⊢fS : (((◇ ▹ PairT) ▹ Nat) ▹ fMot) ⊢ fS ∷ subTy nrs fMot
⊢fS =
  ⊢lam (⊢rec1Tat (⊢fst (⊢var (there (there here)))))
    (⊢lam (⊢rec2Tat (⊢fst (⊢var (there (there (there here)))))
                    (⊢nsuc (⊢var (there (there here)))))
      (⊢app (⊢app (⊢app (⊢var here) dPair) dDesc₁) dDesc₂))
  where
    dx    = ⊢var (there (there (there (there here))))
    db'   = ⊢var (there (there (there here)))
    dPair = ⊢pair ty-Nat (⊢fst dx) db'
    -- ★ BOTH DESCENTS COME FROM THE LIBRARY (D10).  `holdˡ` is μ₁ held —
    --   `fst (pair (fst x) _)` reduces to `fst x`, so reflexivity — and
    --   `dropʳ` is μ₂ strictly down.  The caller writes neither.
    a      = fst (var (vs (vs (vs (vs vz)))))
    b      = var (vs (vs (vs vz)))
    dDesc₁ = holdˡ a b (⊢fst dx)
    dDesc₂ = dropʳ a b db'

fStp : RTm ε
fStp = lam (natrec fZ fS msr₂)

⊢fStp : ◇ ⊢ fStp ∷ lStepT PairT ⌜Nat⌝ msr₁ msr₂
⊢fStp = ⊢lam ⊢PairT (⊢natrec ⊢fMot ⊢fZ ⊢fS ⊢msr₂)

------------------------------------------------------------------------
-- ★★★ THE USE SITE.  Five atoms and one derivation — and `⊢lexrec` is
--     CALLABLE, which is the whole claim this file exists to make.
------------------------------------------------------------------------

open LxΠ ◇ PairT ⌜Nat⌝ msr₁ msr₂ fStp ⊢PairT ⊢⌜Nat⌝ ⊢msr₁ ⊢msr₂ ⊢fStp
  using ( lexrecTm; ⊢lexrecΠ; ⊢lexrecPt )

fTm : RTm ε
fTm = lexrecTm

⊢f : ◇ ⊢ fTm ∷ Π PairT (El ⌜Nat⌝)
⊢f = ⊢lexrecΠ

-- …and pointwise, with no cast, at a concrete pair.
⊢f-at : ◇ ⊢ app fTm (pair (nsuc nzero) (nsuc nzero))
        ∷ subTy (single (pair (nsuc nzero) (nsuc nzero))) (El ⌜Nat⌝)
⊢f-at = ⊢lexrecPt (⊢pair ty-Nat (⊢nsuc ⊢nzero) (⊢nsuc ⊢nzero))
