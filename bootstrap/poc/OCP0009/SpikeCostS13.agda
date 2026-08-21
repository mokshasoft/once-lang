------------------------------------------------------------------------
-- ABLATION S13 — OPTION C: the ambient context is ABSTRACT.
--
-- Same derivation as S1/S12 (⊢lexZZrec1, branch (0,0)'s first recursor
-- argument), but Γ₅ is gone entirely: the ambient context is a PARAMETER
-- `Δ : Ctx`, and the carrier/motive/measures are Agda-level terms with
-- supplied derivations, weakened per binder with ⊢wk — exactly what was
-- done to `stp`, now done to all four.
--
--   S1   Γ₅ = 5 slots, generic carrier   42.5 s / 3.91 GB
--   S12  Γ₅ = 4 slots, generic carrier    8.4 s / 0.88 GB
--   S13  Γ₅ = 0 slots, ambient abstract        ← this file
--
-- ★ WHY IT MIGHT WIN BIG: with Δ abstract, `⌊ Δ ⌋` is a VARIABLE, not a
--   concrete unary `ε ∙ ∙ ∙ ∙`.  Every stored implicit that carried a
--   depth-sized numeral now carries a single reference, and only the four
--   local binders contribute depth at all.
--
-- ★ WHY IT MIGHT NOT: abstract terms do not compute.  `renTm vs cA` is
--   STUCK, so anywhere a substitution has to cancel a weakening we need a
--   propositional lemma and a transport instead of definitional equality.
--   This file is exactly the test of whether that bites on a real branch.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.SpikeCostS13 where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat; U
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; renTm; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk )
open import poc.OCP0009.NbEPDirDBLibOrd using ( ⊢strong-base' )

w : {Γ : Cx} → RTm Γ → RTm (Γ ∙)
w = renTm vs

module _ (Δ : Ctx)
         (cA cP μ₁ μ₂ : RTm ⌊ Δ ⌋)
         (dcA : Δ ⊢ cA ∷ U)
         (dcP : Δ ⊢ cP ∷ Π (El cA) U)
         (dμ₁ : Δ ⊢ μ₁ ∷ Π (El cA) Nat)
         (dμ₂ : Δ ⊢ μ₂ ∷ Π (El cA) Nat)
  where

  -- ctx: vz = lt, vs = le, vs² = x, vs³ = n₂, then Δ
  ΓZZ : Ctx
  ΓZZ =
    (((Δ ▹ Nat) ▹ El (w cA))
       ▹ Hom Nat (app (w (w μ₁)) (var vz)) nzero)
       ▹ Hom Nat (app (w (w (w μ₂))) (var (vs vz))) nzero

  lexZZrec1 : RTm ⌊ ΓZZ ⌋
  lexZZrec1 =
    lam (lam (absurd (app (w (w (w (w (w (w cP)))))) (var (vs vz)))
                     (ordtr (nsuc (app (w (w (w (w (w (w μ₁)))))) (var (vs vz))))
                            (app (w (w (w (w (w (w μ₁)))))) (var (vs (vs (vs (vs vz))))))
                            nzero (var vz) (var (vs (vs (vs vz)))))))

  REC1TZZ : RTy ⌊ ΓZZ ⌋
  REC1TZZ =
    Π (El (w (w (w (w cA)))))
      (Π (Hom Nat (nsuc (app (w (w (w (w (w μ₁))))) (var vz)))
                  (app (w (w (w (w (w μ₁))))) (var (vs (vs (vs vz))))))
         (El (app (w (w (w (w (w (w cP)))))) (var (vs vz)))))

  ⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1 ∷ REC1TZZ
  ⊢lexZZrec1 =
    ⊢lam (ty-El (⊢wk (⊢wk (⊢wk (⊢wk dcA)))))
      (⊢lam (ty-Hom ty-Nat
               (⊢nsuc (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))) (⊢var here)))
               (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁))))) (⊢var (there (there (there here))))))
        (⊢strong-base'
           (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dcP)))))) (⊢var (there here)))
           (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))) (⊢var (there here)))
           (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk (⊢wk dμ₁)))))) (⊢var (there (there (there (there here))))))
           (⊢var here)
           (⊢var (there (there (there here))))))
