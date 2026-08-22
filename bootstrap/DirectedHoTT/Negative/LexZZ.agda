------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,0):  n₁ = 0, n₂ = 0.
--
-- ★ ONE MODULE AGAIN, at the GENERIC carrier — 20.7s / 2.22 GB.
--   It was briefly FIVE (one `⊢lam` per module, ~120s / 3.4 GB peak),
--   because adding `A : U` to Γ₅ made a context slot cost ~4.5×.  Taking
--   `stp` OUT of Γ₅ — it is only ever applied, never bound over, so it is
--   an argument now — paid that back and then some: this is cheaper than
--   the ℕ-carrier original was (35.2s / 2.12 GB), which still carried the
--   stp slot.  See SPIKE-COST.md.
--
-- BOTH obligations are vacuous at (0,0): `rec₁` gets μ₁ y < μ₁ x ≤ 0 and
-- `rec₂` gets μ₂ y < μ₂ x ≤ 0, so each is `ordtr` into `⊢strong-base'`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Negative.LexZZ where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom; ty-El )
open import DirectedHoTT.Lib.Ord using ( ⊢strong-base' )
open import DirectedHoTT.Negative.Lex
  using ( Γ₅; REC1T; REC2T; LStepT; M0lex; lexZZ )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )

------------------------------------------------------------------------
-- 6. BRANCH (0,0), AS Def-BACKED LEMMAS.
--
-- ⚠ STILL WORTH NAMING the two recursor arguments: written as ONE inline
--   term this branch ran 349s to 4.69 GB without reaching a verdict.  Each
--   `⊢app`/`⊢lam` node stores its implicit types in full, so the cost is
--   term SIZE.  A `Def` at the assembly site beats an expanded derivation.
--   What is no longer needed is a MODULE per lemma.
--
-- ★ EVERY type below is READ OFF Agda by the goal-probe, not reconstructed
--   by hand.  Note `renTy (extR vs)⁴`, not ⁵: REC1T/REC2T each gained the
--   carrier slot, so one fewer weakening layer gets to ⌊ΓZZ⌋.
------------------------------------------------------------------------

-- the context after the three `⊢lam`s (x, le : μ₁ x ≤ 0, lt : μ₂ x ≤ n₂)
ΓZZ : Ctx
ΓZZ =
  (((Γ₅ ▹ Nat) ▹ subTy (single nzero) (El (var (vs (vs (vs (vs (vs vz))))))))
     ▹ subTy (extS (single nzero))
         (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var vz)) nzero))
     ▹ subTy (extS (extS (single nzero)))
         (Hom Nat (app (var (vs (vs (vs (vs vz))))) (var (vs vz)))
                  (var (vs (vs vz))))

lexZZrec1 : RTm ⌊ ΓZZ ⌋
lexZZrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZZ : RTy ⌊ ΓZZ ⌋
REC1TZZ =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) (renTy (extR vs) REC1T))))

⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1 ∷ REC1TZZ
⊢lexZZrec1 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there here))))))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var here))) (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there (there (there here)))))) (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there (there (there here)))))) (⊢var here) (⊢var (there (there (there here))))))

lexZZrec2 : RTm ⌊ ΓZZ ⌋
lexZZrec2 =
  lam (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs vz)))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))

-- ★ note `single lexZZrec1`: the argument type of `rec₂` depends on the
--   rec₁ TERM, so the split has to name the term as well as the derivation.
REC2TZZ : RTy ⌊ ΓZZ ⌋
REC2TZZ =
  subTy (single lexZZrec1)
    (subTy (extS (single (var (vs (vs vz)))))
      (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs))
        (renTy (extR (extR vs)) REC2T)))))

⊢lexZZrec2 : ΓZZ ⊢ lexZZrec2 ∷ REC2TZZ
⊢lexZZrec2 =
  ⊢lam (ty-El (⊢var (there (there (there (there (there (there (there here))))))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var here)) (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there here)))) (⊢app (⊢var (there (there (there (there (there (there here))))))) (⊢var (there (there (there (there here))))))) (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there (there (there (there here))))))) (⊢var here) (⊢var (there (there (there here)))))))

------------------------------------------------------------------------
-- 7. BRANCH (0,0) ASSEMBLED.  Three `⊢lam`s and a three-fold `⊢app`
--    spine; both recursor arguments are `Def`s, so this term is small.
------------------------------------------------------------------------

⊢lexZZ : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
         (Γ₅ ▹ Nat) ⊢ lexZZ stpTm ∷ subTy (single nzero) M0lex
⊢lexZZ stpTm dstp =
  ⊢lam (ty-El (⊢var (there (there (there (there here)))))) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there here)))) (⊢var here)) ⊢nzero) (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there here)))) (⊢var (there here))) ⊢nzero) (⊢app (⊢app (⊢app (⊢wk (⊢wk (⊢wk (⊢wk (dstp))))) (⊢var (there (there here)))) ⊢lexZZrec1) ⊢lexZZrec2)))
