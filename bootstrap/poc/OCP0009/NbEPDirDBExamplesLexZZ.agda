------------------------------------------------------------------------
-- OCP-0009 — LEXREC BRANCH (0,0):  n₁ = 0, n₂ = 0.
--
-- ⚠ WHY ITS OWN MODULE.  Not taste — RAM.  This branch alone elaborates
--   to ~3 GB (see NbEPDirDBExamplesLex §"SECOND BLOCKER"), and Agda's
--   term-traversal phases are per-MODULE, so four branches in one file do
--   not fit on a 7.5 GiB box.  Splitting is possible at all only because
--   the branch is cut into `Def`-backed lemmas: it leaves here as a NAME.
--
-- BOTH obligations are vacuous at (0,0): `rec₁` gets μ₁ y < μ₁ x ≤ 0 and
-- `rec₂` gets μ₂ y < μ₂ x ≤ 0, so each is `ordtr` into `⊢strong-base'`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexZZ where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; absurd; ordtr; lam; app
        ; Π; renTy; subTy; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢nzero; ⊢nsuc
        ; ⊢lam; ⊢app
        ; ty-Nat; ty-Hom )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-base' )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; REC1T; REC2T; M0lex; lexZZ )

------------------------------------------------------------------------
-- 6. BRANCH (0,0), SPLIT INTO Def-BACKED LEMMAS.
--
-- ⚠ WHY SPLIT: written as ONE inline term this branch ran 349s to 4.69 GB
--   without reaching a verdict (see the SECOND BLOCKER note above).  Each
--   `⊢app`/`⊢lam` node stores its implicit types in full, so the cost is
--   term SIZE.  Naming the two recursor arguments puts a `Def` at the
--   assembly site instead of an expanded derivation.
--
-- ★ EVERY type below is READ OFF Agda by the goal-probe, not reconstructed
--   by hand — that is the discipline the checkpoint note argues for, and
--   the `renTy (extR vs)⁵ REC1T` shape is exactly what it predicted.
------------------------------------------------------------------------

-- the context after the three `⊢lam`s (x, le : μ₁ x ≤ 0, lt : μ₂ x ≤ n₂)
ΓZZ : Ctx
ΓZZ =
  (((Γ₅ ▹ Nat) ▹ subTy (single nzero) Nat)
     ▹ subTy (extS (single nzero))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var vz)) nzero))
     ▹ subTy (extS (extS (single nzero)))
         (Hom Nat (app (var (vs (vs (vs (vs (vs vz)))))) (var (vs vz)))
                  (var (vs (vs vz))))

lexZZrec1 : RTm ⌊ ΓZZ ⌋
lexZZrec1 =
  lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs vz)))))))))) (var (vs vz))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs vz)))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs vz)))))) nzero (var vz) (var (vs (vs (vs vz)))))))

REC1TZZ : RTy ⌊ ΓZZ ⌋
REC1TZZ =
  subTy (single (var (vs (vs vz))))
    (renTy (extR vs) (renTy (extR vs) (renTy (extR vs)
      (renTy (extR vs) (renTy (extR vs) REC1T)))))

⊢lexZZrec1 : ΓZZ ⊢ lexZZrec1 ∷ REC1TZZ
⊢lexZZrec1 =
  ⊢lam ty-Nat
                (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (here)))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there (there here))))))
                  (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there (there here)))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there here))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there (there here)))))) (⊢var (here)) (⊢var (there (there (there here))))))

lexZZrec2 : RTm ⌊ ΓZZ ⌋
lexZZrec2 =
  lam (lam (lam (absurd (app (var (vs (vs (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))))) (var (vs (vs vz)))) (ordtr (nsuc (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs vz))))) (app (var (vs (vs (vs (vs (vs (vs (vs (vs vz))))))))) (var (vs (vs (vs (vs (vs vz))))))) nzero (var vz) (var (vs (vs (vs vz))))))))

-- ★ note `single lexZZrec1`: the argument type of `rec₂` depends on the
--   rec₁ TERM, so the split has to name the term as well as the derivation.
REC2TZZ : RTy ⌊ ΓZZ ⌋
REC2TZZ =
  subTy (single lexZZrec1)
    (subTy (extS (single (var (vs (vs vz)))))
      (renTy (extR (extR vs)) (renTy (extR (extR vs)) (renTy (extR (extR vs))
        (renTy (extR (extR vs)) (renTy (extR (extR vs)) REC2T))))))

⊢lexZZrec2 : ΓZZ ⊢ lexZZrec2 ∷ REC2TZZ
⊢lexZZrec2 =
  ⊢lam ty-Nat
                (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (here))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there (there here))))))
                  (⊢lam (ty-Hom ty-Nat (⊢nsuc (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there here)))))))) (⊢var (there (there (there (there here)))))))
                    (⊢strong-base' (⊢app (⊢var (there (there (there (there (there (there (there (there (there (there here))))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there here)))) (⊢app (⊢var (there (there (there (there (there (there (there (there here))))))))) (⊢var (there (there (there (there (there here))))))) (⊢var (here)) (⊢var (there (there (there here)))))))

------------------------------------------------------------------------
-- 7. BRANCH (0,0) ASSEMBLED.  Three `⊢lam`s and a three-fold `⊢app`
--    spine; both recursor arguments are `Def`s, so this term is small.
------------------------------------------------------------------------

⊢lexZZ : (Γ₅ ▹ Nat) ⊢ lexZZ ∷ subTy (single nzero) M0lex
⊢lexZZ =
  ⊢lam ty-Nat
    (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there here))))) (⊢var (here))) ⊢nzero)
      (⊢lam (ty-Hom ty-Nat (⊢app (⊢var (there (there (there (there here))))) (⊢var (there here))) ⊢nzero)
        (⊢app (⊢app (⊢app (⊢var (there (there (there (there here))))) (⊢var (there (there here))))
              ⊢lexZZrec1)
              ⊢lexZZrec2)))
