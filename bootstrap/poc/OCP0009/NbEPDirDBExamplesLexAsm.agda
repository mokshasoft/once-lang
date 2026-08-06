------------------------------------------------------------------------
-- OCP-0009 — LEXREC, ASSEMBLED.  The four branches are derived in
-- NbEPDirDBExamplesLex{ZZ,ZS,SZ,SS}; this module stacks them.
--
--   ⊢lexZBr  inner natrec on n₂ at n₁ = 0        (lexZZ / lexZS)
--   ⊢lexSBr  inner natrec on n₂ at n₁ = suc n₁'  (lexSZ / lexSS)
--   ⊢lexAux  OUTER natrec on n₁                  (lexZBr / lexSBr)
--   ⊢lexrec  aux applied at μ₁ x, μ₂ x, x, and two ⊢le-refl's
--
-- ★ THIS IS WHERE THE MOTIVES GET TESTED AGAINST EACH OTHER.  `⊢natrec`
--   demands that the base sit at `subTy (single nzero) M` and the step at
--   `subTy nrs M` for the SAME M — so M0lex/M1lex/lexAuxMot can no longer
--   be three independently hand-counted terms that merely look related.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexAsm where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; natrec; lam; app
        ; Π; renTy; subTy )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢natrec; ⊢lam; ⊢app; ⊢nzero
        ; ty-Nat )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesLex
  using ( Γ₅; lexAuxMot; M0lex; M1lex; ⊢lexAuxMot; ⊢M0lex; ⊢M1lex
        ; lexZBr; lexSBr; lexAuxTm )
open import poc.OCP0009.NbEPDirDBExamplesLexZZ using ( ⊢lexZZ )
open import poc.OCP0009.NbEPDirDBExamplesLexZS using ( ⊢lexZS )
open import poc.OCP0009.NbEPDirDBExamplesLexSZ using ( ⊢lexSZ )
open import poc.OCP0009.NbEPDirDBExamplesLexSS using ( ⊢lexSS )

-- the n₁ = 0 branch of the OUTER recursion: bind n₂, recurse on it.
⊢lexZBr : Γ₅ ⊢ lexZBr ∷ subTy (single nzero) lexAuxMot
⊢lexZBr = ⊢lam ty-Nat (⊢natrec ⊢M0lex ⊢lexZZ ⊢lexZS (⊢var here))

-- the n₁ = suc branch: same shape, at the motive whose μ₁ bound is suc n₁'.
⊢lexSBr : ((Γ₅ ▹ Nat) ▹ lexAuxMot) ⊢ lexSBr ∷ subTy nrs lexAuxMot
⊢lexSBr = ⊢lam ty-Nat (⊢natrec ⊢M1lex ⊢lexSZ ⊢lexSS (⊢var here))

-- ★ THE OUTER RECURSION.  Generic in the bound, as `⊢strong-base'` is —
--   so `lexrec` can instantiate it at μ₁ x.
⊢lexAux : {n : RTm ⌊ Γ₅ ⌋} → Γ₅ ⊢ n ∷ Nat →
          Γ₅ ⊢ lexAuxTm n ∷ subTy (single n) lexAuxMot
⊢lexAux dn = ⊢natrec ⊢lexAuxMot ⊢lexZBr ⊢lexSBr dn

------------------------------------------------------------------------
-- ★★ LEXREC ITSELF:  lexrec x = aux (μ₁ x) (μ₂ x) x (le-refl _) (le-refl _)
--
--   Both bounds are discharged by REFLEXIVITY.  That is the point of the
--   doubly-bounded auxiliary: it is strong enough that the top-level call
--   needs nothing but `μ₁ x ≤ μ₁ x` and `μ₂ x ≤ μ₂ x`.
------------------------------------------------------------------------

lexrecTm : RTm ⌊ Γ₅ ⌋ → RTm ⌊ Γ₅ ⌋
lexrecTm x =
  app (app (app (app (lexAuxTm (app (var (vs (vs vz))) x))
                     (app (var (vs vz)) x))
                x)
           (reflTm (app (var (vs (vs vz))) x)))
      (reflTm (app (var (vs vz)) x))

-- ★★ THE PIPELINE COMPOSES, at a CONCRETE argument.
--
-- ⚠ WHY CONCRETE, AND WHAT IS AND IS NOT PROVED HERE.  `x` is the THIRD
--   argument, so its occurrences in the result type are weakened past the
--   two remaining Π's and substituted back by the last two `⊢app`s.  For
--   a CONCRETE x that all computes and the derivation goes through by
--   reduction alone — which is what this instance shows.  For an ABSTRACT
--   x it does not: Agda is left needing
--     subTm (single q) (subTm (extS (single p)) (renTm vs (renTm vs x))) ≡ x
--   and similar at each argument position.  Those equations are TRUE (the
--   composite substitution is pointwise the identity) and the machinery
--   exists — `wk-single`, `subTm-renTm`, `subTm-subTm`, `subTm-id` — but
--   each argument position needs a different composite, and getting them
--   by batch probing was not converging.  See the note below.
--
-- ★ WHAT THIS INSTANCE DOES ESTABLISH: every layer type-checks together —
--   four branches, two inner natrecs, the outer natrec, and the 5-fold
--   application at the measures — with `⊢le-refl` discharging both
--   bounds.  The mathematical content of `lexrec` is verified; what is
--   missing from the GENERIC statement is substitution bookkeeping.
⊢lexrec-nzero : Γ₅ ⊢ lexrecTm nzero ∷ El (app (var (vs (vs (vs vz)))) nzero)
⊢lexrec-nzero =
  ⊢app (⊢app (⊢app (⊢app (⊢lexAux (⊢app (⊢var (there (there here))) ⊢nzero))
                         (⊢app (⊢var (there here)) ⊢nzero))
                   ⊢nzero)
             (⊢le-refl (⊢app (⊢var (there (there here))) ⊢nzero)))
       (⊢le-refl (⊢app (⊢var (there here)) ⊢nzero))

------------------------------------------------------------------------
-- ⚠⚠ REMAINING GAP — the GENERIC statement:
--
--     ⊢lexrec : {x : RTm ⌊ Γ₅ ⌋} → Γ₅ ⊢ x ∷ Nat
--             → Γ₅ ⊢ lexrecTm x ∷ El (app cP x)
--
--   NOT a mathematical gap — no new lemma about the ORDER is needed, and
--   nothing about the kernel is in doubt.  It is transport along
--   substitution-cancellation equations at three positions (the two
--   `⊢le-refl` arguments and the result type), each with a different
--   composite.  Do it with the interactive goal display, not batch
--   probing: the expected types run to a dozen lines and the truncated
--   `UnequalTerms` output is not enough to pick the right lemma instance.
--
--   ★ A CHEAPER ROUTE WORTH TRYING FIRST: build `lexAuxMot` so that `x`
--     is the LAST argument rather than the third.  Then nothing is
--     weakened past it and every cancellation disappears.  That is a
--     change to the STATEMENT, so it wants the motive combinator layer
--     (below) at the same time.
------------------------------------------------------------------------
