------------------------------------------------------------------------
-- OCP-0009 — LEXREC, ASSEMBLED.  The four branches are derived in
-- NbEPDirDBExamplesLex{ZZ,ZS,SZ,SS}; this module stacks them.
--
--   ⊢lexZBr  inner natrec on n₂ at n₁ = 0        (lexZZ / lexZS)
--   ⊢lexSBr  inner natrec on n₂ at n₁ = suc n₁'  (lexSZ / lexSS)
--   ⊢lexAux  OUTER natrec on n₁                  (lexZBr / lexSBr)
--   ⊢lexrec  aux applied at μ₁ x, μ₂ x, x, and two ⊢le-refl's — GENERIC
--            in x, so it composes as a library lemma
--
-- ★ THIS IS WHERE THE MOTIVES GET TESTED AGAINST EACH OTHER.  `⊢natrec`
--   demands that the base sit at `subTy (single nzero) M` and the step at
--   `subTy nrs M` for the SAME M — so M0lex/M1lex/lexAuxMot can no longer
--   be three independently hand-counted terms that merely look related.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesLexAsm where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; natrec; lam; app
        ; Π; renTy; subTy; renTm; subTm; extS
        ; subTm-renTm; subTm-subTm; subTm-id )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢natrec; ⊢lam; ⊢app; ⊢nzero
        ; ty-Nat )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
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

-- ★ A CONCRETE SANITY INSTANCE, kept because it is the cheapest possible
--   regression test on the whole stack: if any layer breaks, this fails in
--   seconds, whereas the generic `⊢lexrec` below drags in the transports.
⊢lexrec-nzero : Γ₅ ⊢ lexrecTm nzero ∷ El (app (var (vs (vs (vs vz)))) nzero)
⊢lexrec-nzero =
  ⊢app (⊢app (⊢app (⊢app (⊢lexAux (⊢app (⊢var (there (there here))) ⊢nzero))
                         (⊢app (⊢var (there here)) ⊢nzero))
                   ⊢nzero)
             (⊢le-refl (⊢app (⊢var (there (there here))) ⊢nzero)))
       (⊢le-refl (⊢app (⊢var (there here)) ⊢nzero))

------------------------------------------------------------------------
-- ★★ THE GENERIC `⊢lexrec`.
--
-- ⚠ WHY TRANSPORT IS UNAVOIDABLE — it is NOT an argument-order artifact.
--   `le` and `lt` both MENTION x, so x must be bound before them; and the
--   conclusion `El (cP x)` mentions x too.  So in ANY ordering there are
--   binders between x and its use, and applying the later arguments must
--   substitute that weakening back.  For a concrete x it computes; for an
--   abstract one it needs `cancel2`.
--
--   The composite really is the identity: weakening by `vs` twice then
--   substituting twice sends `y ↦ var (vs y) ↦ var y`.  Proved from
--   `subTm-renTm` (fuse sub∘ren), `subTm-subTm` (fuse sub∘sub) and
--   `subTm-id` — the fused substitution is `idₛ` DEFINITIONALLY, by eta.
------------------------------------------------------------------------

cancel2 : (t : RTm ⌊ Γ₅ ⌋) {a b : RTm ⌊ Γ₅ ⌋} →
          subTm (single b) (subTm (extS (single a)) (renTm vs (renTm vs t))) ≡ t
cancel2 t =
  trans (cong (subTm (single _))
              (trans (subTm-renTm (renTm vs t)) (subTm-renTm t)))
        (trans (subTm-subTm t) (subTm-id t))

-- transport BOTH endpoints of a `Hom Nat` at once.  Needed because the two
-- endpoints of one argument's expected type can carry DIFFERENT leftover
-- substitutions: at `rec₂` below the source needs `wk-single` (one weakening
-- survived) and the target needs `cancel2` (two did).
⊢Hom₂ : {m t u t' u' : RTm ⌊ Γ₅ ⌋} → t ≡ t' → u ≡ u' →
        Γ₅ ⊢ m ∷ Hom Nat t u → Γ₅ ⊢ m ∷ Hom Nat t' u'
⊢Hom₂ refl refl d = d

⊢lexrec : {x : RTm ⌊ Γ₅ ⌋} → Γ₅ ⊢ x ∷ Nat →
          Γ₅ ⊢ lexrecTm x ∷ El (app (var (vs (vs (vs vz)))) x)
⊢lexrec {x} dx =
  subst (λ t → Γ₅ ⊢ lexrecTm x ∷ El (app (var (vs (vs (vs vz)))) t))
        (cancel2 x {reflTm (app (var (vs (vs vz))) x)}
                   {reflTm (app (var (vs vz)) x)})
        (⊢app (⊢app (⊢app (⊢app (⊢lexAux (⊢app (⊢var (there (there here))) dx))
                                (⊢app (⊢var (there here)) dx))
                          dx)
                    (subst (λ t → Γ₅ ⊢ reflTm (app (var (vs (vs vz))) x)
                                     ∷ Hom Nat (app (var (vs (vs vz))) x)
                                               (app (var (vs (vs vz))) t))
                           (sym (cancel2 x {app (var (vs vz)) x} {x}))
                           (⊢le-refl (⊢app (⊢var (there (there here))) dx))))
              (⊢Hom₂ (cong (app (var (vs vz)))
                            (sym (wk-single {v = reflTm (app (var (vs (vs vz))) x)} x)))
                     (cong (app (var (vs vz)))
                            (sym (cancel2 x {x} {reflTm (app (var (vs (vs vz))) x)})))
                     (⊢le-refl (⊢app (⊢var (there here)) dx))))
