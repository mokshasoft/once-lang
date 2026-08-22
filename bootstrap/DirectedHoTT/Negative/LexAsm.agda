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
module DirectedHoTT.Negative.LexAsm where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; subst )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; Var; vz; vs
        ; RTy; El; Hom; Nat
        ; RTm; var; nzero; nsuc; natrec; lam; app
        ; Π; renTy; subTy; renTm; subTm; extS
        ; subTm-renTm; subTm-subTm; subTm-id )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; ⊢var; here; there; ⊢natrec; ⊢lam; ⊢app; ⊢nzero
        ; ty-Nat; wk-single )
open import DirectedHoTT.Lib.Strong using ( ⊢le-refl; reflTm )
open import DirectedHoTT.Negative.Lex
  using ( Γ₅; LStepT; lexAuxMot; M0lex; M1lex; ⊢lexAuxMot; ⊢M0lex; ⊢M1lex
        ; lexZBr; lexSBr; lexAuxTm )
open import DirectedHoTT.Negative.LexZZ using ( ⊢lexZZ )
open import DirectedHoTT.Negative.LexZS using ( ⊢lexZS )
open import DirectedHoTT.Negative.LexSZ using ( ⊢lexSZ )
open import DirectedHoTT.Negative.LexSS using ( ⊢lexSS )

-- the n₁ = 0 branch of the OUTER recursion: bind n₂, recurse on it.
⊢lexZBr : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
          Γ₅ ⊢ lexZBr stpTm ∷ subTy (single nzero) lexAuxMot
⊢lexZBr stpTm dstp =
  ⊢lam ty-Nat (⊢natrec ⊢M0lex (⊢lexZZ stpTm dstp) (⊢lexZS stpTm dstp) (⊢var here))

-- the n₁ = suc branch: same shape, at the motive whose μ₁ bound is suc n₁'.
⊢lexSBr : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
          ((Γ₅ ▹ Nat) ▹ lexAuxMot) ⊢ lexSBr stpTm ∷ subTy nrs lexAuxMot
⊢lexSBr stpTm dstp =
  ⊢lam ty-Nat (⊢natrec ⊢M1lex (⊢lexSZ stpTm dstp) (⊢lexSS stpTm dstp) (⊢var here))

-- ★ THE OUTER RECURSION.  Generic in the bound, as `⊢strong-base'` is —
--   so `lexrec` can instantiate it at μ₁ x.
⊢lexAux : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
          {n : RTm ⌊ Γ₅ ⌋} → Γ₅ ⊢ n ∷ Nat →
          Γ₅ ⊢ lexAuxTm stpTm n ∷ subTy (single n) lexAuxMot
⊢lexAux stpTm dstp dn =
  ⊢natrec ⊢lexAuxMot (⊢lexZBr stpTm dstp) (⊢lexSBr stpTm dstp) dn

------------------------------------------------------------------------
-- ★★ LEXREC ITSELF:  lexrec x = aux (μ₁ x) (μ₂ x) x (le-refl _) (le-refl _)
--
--   Both bounds are discharged by REFLEXIVITY.  That is the point of the
--   doubly-bounded auxiliary: it is strong enough that the top-level call
--   needs nothing but `μ₁ x ≤ μ₁ x` and `μ₂ x ≤ μ₂ x`.
------------------------------------------------------------------------

lexrecTm : RTm ⌊ Γ₅ ⌋ → RTm ⌊ Γ₅ ⌋ → RTm ⌊ Γ₅ ⌋
lexrecTm stpTm x =
  app (app (app (app (lexAuxTm stpTm (app (var (vs vz)) x)) (app (var vz) x)) x) (reflTm (app (var (vs vz)) x))) (reflTm (app (var vz) x))

-- ⚠ `⊢lexrec-nzero` IS GONE, and not because it broke — because at a
--   GENERIC carrier it cannot be stated.  It instantiated x := nzero,
--   which typechecked only while the carrier WAS `Nat`.  `El A` for a
--   context variable `A : U` has no closed inhabitant, so the cheapest
--   whole-stack instance is now an actual carrier: see the Ackermann
--   file, which instantiates A := ⌜Σ⌝ ⌜Nat⌝ ⌜Nat⌝.

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

⊢lexrec : (stpTm : RTm ⌊ Γ₅ ⌋) (dstp : Γ₅ ⊢ stpTm ∷ LStepT) →
          {x : RTm ⌊ Γ₅ ⌋} → Γ₅ ⊢ x ∷ El (var (vs (vs (vs vz)))) →
          Γ₅ ⊢ lexrecTm stpTm x ∷ El (app (var (vs (vs vz))) x)
⊢lexrec stpTm dstp {x} dx =
  subst (λ t → Γ₅ ⊢ lexrecTm stpTm x ∷ El (app (var (vs (vs vz))) t)) (cancel2 x {reflTm (app (var (vs vz)) x) } {reflTm (app (var vz) x) }) (⊢app (⊢app (⊢app (⊢app (⊢lexAux stpTm dstp (⊢app (⊢var (there here)) dx)) (⊢app (⊢var here) dx)) dx) (subst (λ t → Γ₅ ⊢ reflTm (app (var (vs vz)) x) ∷ Hom Nat (app (var (vs vz)) x) (app (var (vs vz)) t)) (sym (cancel2 x {app (var vz) x} {x})) (⊢le-refl (⊢app (⊢var (there here)) dx)))) (⊢Hom₂ (cong (app (var vz)) (sym (wk-single {v = reflTm (app (var (vs vz)) x) } x))) (cong (app (var vz)) (sym (cancel2 x {x} {reflTm (app (var (vs vz)) x) }))) (⊢le-refl (⊢app (⊢var here) dx))))
