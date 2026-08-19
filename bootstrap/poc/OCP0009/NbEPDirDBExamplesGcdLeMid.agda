------------------------------------------------------------------------
-- OCP-0009 — EQUATION 4: gcd's STEP, WITH THE DESCENT ABSTRACTED.
--
-- ★ WHAT THIS IS FOR.  Equation 4's `⟶*` premise is unsatisfiable at
--   variables, so the descent must be rewritten PROPOSITIONALLY (see
--   `⊢monusLe`, the bridge).  Transport needs the step application as a
--   ONE-HOLE context with the descent as the hole — that is `midAt`.
--
-- ★★ HOW IT WAS FOUND, and the technique is the reusable part: NOT by
--   hand-composing gcd's substitution stack, which is where this kind of
--   work usually dies.  Instead state the chain with a deliberately WRONG
--   target (`⟶* nzero`) and read the real endpoint out of Agda's
--   mismatch message, one layer at a time.  Four probes gave `Zt`/`St`,
--   then `W`, then the shape, then the descent.
--
-- ⚠ AND THE ONE THAT COST A CYCLE: after the substitution stack the
--   descent is NOT syntactically `monus (nsuc a') (nsuc b')` — it is the
--   SUBSTITUTED form `D3'`, equal only propositionally (`wkS3`/`wkS3e`).
--   That is exactly why `gcd-le-term` carries `mhAt` to rewrite it, so the
--   propositional route pays at the same place the reductional one did.
--
-- ⇒ `subTm (single (D3' a' b')) F` is the chain's endpoint;
--   `subTm (single nzero) F` is where `natrec-zero` fires and gcd's
--   existing tail chain runs unchanged.  `congAt F` bridges them.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdLeMid where

open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTm; RTy; Nat; pair; nsuc; nzero; natrec; app
        ; subTm; subTy; extS; renTm; vs; var; vz; _∘ₛ_; subTy-subTy; subTy-cong; Var; Sub )
open import poc.OCP0009.NbEPDirDBType
  using ( _⟶*_; _⟶_; β; βfst; βsnd; ξ-appˡ; natrec-suc; natrec-zero; single )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-appˡ; ⟶*-natrecⁿ )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ⌊_⌋; _⊢_∷_; _⊢ty_; _▹_; ⊢natrec; ⊢pair; ⊢nsuc; ⊢var; here; there; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj
  using ( sub-lemma; sub-ty; Sub⊢; Sub⊢-ext; ⊢single; ⊢-cast; ⊢wk )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( nrs-w )
open import poc.OCP0009.NbEPDirDBLibNatrec using ( na-z; na-s; ⊢natrec-at; Sub⊢-∘ )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; G1z; gcdInn1; G2z; gcdInn2; G3z; G3s
        ; PAIRᶻ; CERTᶻ; one; _⟫_; wkS3; wkS3e
        ; G1; ⊢G1; ⊢G1z; ⊢gcdInn1; wkS2; G2; ⊢G2; ⊢G2z; ⊢gcdInn2 )
open import poc.OCP0009.NbEPDirDBType using ( single; nrs )

gXx : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
gXx x y = pair (nsuc x) (nsuc y)

R1' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
R1' x y = natrec (subTm (single (gXx x y)) G1z)
                 (subTm (extS (extS (single (gXx x y)))) gcdInn1) y

W' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
W' x y = subTm (single (R1' x y))
           (subTm (extS (single y)) (renTm vs (renTm vs x)))

R2' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
R2' x y = natrec (subTm (single (R1' x y))
                    (subTm (extS (single y))
                      (subTm (extS (extS (single (gXx x y)))) G2z)))
                 (subTm (extS (extS (single (R1' x y))))
                   (subTm (extS (extS (extS (single y))))
                     (subTm (extS (extS (extS (extS (single (gXx x y)))))) gcdInn2)))
                 (W' x y)

-- ★ the third natrec's branches, with the SAME substitution stack pushed onto
-- `G3z`/`G3s` separately — sound because `subTm` distributes over `natrec`
Z3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
Z3' x y = subTm (single (R2' x y))
            (subTm (extS (single (W' x y)))
              (subTm (extS (extS (single (R1' x y))))
                (subTm (extS (extS (extS (single y))))
                  (subTm (extS (extS (extS (extS (single (gXx x y)))))) G3z))))

S3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm ((Γ ∙) ∙)
S3' x y = subTm (extS (extS (single (R2' x y))))
            (subTm (extS (extS (extS (single (W' x y)))))
              (subTm (extS (extS (extS (extS (single (R1' x y))))))
                (subTm (extS (extS (extS (extS (extS (single y))))))
                  (subTm (extS (extS (extS (extS (extS (extS (single (gXx x y))))))))
                         G3s))))

-- ⚠ the descent as the substitution stack ACTUALLY leaves it — equal to
--   `monus (nsuc a') (nsuc b')` only PROPOSITIONALLY (`wkS3`/`wkS3e`),
--   which is exactly why `gcd-le-term` needs `mhAt` to rewrite it.
D3' : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
D3' x y = subTm (single (R2' x y))
            (subTm (extS (single (W' x y)))
              (subTm (extS (extS (single (R1' x y))))
                (subTm (extS (extS (extS (single y))))
                  (subTm (extS (extS (extS (extS (single (gXx x y))))))
                         (monusTm (nsuc (var (vs vz)))
                                  (nsuc (var (vs (vs (vs vz))))))))))

midAt : {Γ : Cx} (a' b' ih d : RTm Γ) → RTm Γ
midAt a' b' ih d = app (natrec (Z3' a' b') (S3' a' b') d) ih

MID : {Γ : Cx} (a' b' ih : RTm Γ) → RTm Γ
MID a' b' ih = midAt a' b' ih (D3' a' b')

-- ★★★ THE mh-FREE PREFIX.  Every step here unfolds a CONSTRUCTOR-headed
--     scrutinee, so none of it needs the branch premise — which is why the
--     chain can be split here at all.
gcd-le-prefix : {Γ : Cx} (a' b' ih : RTm Γ) →
                app (app gcdStp (pair (nsuc a') (nsuc b'))) ih ⟶* MID a' b' ih
gcd-le-prefix a' b' ih =
  ( one (ξ-appˡ (β gcdBody (gXx a' b')))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βsnd _ _)))
  ⟫ ⟶*-appˡ (one (natrec-suc (subTm (single (gXx a' b')) G1z)
                             (subTm (extS (extS (single (gXx a' b')))) gcdInn1)
                             b'))
  ⟫ ⟶*-appˡ (⟶*-natrecⁿ (one (βfst _ _)))
  ⟫ ⟶*-appˡ (one (natrec-suc _ _ (W' a' b')))
  )

------------------------------------------------------------------------
-- ★★★ THE TAIL, AT A LITERAL ZERO.
--
-- ⭐ THIS IS THE WHOLE POINT OF THE PROPOSITIONAL ROUTE.  At `nzero` the
--   third `natrec` FIRES (`natrec-zero` selects `G3z`) and one β-step
--   reaches the recursive call.  Both are ordinary reductions needing no
--   premise, because the scrutinee is now a literal CONSTRUCTOR instead of
--   a stuck term.  The reduction that is impossible at a variable is
--   trivial here, and the bridge's `Id` carries the result back.
------------------------------------------------------------------------

-- the substitution stack the two `G3z` components land under
σz : {Γ : Cx} (a' b' ih : RTm Γ) → RTm ((((((Γ ∙) ∙) ∙) ∙) ∙) ∙) → RTm Γ
σz a' b' ih t =
  subTm (single ih)
    (subTm (extS (single (R2' a' b')))
      (subTm (extS (extS (single (W' a' b'))))
        (subTm (extS (extS (extS (single (R1' a' b')))))
          (subTm (extS (extS (extS (extS (single b')))))
            (subTm (extS (extS (extS (extS (extS (single (gXx a' b'))))))) t)))))

-- the recursive call `gcd (suc a', (suc b') ∸ (suc a'))`, with certificate
RHSz : {Γ : Cx} (a' b' ih : RTm Γ) → RTm Γ
RHSz a' b' ih = app (σz a' b' ih (app (var vz) PAIRᶻ)) (σz a' b' ih CERTᶻ)

gcd-le-tail : {Γ : Cx} (a' b' ih : RTm Γ) →
              midAt a' b' ih nzero ⟶* RHSz a' b' ih
gcd-le-tail a' b' ih =
  ( ⟶*-appˡ (one (natrec-zero (Z3' a' b') (S3' a' b')))
  ⟫ one (β _ ih)
  )

------------------------------------------------------------------------
-- ★★ AND THE DESCENT IS THE CLEAN ONE, up to the two weakening peels the
--    reductional proof already carries.  `gcd-le-term` spends these inside
--    `mhAt`; the propositional route spends them here, once.
------------------------------------------------------------------------

D3-clean : {Γ : Cx} (a' b' : RTm Γ) →
           D3' a' b' ≡ monusTm (nsuc a') (nsuc b')
D3-clean a' b' = cong₂ (λ x y → monusTm (nsuc x) (nsuc y))
                       (wkS3 a') (wkS3e b')

------------------------------------------------------------------------
-- ⚠⚠ THE NEXT OBSTACLE, MEASURED — TYPING THE ONE-HOLE CONTEXT.
--
-- Everything above is `⟶*`, which is UNTYPED, so none of it needed a
-- typing derivation.  `congAt` is a `⊢` statement, so the transport needs
--
--     (Γ ▹ El ⌜Nat⌝) ⊢ <one-hole context> ∷ Nat
--
-- and that is the price of going propositional; the reductional proof
-- never pays it because it never needs the term well-typed.
--
-- ⚠ AND IT CANNOT BE INHERITED.  Two routes are closed, both checked:
--   * SUBJECT REDUCTION — `…SR` records general SR as an "HONEST CEILING
--     (the real obstruction, not a gap)"; only a concrete instance exists.
--     So the typing of an intermediate state does NOT follow from
--     `⊢gcdStp` plus the chain.
--   * REUSING `⊢G1`/`⊢G2`/`⊢G3` DIRECTLY — MEASURED, does not typecheck:
--     `⊢G1` lives in `Γ ▹ PairT ▹ Nat`, while `R1'` sits in plain `Γ`
--     after `single gX`.  The generalized sibling slots (`B`, `C`, `D`)
--     make these context-POLYMORPHIC in their siblings, not in their own
--     prefix, so they do not transport across the substitution.
--   ⚠ And `subTm` does not invert (see `…GcdStep`'s note at `⊢gcdInn2`),
--     so the sub-derivations cannot be recovered from `⊢gcdStp` either.
--
-- ⇒ SO EACH LAYER NEEDS ITS OWN DERIVATION, by the substitution lemma:
--   typings for `gXx`, `R1'`, `W'`, `R2'`, then `⊢G3`/`⊢G3z`/`⊢G3s` pushed
--   through the stack, then `⊢natrec-var` (which wants the branches
--   WEAKENED — so build `F` from `w (Z3' a' b')`, not `Z3' (w a') (w b')`,
--   and the peels cancel by `wk-single`).
--
--   That is ~12 substitution-lemma applications with their `Sub⊢`
--   derivations.  Real work, well-defined, no known obstruction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★★ THE TYPING HALF — LAYER BY LAYER, BY THE SUBSTITUTION LEMMA.
--
-- Neither shortcut is available (see the note above), so each intermediate
-- state gets its own derivation.  The recipe is uniform: `⊢single` for the
-- substitution, `Sub⊢-ext` once per binder the target sits under, then
-- `sub-ty` for motives and `sub-lemma` for terms.
------------------------------------------------------------------------

⊢gXx : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋} →
       Γ ⊢ a' ∷ Nat → Γ ⊢ b' ∷ Nat → Γ ⊢ gXx a' b' ∷ PairT
⊢gXx da db = ⊢pair ty-Nat (⊢nsuc da) (⊢nsuc db)

-- ★★★ LAYER 1, IN ONE LINE.  `⊢natrec-at`'s conclusion is
--     `natrec (subTm σ z) (subTm (extS² σ) s) n`
--   which is EXACTLY `R1'` at σ = `single gX`, z = `G1z`, s = `gcdInn1`,
--   n = `b'`, M = `G1`.  It performs the `na-z`/`na-s` casts internally.
--
-- ⚠ I hand-wrote those casts as `peelZ`/`peelS` before finding the lemma —
--   ~25 lines, now deleted.  See `…LibNatrec`'s header.
⊢R1' : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) →
       Γ ⊢ R1' a' b'
         ∷ subTy (single b') (subTy (extS (single (gXx a' b'))) G1)
⊢R1' da db = ⊢natrec-at ⊢G1 ⊢G1z ⊢gcdInn1 (⊢single (⊢gXx da db)) db

-- ★ layer 2: `W'` is `a'` IN DISGUISE.  `wkS2` is exactly its shape — two
--   weakenings cancelled by two substitutions — so no new work.
⊢W' : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋} →
      Γ ⊢ a' ∷ Nat → Γ ⊢ b' ∷ Nat → Γ ⊢ W' a' b' ∷ Nat
-- ⚠ the TERM moves here, not the type — `⊢-cast` is for types, so this
--   is a `subst` on the subject position.
⊢W' {Γ} {a' = a'} da db = subst (λ z → Γ ⊢ z ∷ Nat) (sym (wkS2 a')) da

------------------------------------------------------------------------
-- ★★★ LAYER 3 — `R2'`, ALSO VIA `⊢natrec-at`.
--
-- Same lemma, now at σ = `single R1'`.  The TWO INNER substitution levels
-- (`single gX`, then `single b'`) ride on the motive and branches via
-- `sub-ty`/`sub-lemma`; the outer one is `⊢natrec-at`'s own σ.  No
-- `Sub⊢-∘` composition is needed, and the `na-z`/`na-s` casts are inside
-- the lemma.
--
-- ⚠ `B` PINNED throughout — the generalised sibling slot is `G1` here and
--   cannot be inferred.
------------------------------------------------------------------------

-- ⚠ AND THE INNER LEVELS DO NOT NEED THEIR OWN CASTS EITHER.  `subTm`
--   DISTRIBUTES over `natrec`, so pushing the WHOLE `⊢natrec-at`
--   derivation through the outer substitutions with `sub-lemma` produces
--   the 3-level substituted `natrec` directly — no `na-z` at the inner
--   levels, which is what the hand-written version needed.
⊢R2' : {Γ : Ctx} {a' b' : RTm ⌊ Γ ⌋}
       (da : Γ ⊢ a' ∷ Nat) (db : Γ ⊢ b' ∷ Nat) → _
⊢R2' da db =
  sub-lemma (sub-lemma (⊢natrec-at (⊢G2 {B = G1}) (⊢G2z {B = G1})
                                   (⊢gcdInn2 {B = G1})
                                   (Sub⊢-ext (Sub⊢-ext (⊢single (⊢gXx da db))))
                                   (⊢wk (⊢wk da)))
                       (Sub⊢-ext (⊢single db)))
            (⊢single (⊢R1' da db))
