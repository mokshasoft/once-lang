------------------------------------------------------------------------
-- OCP-0009 — TYPING THE RECURSIVE CALL'S CERTIFICATE.
--
-- ★ THE PROBLEM.  gap A's recursive equation needs
--   `Δ ⊢ recCert (gcd-gt-term …) ∷ Hom Nat (nsuc (μ Y)) (μ X)`.  That
--   certificate is `CERTˢ` under EIGHT substitutions, and `subTm` does not
--   invert, so subject reduction cannot produce a typing for it.
--
-- ⚠⚠ AND PEELING IT IS THE WRONG MOVE — measured 2026-08-17.  Saying what
--   the certificate EQUALS (`≡ ⊢desc-left`'s subject) forces Agda to
--   normalise `plusMonoLTm` under all eight layers, i.e. through
--   `trHomʳ`/`trHomˡ`/`congS`/`commTm`/`jsub`.  Done inside `gcd-gt-term`
--   that took `…GcdStep` from 31s to over 10 MINUTES.
--
-- ⭐ THE FIX: DO NOT SAY WHAT IT EQUALS, SAY WHY IT IS WELL-TYPED.
--   `sub-lemma` acts on the DERIVATION, not on the term's normal form, so
--   applying it ONCE PER LAYER never normalises the certificate at all.
--   `⊢CERTˢ` (named in prerequisite 1) is the seed; eight `Sub⊢`s carry it
--   down.  The `sub`-naturality lemmas added to `…LibArithComm` are not
--   needed on this route — they stand on their own as library lemmas.
--
-- ★ AND THE `Sub⊢`s ARE THE REAL CONTENT: they demand typings for the
--   reduction's intermediate scrutinees `R₁`/`W`/`R₂`/`R₃`, i.e. exactly
--   what `⊢gcdStp` already knows about gcd's three nested `natrec`s, said
--   at a general scrutinee rather than at `snd x`/`fst x`/`a ∸ b`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdCert where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Sub; subTm; subTy; extS; renTm; _∘ₛ_
        ; subTy-subTy; subTy-cong; subTm-subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢natrec; ⊢nzero; ⊢nsuc
        ; ⊢fst; ⊢snd; ⊢pair; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; sub-ty; sub-lemma; Sub⊢; Sub⊢-ext; ⊢single; ⊢[] )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( subren; renren )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2; wkS2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s
        ; CERTˢ; ⊢CERTˢ; PAIRˢ; KS; NS; gcdIH )

------------------------------------------------------------------------
-- ★★★ A `natrec`'s TYPING, TRANSPORTED ALONG A SUBSTITUTION.
--
-- ⚠ GENERAL — nothing gcd-specific here; it belongs beside `⊢natrec-var`
--   in the WF library (see FUTURE.md).  `⊢natrec-var` re-types a `natrec`
--   at a VARIABLE scrutinee; this one re-types it at an ARBITRARY scrutinee
--   under an arbitrary substitution of the ambient context, which is what a
--   reduction's intermediate scrutinees need.
--
-- ★ Two casts, and both are the same shape: a substitution meeting
--   `single nzero` resp. `nrs`, decided variable-by-variable.
------------------------------------------------------------------------

module _ {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {M : RTy (⌊ Γ ⌋ ∙)} where

  na-z : subTy (single nzero) (subTy (extS σ) M)
       ≡ subTy σ (subTy (single nzero) M)
  na-z = trans (subTy-subTy M) (trans (subTy-cong br M) (sym (subTy-subTy M)))
    where
      br : ∀ v → subTm (single nzero) (extS σ v) ≡ subTm σ (single nzero v)
      br vz     = refl
      br (vs u) = wk-single {v = nzero} (subTm σ (var u))

  na-s : subTy nrs (subTy (extS σ) M)
       ≡ subTy (extS (extS σ)) (subTy nrs M)
  na-s = trans (subTy-subTy M) (trans (subTy-cong br M) (sym (subTy-subTy M)))
    where
      br : ∀ v → subTm nrs (extS σ v) ≡ subTm (extS (extS σ)) (nrs v)
      br vz     = refl
      br (vs u) =
        trans (subren {σ = nrs} {ρ = vs} {ρ' = λ x → vs (vs x)}
                      (λ _ → refl) (subTm σ (var u)))
              (sym (renren {ϑ = vs} {ρ = vs} {ρ' = λ x → vs (vs x)}
                           (λ _ → refl) (subTm σ (var u))))

-- ★ TYPED SUBSTITUTIONS COMPOSE.  ⚠ Also general, also missing from
--   `…Subj`.  One line: substitute the derivation `σ⊢` gives, then fuse the
--   two `subTy`s.  Needed because the reduction's scrutinees live three and
--   five slots deep, so their `Sub⊢`s are composites.
Sub⊢-∘ : {Γ Δ Θ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {τ : Sub ⌊ Δ ⌋ ⌊ Θ ⌋} →
         Sub⊢ Γ Δ σ → Sub⊢ Δ Θ τ → Sub⊢ Γ Θ (τ ∘ₛ σ)
Sub⊢-∘ {σ = σ} {τ = τ} σ⊢ τ⊢ {A = A} v =
  ⊢-cast (subTy-subTy A) (sub-lemma (σ⊢ v) τ⊢)

-- ★ …and the lemma itself.  Three lines; the two casts above are all of it.
⊢natrec-at : {Γ Δ : Ctx} {σ : Sub ⌊ Γ ⌋ ⌊ Δ ⌋} {M : RTy (⌊ Γ ⌋ ∙)}
             {z : RTm ⌊ Γ ⌋} {s : RTm ((⌊ Γ ⌋ ∙) ∙)} {n : RTm ⌊ Δ ⌋} →
             (Γ ▹ Nat) ⊢ty M →
             Γ ⊢ z ∷ subTy (single nzero) M →
             ((Γ ▹ Nat) ▹ M) ⊢ s ∷ subTy nrs M →
             Sub⊢ Γ Δ σ → Δ ⊢ n ∷ Nat →
             Δ ⊢ natrec (subTm σ z) (subTm (extS (extS σ)) s) n
               ∷ subTy (single n) (subTy (extS σ) M)
⊢natrec-at dM dz ds σ⊢ dn =
  ⊢natrec (sub-ty dM (Sub⊢-ext σ⊢))
          (⊢-cast (sym na-z) (sub-lemma dz σ⊢))
          (⊢-cast (sym na-s) (sub-lemma ds (Sub⊢-ext (Sub⊢-ext σ⊢))))
          dn

------------------------------------------------------------------------
-- ★★ THE REDUCTION'S INTERMEDIATE SCRUTINEES, TYPED.
--
-- `R₁` is `gcd`'s outer `natrec` at the carrier `gX` and the PREDECESSOR
-- `b'` — i.e. the recursive call `natrec-suc` hands over.  ⭐ One line,
-- because `⊢natrec-at` takes exactly the data `⊢gcdStp` already names.
------------------------------------------------------------------------

module GcdCertAt {Δ : Ctx} {a' b' d : RTm ⌊ Δ ⌋}
                 (da : Δ ⊢ a' ∷ Nat) (db : Δ ⊢ b' ∷ Nat)
                 (dd : Δ ⊢ d ∷ Nat) where

  gX : RTm ⌊ Δ ⌋
  gX = pair (nsuc a') (nsuc b')

  ⊢gX : Δ ⊢ gX ∷ PairT
  ⊢gX = ⊢pair ty-Nat (⊢nsuc da) (⊢nsuc db)

  R₁ : RTm ⌊ Δ ⌋
  R₁ = natrec (subTm (single gX) G1z)
              (subTm (extS (extS (single gX))) gcdInn1) b'

  ⊢R₁ : Δ ⊢ R₁ ∷ subTy (single b') (subTy (extS (single gX)) G1)
  ⊢R₁ = ⊢natrec-at ⊢G1 ⊢G1z ⊢gcdInn1 (⊢single ⊢gX) db

  ------------------------------------------------------------------------
  -- ★ `W` — the descent's first argument, `a ∸ b`, after the outer
  --   substitutions.  ⚠ It is `a'` only PROPOSITIONALLY (`wkS2`), so the
  --   typing moves by `subst` on the TERM, not `⊢-cast` on the type.
  ------------------------------------------------------------------------

  W : RTm ⌊ Δ ⌋
  W = subTm (single R₁) (subTm (extS (single b')) (renTm vs (renTm vs a')))

  ⊢W : Δ ⊢ W ∷ Nat
  ⊢W = subst (λ t → Δ ⊢ t ∷ Nat) (sym (wkS2 {u = R₁} {v = b'} a')) da

  ------------------------------------------------------------------------
  -- ★ THE EIGHT SUBSTITUTION LAYERS, NAMED — one per slot of `CΓs`, in the
  --   order the reduction applied them.  Naming them is what keeps the rest
  --   of this module readable; spelled out, `σH` is a page wide.
  ------------------------------------------------------------------------

  σA : Sub (⌊ Δ ⌋ ∙) ⌊ Δ ⌋
  σA = single gX

  σB : Sub (⌊ Δ ⌋ ∙ ∙) ⌊ Δ ⌋
  σB = single b' ∘ₛ extS σA

  σC : Sub (⌊ Δ ⌋ ∙ ∙ ∙) ⌊ Δ ⌋
  σC = single R₁ ∘ₛ extS σB

  σA⊢ : Sub⊢ (Δ ▹ PairT) Δ σA
  σA⊢ = ⊢single ⊢gX

  σB⊢ : Sub⊢ ((Δ ▹ PairT) ▹ Nat) Δ σB
  σB⊢ = Sub⊢-∘ {σ = extS σA} {τ = single b'}
               (Sub⊢-ext {C = Nat} σA⊢) (⊢single db)

  σC⊢ : Sub⊢ (((Δ ▹ PairT) ▹ Nat) ▹ G1) Δ σC
  σC⊢ = Sub⊢-∘ {σ = extS σB} {τ = single R₁}
               (Sub⊢-ext {C = G1} σB⊢)
               (⊢single (⊢-cast (subTy-subTy {τ = single b'} {σ = extS σA} G1) ⊢R₁))

  ------------------------------------------------------------------------
  -- ★ …and the same one-liner at each deeper scrutinee.  ⚠ Every implicit
  --   substitution is PINNED: one that occurs only in APPLIED position is a
  --   higher-order pattern Agda solves partway and then blocks on.
  ------------------------------------------------------------------------

  R₂ : RTm ⌊ Δ ⌋
  R₂ = natrec (subTm σC G2z) (subTm (extS (extS σC)) gcdInn2) W

  ⊢R₂ : Δ ⊢ R₂ ∷ subTy (single W) (subTy (extS σC) G2)
  ⊢R₂ = ⊢natrec-at ⊢G2 ⊢G2z ⊢gcdInn2 σC⊢ ⊢W

  σD : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σD = single W ∘ₛ extS σC

  σD⊢ : Sub⊢ ((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) Δ σD
  σD⊢ = Sub⊢-∘ {σ = extS σC} {τ = single W}
               (Sub⊢-ext {C = Nat} σC⊢) (⊢single ⊢W)

  σE : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σE = single R₂ ∘ₛ extS σD

  σE⊢ : Sub⊢ (((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) Δ σE
  σE⊢ = Sub⊢-∘ {σ = extS σD} {τ = single R₂}
               (Sub⊢-ext {C = G2} σD⊢)
               (⊢single (⊢-cast (subTy-subTy {τ = single W} {σ = extS σC} G2) ⊢R₂))

  ------------------------------------------------------------------------
  -- ★ the LAST scrutinee, and the last three layers.
  ------------------------------------------------------------------------

  R₃ : RTm ⌊ Δ ⌋
  R₃ = natrec (subTm σE G3z) (subTm (extS (extS σE)) G3s) d

  ⊢R₃ : Δ ⊢ R₃ ∷ subTy (single d) (subTy (extS σE) G3)
  ⊢R₃ = ⊢natrec-at ⊢G3 ⊢G3z ⊢G3s σE⊢ dd

  σF : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σF = single d ∘ₛ extS σE

  σF⊢ : Sub⊢ ((((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ▹ Nat) Δ σF
  σF⊢ = Sub⊢-∘ {σ = extS σE} {τ = single d}
               (Sub⊢-ext {C = Nat} σE⊢) (⊢single dd)

  σG : Sub (⌊ Δ ⌋ ∙ ∙ ∙ ∙ ∙ ∙ ∙) ⌊ Δ ⌋
  σG = single R₃ ∘ₛ extS σF

  σG⊢ : Sub⊢ (((((((Δ ▹ PairT) ▹ Nat) ▹ G1) ▹ Nat) ▹ G2) ▹ Nat) ▹ G3) Δ σG
  σG⊢ = Sub⊢-∘ {σ = extS σF} {τ = single R₃}
               (Sub⊢-ext {C = G3} σF⊢)
               (⊢single (⊢-cast (subTy-subTy {τ = single d} {σ = extS σE} G3) ⊢R₃))

  ------------------------------------------------------------------------
  -- ★★★★ THE CERTIFICATE, TYPED — and `CERTˢ` was never normalised.
  --
  -- ⚠ The `ih` layer is a PARAMETER, not fixed here: `ih` is whatever the
  --   caller passes to the step, and its typing is what the caller has.
  ------------------------------------------------------------------------

  ⊢cert : {ih : RTm ⌊ Δ ⌋} →
          Δ ⊢ ih ∷ subTy σG (gcdIH (plusTm (nsuc (var (vs (vs (vs vz)))))
                                           (nsuc (var (vs (vs (vs (vs (vs vz))))))))) →
          Δ ⊢ subTm (single ih ∘ₛ extS σG) CERTˢ
            ∷ subTy (single ih ∘ₛ extS σG)
                    (Hom Nat (nsuc (plusTm (fst PAIRˢ) (snd PAIRˢ)))
                             (plusTm (nsuc KS) (nsuc NS)))
  ⊢cert {ih = ih} dih =
    sub-lemma ⊢CERTˢ
      (Sub⊢-∘ {σ = extS σG} {τ = single ih}
              (Sub⊢-ext {C = gcdIH (plusTm (nsuc (var (vs (vs (vs vz)))))
                                           (nsuc (var (vs (vs (vs (vs (vs vz))))))))}
                        σG⊢)
              (⊢single dih))

  ------------------------------------------------------------------------
  -- ⚠⚠ NOT DONE: THE NESTED FORM.  `⊢cert` above types the FUSED
  --   `subTm (single ih ∘ₛ extS σG) CERTˢ`; `recCert (gcd-gt-term …)` is
  --   EIGHT NESTED `subTm`s, and the caller needs the nested one.
  --
  --   Both routes to it were tried and both OOM-kill (measured 2026-08-17,
  --   one agda at a time):
  --     * fusing the nested form to the composite — that is exactly the
  --       comparison that costs >10min;
  --     * applying `sub-lemma` one layer at a time, which lands on the
  --       nested form directly.  Expensive even with the subject AND type
  --       written out by hand, so it is not an inference artefact: eight
  --       `Sub⊢-ext` towers over substituted contexts is simply a lot.
  --
  --   ⭐ What IS established: the certificate is typeable by DERIVATION at
  --   6.2s, and every ingredient (`⊢R₁`/`⊢W`/`⊢R₂`/`⊢R₃`, the eight typed
  --   layers) is green and cheap.  The remaining problem is only the SHAPE
  --   the reduction hands over, not the mathematics.
  ------------------------------------------------------------------------
