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

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Sub; subTm; subTy; extS; renTm
        ; subTy-subTy; subTy-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there; ⊢natrec; ⊢nzero; ⊢nsuc
        ; ⊢fst; ⊢snd; ⊢pair; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; sub-ty; sub-lemma; Sub⊢; Sub⊢-ext; ⊢single; ⊢[] )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( subren; renren )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1 )

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

module GcdCertAt {Δ : Ctx} {a' b' : RTm ⌊ Δ ⌋}
                 (da : Δ ⊢ a' ∷ Nat) (db : Δ ⊢ b' ∷ Nat) where

  gX : RTm ⌊ Δ ⌋
  gX = pair (nsuc a') (nsuc b')

  ⊢gX : Δ ⊢ gX ∷ PairT
  ⊢gX = ⊢pair ty-Nat (⊢nsuc da) (⊢nsuc db)

  ⊢R₁ : Δ ⊢ natrec (subTm (single gX) G1z)
                   (subTm (extS (extS (single gX))) gcdInn1) b'
        ∷ subTy (single b') (subTy (extS (single gX)) G1)
  ⊢R₁ = ⊢natrec-at ⊢G1 ⊢G1z ⊢gcdInn1 (⊢single ⊢gX) db
