------------------------------------------------------------------------
-- OCP-0009 · LIBRARY — THE IH-CALL BINDER SHAPE, and its three payloads.
--
-- ★★★ THE OBSERVATION THIS MODULE EXISTS FOR.  Three constructions in this
--   development, written weeks apart by three different lines of work, are
--   THE SAME TYPE with a different body:
--
--     aIHTat' A m mx (El cm)        the IH's OWN type            (…LibRec)
--     pwT     μ i₁ i₂               `StepExt`'s pointwise premise (…GcdStepExt)
--     indPWT  μ ih                  `IndStep`'s pointwise premise (…GcdIndG)
--
--   all of them
--
--       Π A (Π (Hom Nat (nsuc m) mx) <payload>)
--
--   — "for every carrier `y` and every certificate that `μ y < mx`, …".
--   `…LibRec` already had it, with the payload hard-wired to `El cm`.
--
-- ⇒ `ihCallT` is that shape with the payload OPEN, and `aIHTat'` is its
--   instance.  `…ExamplesIHCallAgree` checks all three by `refl`.
--
-- ⚠⚠ AND HERE IS THE HONEST MEASUREMENT OF WHAT THAT BUYS.  `ihCallElim`
--   is TWO `⊢app`s AND NOTHING ELSE.  Every line of `pwElim`'s and
--   `indPWElim`'s bulk was peeling the PAYLOAD — the `w`s on the handles,
--   the `wk-single`s on the bound — and that peel depends on the payload,
--   so it stays with the client.  ⇒ **the binder shape amortises to
--   nothing, because it never cost anything.  The cost was always the
--   payload, and the payload does not amortise.**
--
--   That is worth writing down rather than discovering twice: this
--   consolidation is a STRUCTURAL clarification, not a cost win.
--
-- ★ WHAT IS A REAL WIN is below the fold: `appIHat` and the `aIHTat`
--   weakening tower, both of which `…GcdStepExt` carries at a FIXED
--   carrier and which are carrier-generic here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBLibIHCall where

open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; vz; vs
        ; RTy; El; Nat; Hom; Π
        ; RTm; var; lam; app; nsuc
        ; subTy; subTm; renTy; renTm; Ren; Sub; extS; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢lam; ⊢app; ⊢nsuc; ty-Π; ty-Hom; ty-Nat )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢-cast )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat'; aIHTat )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( aIHTat-ren )

------------------------------------------------------------------------
-- ★ THE SHAPE.
------------------------------------------------------------------------

ihCallT : {Γ : Cx} (A : RTy Γ) (m mx : RTm (Γ ∙)) (P : RTy ((Γ ∙) ∙)) → RTy Γ
ihCallT A m mx P = Π A (Π (Hom Nat (nsuc m) mx) P)

-- ★ …and `…LibRec`'s `aIHTat'` IS its instance at the payload `El cm`.
aIHTat'-is : {Γ : Cx} (A : RTy Γ) (m mx : RTm (Γ ∙)) (cm : RTm ((Γ ∙) ∙)) →
             aIHTat' A m mx cm ≡ ihCallT A m mx (El cm)
aIHTat'-is A m mx cm = refl

⊢ihCallT : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {m mx : RTm (⌊ Γ ⌋ ∙)}
           {P : RTy ((⌊ Γ ⌋ ∙) ∙)} →
           Γ ⊢ty A → (Γ ▹ A) ⊢ m ∷ Nat → (Γ ▹ A) ⊢ mx ∷ Nat →
           ((Γ ▹ A) ▹ Hom Nat (nsuc m) mx) ⊢ty P →
           Γ ⊢ty ihCallT A m mx P
⊢ihCallT dA dm dmx dP = ty-Π dA (ty-Π (ty-Hom ty-Nat (⊢nsuc dm) dmx) dP)

-- ⭐ the two naturality laws are `refl`: the shape is pure `Π`/`Hom`, and
--   every component is a PARAMETER, so `subTy`/`renTy` walk straight in.
--   (Contrast `aIHTat`, whose `w μx`/`w cM` need `aIHTat-sub`.)
ihCallT-sub : {Γ Γ' : Cx} {σ : Sub Γ Γ'}
              (A : RTy Γ) (m mx : RTm (Γ ∙)) (P : RTy ((Γ ∙) ∙)) →
              subTy σ (ihCallT A m mx P)
            ≡ ihCallT (subTy σ A) (subTm (extS σ) m) (subTm (extS σ) mx)
                      (subTy (extS (extS σ)) P)
ihCallT-sub A m mx P = refl

ihCallT-ren : {Γ Γ' : Cx} {ρ : Ren Γ Γ'}
              (A : RTy Γ) (m mx : RTm (Γ ∙)) (P : RTy ((Γ ∙) ∙)) →
              renTy ρ (ihCallT A m mx P)
            ≡ ihCallT (renTy ρ A) (renTm (extR ρ) m) (renTm (extR ρ) mx)
                      (renTy (extR (extR ρ)) P)
ihCallT-ren A m mx P = refl

------------------------------------------------------------------------
-- ★ INTRO AND ELIM.  ⚠ Both are trivial ON PURPOSE — see the header.
------------------------------------------------------------------------

ihCallIntro : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {m mx : RTm (⌊ Γ ⌋ ∙)}
              {P : RTy ((⌊ Γ ⌋ ∙) ∙)} {t : RTm (((⌊ Γ ⌋ ∙) ∙))} →
              Γ ⊢ty A → (Γ ▹ A) ⊢ty Hom Nat (nsuc m) mx →
              ((Γ ▹ A) ▹ Hom Nat (nsuc m) mx) ⊢ t ∷ P →
              Γ ⊢ lam (lam t) ∷ ihCallT A m mx P
ihCallIntro dA dH dt = ⊢lam dA (⊢lam dH dt)

ihCallElim : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {m mx : RTm (⌊ Γ ⌋ ∙)}
             {P : RTy ((⌊ Γ ⌋ ∙) ∙)} {h y q : RTm ⌊ Γ ⌋} →
             Γ ⊢ h ∷ ihCallT A m mx P → Γ ⊢ y ∷ A →
             Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) m)) (subTm (single y) mx) →
             Γ ⊢ app (app h y) q
               ∷ subTy (single q) (subTy (extS (single y)) P)
ihCallElim dh dy dq = ⊢app (⊢app dh dy) dq

-- ★ the CALL ITSELF, which `pwT` and `indPWT` both build by hand:
--   the handle applied to the two bound variables.
ihCall : {Γ : Cx} → RTm Γ → RTm ((Γ ∙) ∙)
ihCall i = app (app (w (w i)) (var (vs vz))) (var vz)

------------------------------------------------------------------------
-- ★★★ THE PART THAT IS A REAL WIN — `aIHTat` at an ARBITRARY carrier.
--
-- ⚠ `…GcdStepExt` carries all of this at `PairT`/`⌜Nat⌝`/`msr`
--   (`gcdIH-w`, `gcdIH-w²`, `gcdIH-w³`, `appGcdIH`).  `gcdIH-w` is
--   LITERALLY `aIHTat-ren PairT ⌜Nat⌝ msr` — an instantiation of a library
--   lemma sitting in an example.  Carrier-generic, it serves every client.
------------------------------------------------------------------------

aIHTat-w : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μ : RTm Γ) →
           renTy vs (aIHTat A cM m μ)
         ≡ aIHTat (renTy vs A) (renTm (extR vs) cM) (renTm (extR vs) m) (w μ)
aIHTat-w A cM m μ = aIHTat-ren A cM m μ

aIHTat-w² : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μ : RTm Γ) →
            renTy vs (renTy vs (aIHTat A cM m μ))
          ≡ aIHTat (renTy vs (renTy vs A))
                   (renTm (extR vs) (renTm (extR vs) cM))
                   (renTm (extR vs) (renTm (extR vs) m)) (w (w μ))
aIHTat-w² A cM m μ =
  trans (cong (renTy vs) (aIHTat-w A cM m μ))
        (aIHTat-w (renTy vs A) (renTm (extR vs) cM) (renTm (extR vs) m) (w μ))

aIHTat-w³ : {Γ : Cx} (A : RTy Γ) (cM m : RTm (Γ ∙)) (μ : RTm Γ) →
            renTy vs (renTy vs (renTy vs (aIHTat A cM m μ)))
          ≡ aIHTat (renTy vs (renTy vs (renTy vs A)))
                   (renTm (extR vs) (renTm (extR vs) (renTm (extR vs) cM)))
                   (renTm (extR vs) (renTm (extR vs) (renTm (extR vs) m)))
                   (w (w (w μ)))
aIHTat-w³ A cM m μ =
  trans (cong (renTy vs) (aIHTat-w² A cM m μ))
        (aIHTat-w (renTy vs (renTy vs A))
                  (renTm (extR vs) (renTm (extR vs) cM))
                  (renTm (extR vs) (renTm (extR vs) m)) (w (w μ)))

-- ★★ APPLYING AN IH HANDLE, at an arbitrary carrier and motive.
--    ⚠ `…GcdStepExt`'s `appGcdIH` is this at `PairT`/`⌜Nat⌝`/`msr`, where
--      the conclusion collapses to `El ⌜Nat⌝` because the motive is closed.
appIHat : {Γ : Ctx} {A : RTy ⌊ Γ ⌋} {cM m : RTm (⌊ Γ ⌋ ∙)} {μ i y q : RTm ⌊ Γ ⌋} →
          Γ ⊢ i ∷ aIHTat A cM m μ → Γ ⊢ y ∷ A →
          Γ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) m)) μ →
          Γ ⊢ app (app i y) q ∷ El (subTm (single y) cM)
appIHat {cM = cM} {m = m} {μ = μ} {y = y} {q = q} di dy dq =
  ⊢-cast eq2 (⊢app (⊢-cast eq1 (⊢app di dy)) dq)
  where
    eq1 = cong₂ (λ u c → Π (Hom Nat (nsuc (subTm (single y) m)) u) (El c))
                (wk-single {v = y} μ)
                (sub-w {σ = single y} cM)

    eq2 = cong El (wk-single {v = q} (subTm (single y) cM))
