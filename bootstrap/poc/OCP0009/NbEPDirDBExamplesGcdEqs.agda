------------------------------------------------------------------------
-- OCP-0009 — GAP A: gcd's DEFINING EQUATIONS AT VARIABLES.
--
-- ★ WHAT THIS CLOSES.  `…GcdStep` proves all four equations at CONCRETE
--   NUMERALS, by reduction.  At an open `a`/`b` the reductions get stuck:
--   `gcd (suc a , suc b)` cannot step to `gcd (suc a ∸ suc b , suc b)`
--   because the recursion is guarded by a measure that does not compute.
--   The two RECURSIVE equations therefore have to be INTERNAL — an `Id`,
--   not a `⟶*` — and that is what `amrec-unfold-Id` was built for.
--
-- ⚠ It was CONDITIONAL on `StepExt`, which nothing in the tree supplied
--   until `…GcdStepExt.gcdStepExt`.  Everything here is that hypothesis
--   being spent.
--
-- ★ THE TWO BASE EQUATIONS NEED NOTHING FROM HERE: `gcd (a , 0) = a` and
--   `gcd (0 , b) = b` already hold at variables BY REDUCTION
--   (`…GcdLib.gcd-suc-0At`, `…GcdStep.gcd-b0-var`/`gcd-a0-var`), because
--   neither branch inspects the measure.  Only the recursive ones are stuck.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdEqs where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π; Id
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝; ordtr
        ; Ren; renTm; renTy; Sub; subTm; subTy; extR; extS )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; _⟶_; _⟶*_; done; step
        ; ξ-natrecⁿ; ξ-natrecᶻ; βfst; βsnd; natrec-suc )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢wk; ⊢-cast; ⊢[] )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; StepExt; module AmTΠ; aStepT; renTm-idR
        ; idToRed )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm; ⊢monus )
open import poc.OCP0009.NbEPDirDBExamplesOrd using ( ⊢strong-step )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( ⊢le-refl; reflTm )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; ⊢gcdStp; msr; ⊢msr; descConv
        ; RecCall; recCall; recCert; recRed; gcd-gt-term; gcd-le-term )
open import poc.OCP0009.NbEPDirDBLibArith using ( plusMonoTm )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( plusMonoLTm )
open import poc.OCP0009.NbEPDirDBLibArithMonus
  using ( monusLtTm; ⊢desc-left; ⊢desc-right )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtA using ( gcdStepExt )
open import poc.OCP0009.NbEPDirDBType using ( ⊢nsuc; ⊢fst; ⊢snd; ⊢pair; ty-Nat; ⊢⌜Nat⌝ )

module GcdEqAt (Δ : Ctx) where

  open AmTΠ Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp public
    using ( amrecTm; auxIH; ihS-atP; descS-at; descS-atR; descS-peel
          ; ih-app; amrec-unfold-Id-red; idR; auxAt-id; descS )

  ------------------------------------------------------------------------
  -- ★ TYPING THE RECURSIVE CALL'S CERTIFICATE, un-renamed.
  --
  -- `descS-peel` says what the certificate IS, but only for the RENAMED
  -- form `descS-atR`.  At the identity renaming the two coincide — the
  -- extra `renTm (extR⁶ idR)` layer collapses and `auxAt idR` is `auxIH` —
  -- so one bridge gives the un-renamed twin, and `⊢strong-step` types it.
  --
  -- ⚠ Same shape as the library's `dD` in `irr-ss`: a certificate that
  --   exists only as a REDUCT can never be typed by subject reduction,
  --   because `subTm` does not invert.  Say what it is first.
  ------------------------------------------------------------------------

  extR-id : {Γ : Cx} {ρ : Ren Γ Γ} → (∀ v → ρ v ≡ v) → (∀ v → extR ρ v ≡ v)
  extR-id h vz     = refl
  extR-id h (vs v) = cong vs (h v)

  extR⁶-id : ∀ v → extR (extR (extR (extR (extR (extR idR))))) v ≡ v
  extR⁶-id = extR-id (extR-id (extR-id (extR-id (extR-id (extR-id (λ v → refl))))))

  descS-at-idR : (x a k p y q : RTm ⌊ Δ ⌋) →
                 descS-atR idR x a k p y q ≡ descS-at x a k p y q
  descS-at-idR x a k p y q =
    cong₂ (λ u t → subTm (single q)
                     (subTm (extS (single y))
                       (subTm (extS (extS (single p)))
                         (subTm (extS (extS (extS (single a))))
                           (subTm (extS (extS (extS (extS (single u)))))
                             (subTm (extS (extS (extS (extS (extS (single k))))))
                                    t))))))
          (auxAt-id x k)
          (renTm-idR extR⁶-id
                     (subTm (extS (extS (extS (extS (extS (extS (single x)))))))
                            descS))

  ⊢descS-at : {x a k p y q : RTm ⌊ Δ ⌋} →
              Δ ⊢ subTm (single y) msr ∷ Nat →
              Δ ⊢ subTm (single a) msr ∷ Nat → Δ ⊢ k ∷ Nat →
              Δ ⊢ q ∷ Hom Nat (nsuc (subTm (single y) msr)) (subTm (single a) msr) →
              Δ ⊢ p ∷ Hom Nat (subTm (single a) msr) (nsuc k) →
              Δ ⊢ descS-at x a k p y q ∷ Hom Nat (subTm (single y) msr) k
  ⊢descS-at {x = x} {a} {k} {p} {y} {q} dμy dμa dk dq dp =
    subst (λ u → Δ ⊢ u ∷ Hom Nat (subTm (single y) msr) k)
          (trans (sym (descS-peel idR x a k p y q)) (descS-at-idR x a k p y q))
          (⊢strong-step dμy dμa dk dq dp)

  ------------------------------------------------------------------------
  -- ★ THE MEASURE AT A CONSTRUCTOR-HEADED PAIR — the one thing that DOES
  --   still compute at variables, and the reason the recursive equations
  --   are reachable at all.
  ------------------------------------------------------------------------

  μ-pair : (u v : RTm ⌊ Δ ⌋) → subTm (single (pair u v)) msr ⟶* plusTm u v
  μ-pair u v = step (ξ-natrecⁿ (βfst u v)) (step (ξ-natrecᶻ (βsnd u v)) done)

  plus-suc : (u v : RTm ⌊ Δ ⌋) → plusTm (nsuc u) v ⟶* nsuc (plusTm u v)
  plus-suc u v = step (natrec-suc _ _ _) done

  μ-ss : (a' b' : RTm ⌊ Δ ⌋) →
         subTm (single (pair (nsuc a') (nsuc b'))) msr
       ⟶* nsuc (plusTm a' (nsuc b'))
  μ-ss a' b' = ⟶*-trans (μ-pair (nsuc a') (nsuc b')) (plus-suc a' (nsuc b'))


  ------------------------------------------------------------------------
  -- ★★★★★ GAP A — gcd UNFOLDS INTERNALLY, AT VARIABLES.
  --
  --     gcd (suc a , suc b)  ≡  gcdStp (suc a , suc b) ⟨ih⟩
  --
  -- ⚠ THIS IS THE FIRST STATEMENT OF ITS KIND IN THE TREE.  `amrec-unfold-Id`
  --   has existed since 2026-08-15 but was CONDITIONAL on `StepExt`, which
  --   nothing supplied; `LibAmrec`'s header called it "machinery with a real
  --   statement, not yet evidence that any particular function unfolds
  --   internally".  With `gcdStepExt` it is evidence.
  --
  -- ★ `a` and `b` are ARBITRARY TERMS — variables included.  Nothing here
  --   reduces the measure to a numeral: `μ (suc a , suc b)` computes to
  --   `suc (a + suc b)` for any `a`, `b`, and that is all the premise needs.
  ------------------------------------------------------------------------

  gX : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  gX a' b' = pair (nsuc a') (nsuc b')

  gK : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  gK a' b' = plusTm a' (nsuc b')

  gIH : RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋ → RTm ⌊ Δ ⌋
  gIH a' b' = ihS-atP (gX a' b') (gX a' b') (gK a' b')
                      (reflTm (subTm (single (gX a' b')) msr))

  ⊢gX : {a' b' : RTm ⌊ Δ ⌋} → Δ ⊢ a' ∷ Nat → Δ ⊢ b' ∷ Nat →
        Δ ⊢ gX a' b' ∷ PairT
  ⊢gX da db = ⊢pair ty-Nat (⊢nsuc da) (⊢nsuc db)

  gcd-unfold : {a' b' : RTm ⌊ Δ ⌋} → Δ ⊢ a' ∷ Nat → Δ ⊢ b' ∷ Nat →
               Prv Δ (Id (El ⌜Nat⌝)
                         (app amrecTm (gX a' b'))
                         (app (app gcdStp (gX a' b')) (gIH a' b')))
  gcd-unfold {a' = a'} {b' = b'} da db =
    amrec-unfold-Id-red gcdStepExt (⊢gX da db) (⊢plus da (⊢nsuc db)) (μ-ss a' b')

  ------------------------------------------------------------------------
  -- ★★★★★ …AND THEREFORE IT MAKES THE RECURSIVE CALL, INTERNALLY.
  --
  --     gcd (suc a , suc b)  ≡  ⟨ih⟩ (suc a ∸ suc b , suc b) ⟨cert⟩     (a > b)
  --
  -- Compose the unfolding with the step's own reduction to its recursive
  -- call.  ⚠ `⟨ih⟩` here is gcd's INTERNAL induction hypothesis, not
  -- `gcd` itself; turning it into `app amrecTm Y` is the remaining step and
  -- needs the recursive call's certificate TYPED — see the header note.
  ------------------------------------------------------------------------

  gcd-gt-call : {a' b' d : RTm ⌊ Δ ⌋} → Δ ⊢ a' ∷ Nat → Δ ⊢ b' ∷ Nat →
                (mh : monusTm (nsuc a') (nsuc b') ⟶* nsuc d) →
                Prv Δ (Id (El ⌜Nat⌝)
                          (app amrecTm (gX a' b'))
                          (app (app (gIH a' b')
                                    (pair (monusTm (nsuc a') (nsuc b')) (nsuc b')))
                               (recCert (gcd-gt-term a' b' d (gIH a' b') mh))))
  gcd-gt-call {a' = a'} {b' = b'} {d = d} da db mh =
    idToRed done (recRed (gcd-gt-term a' b' d (gIH a' b') mh)) (gcd-unfold da db)
