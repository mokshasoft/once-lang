------------------------------------------------------------------------
-- OCP-0009 — GAP A, EQUATION 3: gcd's RECURSIVE STEP, INTERNALLY.
--
-- ⚠ SPLIT OUT OF `…GcdEqs` FOR COST, 2026-08-17.  `irr-ind` instantiated at
--   gcd's step is a big term — a `natrec` over four leaves carrying the
--   whole `irrT` motive — and adding it to `…GcdEqs` OOM-killed a module
--   that is otherwise 5s.  Alone it has room.  ⭐ Same isolation that took
--   `leaf₃s` from an OOM to 10s and `split2` from an OOM to 4.8s: one big
--   term per module when the term is big enough.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdRec where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Id
        ; RTm; var; nzero; nsuc; app; pair; fst; snd; ⌜Nat⌝
        ; subTm )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; _⊢_∷_; ⊢app; ⊢nsuc; ⊢conv; csymᵀ
        ; _⟶*_; done )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢-cast; ⊢[] )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; idToRed; idOfRed )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; asN )
open import poc.OCP0009.NbEPDirDBLibArithComm using ( transN; ⊢transN )
open import poc.OCP0009.NbEPDirDBInj using ( red→≅ᵀ; ⟶ᵀ*-Homʳ )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( ⊢plus )
open import poc.OCP0009.NbEPDirDBExamplesDiv using ( monusTm )
open import poc.OCP0009.NbEPDirDBExamplesStrong using ( reflTm; ⊢le-refl )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( msr; ⊢msr; recCert; gcd-gt-term; descConv )
open import poc.OCP0009.NbEPDirDBLibArithMonus using ( ⊢desc-left )
open import poc.OCP0009.NbEPDirDBExamplesNat using ( plusTm )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtA using ( gcdStepExt )
open import poc.OCP0009.NbEPDirDBExamplesGcdEqs using ( module GcdEqAt )

module GcdRecAt (Δ : Ctx) where

  open GcdEqAt Δ public

  ------------------------------------------------------------------------
  -- ★★ THE IRRELEVANCE WITNESS, AT THE TWO BOUNDS.
  --
  -- `irr-ind` proves it as a `Π Nat` — quantified over the SECOND bound —
  -- and one application lands it where the recursive step needs it: the
  -- auxiliary seeded at `x` and run to bound `k` agrees with the auxiliary
  -- seeded at `y` and run to bound `n₂`, at every carrier and both
  -- certificates.  ⭐ THIS is what nothing weaker gives, and what
  -- `StepExt` was ultimately for.
  --
  -- ⚠⚠ COMMENTED OUT — IT OOM-KILLS (three attempts 2026-08-17, every one
  --   with a concurrent build running, so none is a clean measurement).
  --   Kept verbatim so the discharge is not lost; the theorem below takes
  --   the witness as a HYPOTHESIS instead, which verifies that every
  --   interface in the recursive step lines up and isolates the remaining
  --   problem to producing this ONE term.
  --   ⚠ `Green ≠ meaningful`: nothing below proves anything about gcd until
  --   this is discharged.
  ------------------------------------------------------------------------

--   irrAt : {x y k n₂ : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
--           (dk : Δ ⊢ k ∷ Nat) (dn₂ : Δ ⊢ n₂ ∷ Nat) →
--           Δ ⊢ app (prvTm (irr-ind gcdStepExt dx dy dk)) n₂ ∷ irrT idR x y k n₂
--   irrAt {x = x} {y = y} {k = k} {n₂ = n₂} dx dy dk dn₂ =
--     ⊢-cast (trans (irrT-sub vs idR (λ v → refl) x y (w k) (var vz))
--                   (cong (λ u → irrT idR x y u n₂) (wk-single {v = n₂} k)))
--            (⊢app (prvOk (irr-ind gcdStepExt dx dy dk)) dn₂)

  ------------------------------------------------------------------------
  -- ★★★★★ GAP A, EQUATION 3 — CONDITIONAL on the witness above.
  --
  -- ⚠ EVERY PIECE IS ITS OWN Def inside a parameterised sub-module, not a
  --   `where` block.  As one term this ran 75 MINUTES without finishing;
  --   the rule that has held all session is one big term per Def.
  ------------------------------------------------------------------------

  module GtEq {a' b' d : RTm ⌊ Δ ⌋}
              (da : Δ ⊢ a' ∷ Nat) (db : Δ ⊢ b' ∷ Nat) (dd : Δ ⊢ d ∷ Nat)
              (mh : monusTm (nsuc a') (nsuc b') ⟶* nsuc d) where

    X = gX a' b'
    Y = PAIRᵍ a' b'
    K = gK a' b'
    IHt = gIH a' b'
    CRT = recCert (gcd-gt-term a' b' d IHt mh)

    ⊢X = ⊢gX da db
    ⊢Y = ⊢PAIRᵍ da db
    ⊢K = ⊢plus da (⊢nsuc db)

    dμX = ⊢[] ⊢msr ⊢X
    dμY = ⊢[] ⊢msr ⊢Y

    -- μ X ≤ suc K, from the measure's own reduction
    dP : Δ ⊢ reflTm (subTm (single X) msr)
           ∷ Hom Nat (subTm (single X) msr) (nsuc K)
    dP = ⊢conv (⊢le-refl dμX) (red→≅ᵀ (⟶ᵀ*-Homʳ (μ-ss a' b')))

    -- ⭐⭐ THE RECURSIVE CALL'S CERTIFICATE, TYPED — AND IT IS ONE
    --    `⊢desc-left`.  This is the whole payoff of making `gcd-gt-term`
    --    produce the certificate CLEAN at construction: `recCert` IS
    --    `gtCert a' b'`, which is exactly what `⊢desc-left` derives, so
    --    there is nothing to peel and nothing to compare.  Two `⊢conv`s
    --    remain and both are measure bookkeeping: `descConv` moves the
    --    measure across the pair's projections, and `μ-pair` computes the
    --    carrier's own measure.
    dQ : Δ ⊢ CRT ∷ Hom Nat (nsuc (subTm (single Y) msr)) (subTm (single X) msr)
    dQ = ⊢conv (⊢conv (⊢desc-left da db)
                      (csymᵀ (descConv (monusTm (nsuc a') (nsuc b')) (nsuc b')
                                       (plusTm (nsuc a') (nsuc b')))))
               (csymᵀ (red→≅ᵀ (⟶ᵀ*-Homʳ (μ-pair (nsuc a') (nsuc b')))))

    -- ⚠ SIGNED.  `⊢descS-at`'s `x` occurs ONLY in the subject, so nothing
    --   determines it from the arguments — the standing rule again.
    dC₁ : Δ ⊢ descS-at X X K (reflTm (subTm (single X) msr)) Y CRT
            ∷ Hom Nat (subTm (single Y) msr) K
    dC₁ = ⊢descS-at {x = X} {a = X} {k = K}
                    {p = reflTm (subTm (single X) msr)} {y = Y} {q = CRT}
                    dμY dμX ⊢K dQ dP
    dC₂ = ⊢le-refl dμY

    MID = app (app (auxIH X K) Y)
              (descS-at X X K (reflTm (subTm (single X) msr)) Y CRT)

    -- 1+2: unfold gcd, then reduce the IH application to the auxiliary
    s1 : Prv Δ (Id (El ⌜Nat⌝) (app amrecTm X) MID)
    s1 = idToRed done
           (ih-app X X K (reflTm (subTm (single X) msr)) Y CRT)
           (gcd-gt-call da db mh)

    -- 3: irrelevance, then read the right-hand side back as `gcd Y`
    s2 : {t : RTm ⌊ Δ ⌋} →
         Δ ⊢ t ∷ irrT idR X Y K (subTm (single Y) msr) →
         Prv Δ (Id (El ⌜Nat⌝) MID (app amrecTm Y))
    -- ⚠ `c₁`/`c₂` EXPLICIT: they occur only under `subTm` in `irrElim`'s
    --   conclusion, so leaving them `_` blocks (the standing rule).
    s2 dirr = idOfRed done (amrec-β Y)
                (irrElim {θ = idR} {x = X} {y = Y} dirr Y
                         (descS-at X X K (reflTm (subTm (single X) msr)) Y CRT)
                         (reflTm (subTm (single Y) msr))
                         ⊢Y dC₁ dC₂)

    dA = asN (⊢amrecPt ⊢X)
    dB = asN (appAux ⊢X ⊢K ⊢Y dC₁)
    dC = asN (⊢amrecPt ⊢Y)

    gcd-gt-eq : {t : RTm ⌊ Δ ⌋} →
                Δ ⊢ t ∷ irrT idR X Y K (subTm (single Y) msr) →
                Prv Δ (Id (El ⌜Nat⌝) (app amrecTm X) (app amrecTm Y))
    gcd-gt-eq dirr =
      prv (transN (app amrecTm X) (prvTm s1) (prvTm (s2 dirr)))
          (⊢transN dA dB dC (prvOk s1) (prvOk (s2 dirr)))
