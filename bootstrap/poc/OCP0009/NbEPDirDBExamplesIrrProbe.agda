------------------------------------------------------------------------
-- OCP-0009 — SHRINKING `irr-ind` UNTIL IT COMPLETES.
--
-- ⚠ THE QUESTION SIX EXPERIMENTS DID NOT ANSWER.  `⊢app` on
--   `irr-ind gcdStepExt …` OOMs, and profiling cannot say why because
--   `--profile=all` prints only on COMPLETION.  So shrink the instance
--   until it DOES complete, and see which parameter carries the cost:
--
--     is `irr-ind` inherently large,  or does gcd's `stp` make it large?
--
-- ★ THE SHRUNK INSTANCE.  Same carrier, code and measure as gcd —
--   `PairT`/`⌜Nat⌝`/`msr` — so the only thing that changes is the STEP.
--   `stpT` ignores its IH entirely and returns `fst x`, which is gcd's own
--   leaf 1 with the recursion removed.  Its `StepExt` is then trivial: both
--   sides reduce to the SAME term, so `⊢idrefl` closes it, where gcd's
--   needed three nested splits and four leaves.
--
--   ⇒ if `⊢app` is CHEAP here, the cost is gcd's `stp` and the fix is in
--     `…GcdStepExt`;  if it is EXPENSIVE here too, `irr-ind` itself is the
--     problem and the fix belongs in `LibAmrec`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesIrrProbe where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; sym; subst )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π
        ; RTm; var; nsuc; lam; app; fst; snd; ⌜Nat⌝
        ; subTm; subTy; renTm; extR )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single
        ; _⊢_∷_; ⊢var; here; there; ⊢lam; ⊢app; ⊢fst
        ; _⟶*_; done; step; β; ξ-appˡ; ⊢idrefl; ⊢⌜Nat⌝ )
open import poc.OCP0009.NbEPDirDBSubj using ( ⊢-cast; ren-lemma; Ren⊢ )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; StepExt; aStepT; idOfRed; module AmTΠ )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asP )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( msr; ⊢msr; ⊢gcdIH )

------------------------------------------------------------------------
-- ★ THE TRIVIAL STEP — `λ x. λ ih. fst x`.  The IH is bound and ignored.
------------------------------------------------------------------------

stpT : {Γ : Cx} → RTm Γ
stpT = lam (lam (fst (var (vs vz))))

⊢stpT : {Γ : Ctx} → Γ ⊢ stpT ∷ aStepT PairT ⌜Nat⌝ msr
⊢stpT = ⊢lam ⊢PairT (⊢lam (⊢gcdIH ⊢msr) (asP (⊢fst (⊢var (there here)))))

------------------------------------------------------------------------
-- ★ …and its `StepExt`, which is trivial: BOTH SIDES REDUCE TO `fst a`,
--   because the step never touches the `ih` it was given.
------------------------------------------------------------------------

redT : {Γ : Cx} (a ih : RTm Γ) → app (app stpT a) ih ⟶* fst a
redT a ih =
  subst (λ t → app (app stpT a) ih ⟶* fst t) (wk-single {v = ih} a)
        (step (ξ-appˡ (β _ a)) (step (β _ ih) done))

------------------------------------------------------------------------
-- ★★ THE TRIVIAL `StepExt` — one `⊢idrefl`.
--
-- ⭐ COMPARE WITH gcd's: three nested `natrec` splits, four leaves, an
--   internalised pointwise hypothesis, and ~600 lines across ten modules.
--   Here both sides reduce to the SAME term because the step never looks at
--   its `ih`, so `idOfRed` plus reflexivity is the whole proof.
------------------------------------------------------------------------

stpTExt : {Δ : Ctx} → StepExt Δ PairT ⌜Nat⌝ msr stpT
stpTExt hρ a ih₁ ih₂ da d₁ d₂ pw =
  idOfRed (redT a ih₁) (redT a ih₂)
          (prv _ (⊢idrefl ⊢⌜Nat⌝ (asP (⊢fst da))))

------------------------------------------------------------------------
-- ★★★ AND THE MEASUREMENT: `⊢app` on `irr-ind` AT THIS STEP.
--
-- Identical in shape to gcd's `irrAt`, differing ONLY in which `StepExt`
-- is supplied.  If this is cheap, gcd's `stp` carries the cost; if it OOMs
-- too, `irr-ind` itself does.
------------------------------------------------------------------------

module ProbeAt (Δ : Ctx) where

  open AmTΠ Δ PairT ⌜Nat⌝ msr stpT ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢stpT public
    using ( irrT; irrT-sub; irr-ind; idR )

  probeApp : {x y k n₂ : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
             (dk : Δ ⊢ k ∷ Nat) (dn₂ : Δ ⊢ n₂ ∷ Nat) →
             Δ ⊢ app (prvTm (irr-ind stpTExt dx dy dk)) n₂
               ∷ subTy (single n₂) (irrT vs x y (w k) (var vz))
  probeApp dx dy dk dn₂ = ⊢app (prvOk (irr-ind stpTExt dx dy dk)) dn₂
