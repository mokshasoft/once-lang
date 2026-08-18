------------------------------------------------------------------------
-- OCP-0009 — DOES **ONE** FORCED APPLICATION OF `gcdStepExt` FIT?
--
-- ⚠ THE SUB-QUESTION THAT DECIDES THE NEXT REFACTOR.  The ladder showed the
--   cost is the `StepExt` PROOF, not the step term: `irr-ind` applies `ext`
--   and `idOfRed` forces the result, ONCE PER LEAF — four times.  The
--   obvious lever is to make that happen ONCE.  But that only helps if a
--   SINGLE application fits:
--
--     one application cheap, four OOM   ⇒ hoisting to one is the fix
--     one application OOMs              ⇒ hoisting is pointless; the cost
--                                         is gcd's `StepExt` reducing AT
--                                         ALL, and the interface has to
--                                         change so it is never forced
--
-- ★ Every premise is a PARAMETER, so nothing here builds a `StepPW` or a
--   renaming — the module measures exactly one thing: forcing the result of
--   `gcdStepExt` open, via `prvOk`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesOneApp where

open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; _∙; RTy; El; Id; RTm; app; ⌜Nat⌝
        ; Ren; renTm; renTy; subTm; subTy; extR; nrs )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; _▹_; ⌊_⌋; single; _⊢_∷_ )
open import poc.OCP0009.NbEPDirDBSubj using ( Ren⊢ )
open import poc.OCP0009.NbEPDirDBLibRec using ( aIHTat )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( prvTm; prvOk; StepPW )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( gcdStp; msr )
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtA using ( gcdStepExt )
open import poc.OCP0009.NbEPDirDBLibAmrec using ( module AmTΠ; Prv; wR )
open import poc.OCP0009.NbEPDirDBType using ( ◇; _⊢ty_; ⊢nzero; ⊢nsuc; ⊢var; here; there )
open import poc.OCP0009.NbEPDirDBPi using ( nzero; nsuc; var; vs; vz; Π; Nat )
open import poc.OCP0009.NbEPDirDBLibWk using ( w )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( ⊢PairT )
open import poc.OCP0009.NbEPDirDBType using ( ⊢⌜Nat⌝ )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep using ( ⊢msr; ⊢gcdStp )

-- the IH type at the carrier, spelled exactly as `StepExt` spells it
IHTy : {Δ Θ : Ctx} (ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋) (a : RTm ⌊ Θ ⌋) → RTy ⌊ Θ ⌋
IHTy ρ a = aIHTat (renTy ρ PairT) (renTm (extR ρ) ⌜Nat⌝) (renTm (extR ρ) msr)
                  (subTm (single a) (renTm (extR ρ) msr))

------------------------------------------------------------------------
-- ★★★ ONE APPLICATION, FORCED.
------------------------------------------------------------------------

oneApp : {Δ Θ : Ctx} {ρ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (hρ : Ren⊢ Δ Θ ρ)
         (a ih₁ ih₂ : RTm ⌊ Θ ⌋)
         (da : Θ ⊢ a ∷ renTy ρ PairT)
         (d₁ : Θ ⊢ ih₁ ∷ IHTy ρ a) (d₂ : Θ ⊢ ih₂ ∷ IHTy ρ a)
         (pw : StepPW Δ PairT ⌜Nat⌝ msr Θ ρ a ih₁ ih₂) →
         Θ ⊢ prvTm (gcdStepExt hρ a ih₁ ih₂ da d₁ d₂ pw)
           ∷ Id (El (subTm (single a) (renTm (extR ρ) ⌜Nat⌝)))
                (app (app (renTm ρ gcdStp) a) ih₁)
                (app (app (renTm ρ gcdStp) a) ih₂)
oneApp hρ a ih₁ ih₂ da d₁ d₂ pw = prvOk (gcdStepExt hρ a ih₁ ih₂ da d₁ d₂ pw)

------------------------------------------------------------------------
-- ★★★ WHICH LEAF?  Three of `irr-ind`'s four are EX FALSO (`pwZ`); only
--     `irr-ss` has content — it instantiates the pointwise hypothesis at
--     the recursive call.  Force each at gcd's `ext` and compare.
------------------------------------------------------------------------

module LeafAt (Δ : Ctx) where

  open AmTΠ Δ PairT ⌜Nat⌝ msr gcdStp ⊢PairT ⊢⌜Nat⌝ ⊢msr ⊢gcdStp public
    using ( irr-zz; irr-zs; irr-sz; irr-ss; irrT; vsθ; irrSplit
          ; irrT-sub; ⊢irrT )

  -- the cheapest leaf: both bounds zero, premise ex falso
  leafZZ : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ)
           {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT) →
           Prv Θ (irrT θ x y nzero nzero)
  leafZZ h dx dy = irr-zz gcdStepExt h dx dy

  -- ★ one bound zero, one a successor — still ex falso, but the successor
  --   side goes through `⊢ihS-atR` rather than `⊢ihZ-atR`
  leafZS : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ)
           {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
           {k : RTm ⌊ Θ ⌋} (dk : Θ ⊢ k ∷ Nat) →
           Prv Θ (irrT θ x y nzero (nsuc k))
  leafZS h dx dy dk = irr-zs gcdStepExt h dx dy dk

  -- ★★ THE ONLY LEAF WITH CONTENT: both bounds successors, so the pointwise
  --    hypothesis is instantiated at the recursive call rather than being
  --    ex falso.  This is where `descS-peel` and `⊢strong-step` live.
  leafSS : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ)
           {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
           {k₁ k₂ t : RTm ⌊ Θ ⌋} (dk₁ : Θ ⊢ k₁ ∷ Nat) (dk₂ : Θ ⊢ k₂ ∷ Nat)
           (dih : Θ ⊢ t ∷ Π Nat (irrT (vsθ θ) x y (w k₁) (var vz))) →
           Prv Θ (irrT θ x y (nsuc k₁) (nsuc k₂))
  leafSS h dx dy dk₁ dk₂ dih = irr-ss gcdStepExt h dx dy dk₁ dk₂ dih

  -- ★★★ THE INNER ASSEMBLY.  `irr-ind` builds `ZP` exactly like this: an
  --     `irrSplit` over the SECOND bound, combining the two ex-falso leaves.
  --     Every ingredient here is already measured cheap; this is the first
  --     COMBINATION.
  splitZP : {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT) →
            Prv (Δ ▹ Nat) (irrT vs x y nzero (var vz))
  splitZP dx dy =
    irrSplit there dx dy ⊢nzero
             (irr-zz gcdStepExt there dx dy)
             (irr-zs gcdStepExt (wR (wR there)) dx dy (⊢var (there here)))

  ------------------------------------------------------------------------
  -- ★★ SPLITTING `irrSplit` INTO ITS TWO HALVES.
  --
  --   (a) the THREE CASTS — pure type equalities, `irrT-sub` + `wk-single`
  --   (b) the MOTIVE — `⊢irrT`, a `⊢ty` derivation for `irrT` itself
  --
  --   `irrT` mentions `auxAt x n`, i.e. the AUXILIARY, which is built from
  --   the step — so (b) is the half that could carry gcd's step into the
  --   type.  (a) never looks at the step at all.
  ------------------------------------------------------------------------

  -- (a) the three casts, at the shape `irrSplit` uses them
  castAt : {Θ₀ : Ctx} {θ : Ren ⌊ Δ ⌋ (⌊ Θ₀ ⌋ ∙)} {x y : RTm ⌊ Δ ⌋}
           (n₁ : RTm (⌊ Θ₀ ⌋ ∙)) →
           subTy (single (var vz)) (irrT (vsθ θ) x y (w n₁) (var vz))
         ≡ irrT θ x y n₁ (var vz)
  castAt {θ = θ} {x = x} {y = y} n₁ =
    trans (irrT-sub (vsθ θ) θ (λ v → refl) x y (w n₁) (var vz))
          (cong (λ u → irrT θ x y u (var vz)) (wk-single {v = var vz} n₁))

  castZ : {Θ₀ : Ctx} {θ : Ren ⌊ Δ ⌋ (⌊ Θ₀ ⌋ ∙)} {x y : RTm ⌊ Δ ⌋}
          (n₁ : RTm (⌊ Θ₀ ⌋ ∙)) →
          subTy (single nzero) (irrT (vsθ θ) x y (w n₁) (var vz))
        ≡ irrT θ x y n₁ nzero
  castZ {θ = θ} {x = x} {y = y} n₁ =
    trans (irrT-sub (vsθ θ) θ (λ v → refl) x y (w n₁) (var vz))
          (cong (λ u → irrT θ x y u nzero) (wk-single {v = nzero} n₁))

  -- (b) the MOTIVE — the half that mentions the auxiliary
  motive : {Θ : Ctx} {θ : Ren ⌊ Δ ⌋ ⌊ Θ ⌋} (h : Ren⊢ Δ Θ θ)
           {x y : RTm ⌊ Δ ⌋} (dx : Δ ⊢ x ∷ PairT) (dy : Δ ⊢ y ∷ PairT)
           {n₁ n₂ : RTm ⌊ Θ ⌋} (dn₁ : Θ ⊢ n₁ ∷ Nat) (dn₂ : Θ ⊢ n₂ ∷ Nat) →
           Θ ⊢ty irrT θ x y n₁ n₂
  motive h dx dy dn₁ dn₂ = ⊢irrT h dx dy dn₁ dn₂
