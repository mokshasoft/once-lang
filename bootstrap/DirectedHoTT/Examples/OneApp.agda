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
module DirectedHoTT.Examples.OneApp where
open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTy; El; Id; RTm; app; ⌜Nat⌝
        ; Ren; renTm; renTy; subTm; subTy; extR; nrs )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; _▹_; ⌊_⌋; single; _⊢_∷_; wk-single )
open import DirectedHoTT.Metatheory.SubjectReduction using ( Ren⊢ )
open import DirectedHoTT.Lib.Rec using ( aIHTat )
open import DirectedHoTT.Lib.Amrec using ( prvTm; prvOk; StepPW )
open import DirectedHoTT.Lib.Pair using ( PairT )
open import DirectedHoTT.Examples.Gcd.Step using ( gcdStp; msr )
open import DirectedHoTT.Examples.Gcd.StepExtA using ( gcdStepExt )
open import DirectedHoTT.Lib.Amrec using ( module AmTΠ; Prv; wR )
open import DirectedHoTT.Spec.Typing using ( ◇; _⊢ty_; ⊢nzero; ⊢nsuc; ⊢var; here; there )
open import DirectedHoTT.Spec.Syntax using ( nzero; nsuc; var; vs; vz; Π; Nat )
open import DirectedHoTT.Lib.Wk using ( w )
open import DirectedHoTT.Lib.Pair using ( ⊢PairT )
open import DirectedHoTT.Spec.Typing using ( ⊢⌜Nat⌝ )
open import DirectedHoTT.Examples.Gcd.Step using ( ⊢msr; ⊢gcdStp )

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

------------------------------------------------------------------------
-- ⚠⚠ AND THE TENSION IS NOT CLEAN — TESTED 2026-08-18, FALSIFIED.
--
-- The measurement said `irrSplit`'s 17.5s is the `⊢natrec` CONVERSION-
-- CHECKING its branches against `irrT` types, and `irrT` mentions `auxAt`,
-- so the remedy was to make `auxAt` OPAQUE and let those comparisons stay
-- syntactic.  The question was whether the `aux-*` reduction lemmas could
-- keep it transparent while the `irr-*` block did not.
--
-- THE SPLIT IS MECHANICALLY CLEAN: only TWO sites need `auxAt` to compute —
-- `⊢auxAt` (its definitional typing) and the `aux-*` reduction block, which
-- took one `opaque unfolding auxAt` covering 1,172 lines.  `irr-*` needed no
-- unfolding at all, exactly as predicted.
--
-- ⚠ BUT IT MADE THINGS WORSE.  With that split in place `…LibAmrec` ITSELF
--   OOMs — it is ~57s green without it.  So opacity on `auxAt` costs more
--   than the conversion checking it was meant to avoid.
--
-- ⇒ SEVEN fixes now proposed and falsified for this obligation.  The
--   LOCALISATION stands (the cost is `irrSplit`'s `⊢natrec`), but every
--   remedy that blocks unfolding has failed, and this one made the library
--   unbuildable.  Do not retry `auxAt` opacity.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ⚠⚠ DEF-HOISTING BUYS NOTHING — TESTED 2026-08-18, FALSIFIED (fix #8).
--
-- Controlled A/B, two modules identical but for a TWO-LINE diff in
-- `splitZP`'s two leaf arguments:
--
--   A  irrSplit … (irr-zz gcdStepExt there dx dy) (irr-zs gcdStepExt …)
--   B  irrSplit … (leafZZ there dx dy)            (leafZS …)
--
-- where `leafZZ`/`leafZS` are named Defs with explicit `Prv Θ (irrT …)`
-- ascriptions, i.e. the "split into Def-backed lemmas" lever that has
-- worked elsewhere in this project.
--
--   A = 15.3s   B = 16.5s   ⇒ no effect (B slower, inside the ±12% floor).
--
-- ★ WHY, and it is worth keeping: `irr-zz gcdStepExt there dx dy` was
--   ALREADY small syntactically — `gcdStepExt` is a Def REFERENCE, not an
--   inlined body — so there was no duplication for hoisting to remove.  A
--   further Def layer is unfolded during conversion just the same.
--
-- ⇒ THE MECHANISM IS NOW PINNED FROM BOTH SIDES.  The cost is the
--   conversion check FORCING `gcdStepExt`'s body.  It does not scale with
--   the number of syntactic references (hoisting: nil) and it does not
--   scale with STEP-TERM size (`IrrProbe` rung 2, a bigger step under a
--   3-line ext: nil, 4.4s for both rungs).  It scales with the EXT PROOF.
--
-- ⇒ ONE LEVER REMAINS UNTRIED: make `gcdStepExt`'s proof term SMALLER.
--   All eight attempts so far changed how Agda HANDLES a fixed ~600-line
--   proof across ten modules; none shrank the proof.  The trivial-ext
--   probes are free and gcd's OOMs, so the term is the whole variable.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- ★★★★ THE COST IS THE CONCRETE STEP TERM, IN THE TYPE — 2026-08-18.
--
-- Three modules, identical but for what is held ABSTRACT as a module
-- PARAMETER (a variable Agda cannot unfold), measured cold:
--
--     stp        ext             time
--     gcdStp     gcdStepExt      15.3s
--     gcdStp     ABSTRACT        17.5s
--     ABSTRACT   ABSTRACT         5.4s   ← bare module overhead
--
-- ⇒ THE EXT PROOF IS NOT THE DRIVER.  Removing it entirely (HoistP) does
--   not move the number.  Shrinking `gcdStepExt` would buy NOTHING; do not
--   spend effort there.
--
-- ⇒ THE COST IS IN THE TYPE, NOT THE PROOF.  With `ext` abstract there are
--   no expensive proof values left, yet merely STATING and converting
--   `irrT θ x y n₁ n₂` at a concrete `gcdStp` still costs 17.5s.  Any
--   client that writes that type pays.  `irrT` mentions `auxAt`, `auxAt`
--   mentions `auxS x`, and `auxS` carries the step.
--
-- ⚠ AND `IrrProbe` RUNG 2 WAS UNDERPOWERED, not decisive.  `stpB` is far
--   smaller than `gcdStp`, so "bigger step term costs nothing" was a null
--   result from a weak test, and it wrongly retired this mechanism once.
--   Vary the step by a parameter, not by a slightly larger term.
--
-- ⇒ TARGET: `irrT'` ALREADY takes the two auxiliary occurrences as abstract
--   slots `zx`/`zy`; `irrT` fills them with `auxAt …`, which is where the
--   step enters.  Keeping them abstract through the assembly is exactly the
--   configuration HoistQ measures FREE.
------------------------------------------------------------------------
