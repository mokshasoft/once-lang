------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — gcd's `StepExt`, parts 3b…3g, ONE MODULE.
--
-- ⚠⚠ THIS MODULE NEEDS THE COMPACTING COLLECTOR.  Check it with
--
--       ./check.sh poc/OCP0009/NbEPDirDBExamplesGcdStepExtA.agda +RTS -c -RTS
--
--   (`sweep.sh` greps that phrase from these first 40 lines and uses
--    `-A64m -c` on the FIRST attempt; its exit-143 retry is the safety
--    net for machine variation, not the mechanism.)
--
-- ★ WAS SEVEN MODULES, MERGED 2026-08-21 — and they were ONE CHAIN, not
--   a fan: A1 → A2 → A3 → C → A4 → A5 → A.  `…GcdStepExtC` sat in the
--   MIDDLE of it (A4 imported C, C imported A3), so the numbering was
--   never the dependency order and `C` was internal to the chain all
--   along — its only importer was A4.  Merging therefore needed no
--   external repointing at all.
--
--   The order below IS the derivation's order:
--     3b  split-1 and split-2 MOTIVES
--     3c  the split-3 MOTIVE (the heavy one)
--     3d  SPLIT 3
--     3d2 the two SPLIT-BOUNDARY CONVERSIONS
--     3e  SPLIT 2
--     3f  SPLIT 1
--     3g  StepExt, DISCHARGED
--
-- ⚠ MEASURED (`PERF-2026-08-21.md` §3): splitting is COST-NEUTRAL in wall
--   time — the sibling `…GcdDvdA*` family cost 147s as six modules and
--   147s merged.  The 2026-08-17 split was forced by the default COPYING
--   collector wanting ~2x the live heap, not by the derivation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBExamplesGcdStepExtA where

open import poc.OCP0009.NbEPDirDBExamplesGcdStepExt public
open import poc.OCP0009.NbEPDirDBExamplesGcdStepExtE public
open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂; sym )
open import poc.OCP0009.NbEPDirDBPi
  using ( Cx; ε; _∙; vz; vs
        ; RTy; El; Hom; Nat; Π; Id
        ; RTm; var; nzero; nsuc; natrec; lam; app; pair; fst; snd; ⌜Nat⌝
        ; Ren; renTm; renTy; Sub; subTm; subTy; extR; extS; Id-cong₃
        ; subTy-renTy; renTy-subTy; subTy-cong )
open import poc.OCP0009.NbEPDirDBType
  using ( Ctx; ◇; _▹_; ⌊_⌋; single; nrs
        ; _⊢_∷_; _∋_∷_; _⊢ty_; ⊢var; here; there; ⊢lam; ⊢app; ⊢nsuc; ⊢natrec
        ; ⊢fst; ⊢snd; ⊢nzero; ⊢idrefl; natrec-zero; natrec-suc
        ; ⊢conv; _≅ᵀ_; csymᵀ
        ; ty-Nat; ty-Hom; ty-El; ty-Π; ty-Id; ⊢⌜Nat⌝
        ; _⟶_; _⟶*_; done; step; β; ξ-appˡ )
open import poc.OCP0009.NbEPDirDBSubj
  using ( ⊢wk; ⊢-cast; ∋-cast; Ren⊢; Ren⊢-ext; ren-ty; ren-lemma; ⊢[] )
open import poc.OCP0009.NbEPDirDBLibAmrec
  using ( Prv; prv; prvTm; prvOk; StepExt; StepPW; wR; renren; renTy-idR
        ; subrenTy; aIHTat-ren; aIHTat-sub; idOfRed )
open import poc.OCP0009.NbEPDirDBLibWk using ( w; sub-w; sub-w²; sub-w³; ren-w )
open import poc.OCP0009.NbEPDirDBLR using ( wk-single )
open import poc.OCP0009.NbEPDirDBLibPair using ( PairT; ⊢PairT; asP )
open import poc.OCP0009.NbEPDirDBConf using ( ⟶*-trans; ⟶*-appˡ; ⟶*-ren )
open import poc.OCP0009.NbEPDirDBInj
  using ( _⟶ᵀ*_; stepᵀ; doneᵀ; red→≅ᵀ; ⟶ᵀ*-trans; ⟶ᵀ*-Πʳ; ⟶ᵀ*-Idˡ; ⟶ᵀ*-Idʳ )
open import poc.OCP0009.NbEPDirDBExamplesGcdStep
  using ( gcdStp; gcdBody; msr; ⊢msr; gcdIH; ⊢gcdIH; gcdG; ⊢gcdG
        ; G1; ⊢G1; G1z; ⊢G1z; gcdInn1; ⊢gcdInn1; ⊢gcdBody
        ; G2; ⊢G2; G2z; ⊢G2z; gcdInn2; ⊢gcdInn2
        ; G3; ⊢G3; G3z; ⊢G3z; G3s; ⊢G3s; PAIRᶻ; ⊢PAIRᶻ; CERTᶻ; ⊢CERTᶻ
        ; PAIRˢ; ⊢PAIRˢ; CERTˢ; ⊢CERTˢ )
open import poc.OCP0009.NbEPDirDBLibNat using ( plusTm; ⊢plus )
open import poc.OCP0009.NbEPDirDBLibMonus using ( monusTm; ⊢monus )


-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtA1
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3b: the split-1 and split-2 MOTIVES.
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

⊢M₁ : {Γ : Ctx} → ((Γ ▹ PairT) ▹ Nat) ⊢ty M₁
⊢M₁ = ⊢eqG (⊢plus (⊢fst (⊢var (there here))) (⊢var here))
           (⊢natrec-var ⊢G1 ⊢G1z ⊢gcdInn1)

⊢M₂ : {Γ : Ctx} → (Θ₂ Γ ▹ Nat) ⊢ty M₂
⊢M₂ = ⊢eqG (⊢plus (⊢var here) (⊢nsuc (⊢var (there (there here)))))
           (⊢natrec-var ⊢G2 ⊢G2z ⊢gcdInn2)

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtA2
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3c: the split-3 MOTIVE (the heavy one).
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

⊢M₃ : {Γ : Ctx} → (Θ₃ Γ ▹ Nat) ⊢ty M₃
⊢M₃ = ⊢eqG (⊢plus (⊢nsuc (⊢var (there (there here))))
                  (⊢nsuc (⊢var (there (there (there (there here)))))))
           (⊢natrec-var ⊢G3 ⊢G3z ⊢G3s)

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtA3
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3d: SPLIT 3.
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

split3 : {Γ : Ctx} →
         Prv (Θ₃ Γ)
             (subTy (single (monusTm (nsuc (var (vs vz)))
                                     (nsuc (var (vs (vs (vs vz))))))) M₃)
split3 = prv _ (⊢natrec ⊢M₃ (prvOk leaf₃z) (prvOk leaf₃s)
                        (⊢monus (⊢nsuc (⊢var (there here)))
                                (⊢nsuc (⊢var (there (there (there here)))))))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtC
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3d2: the two SPLIT-BOUNDARY CONVERSIONS.
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

-- ⚠ EACH CONVERSION IS ITS OWN Def, in its own module.  `eqG-red` pushes a
--   reduction of `f` through three `Π`s and BOTH `Id` sides, and `f` here is
--   the gcd `natrec` carrying `G3z`/`G3s` — inline inside the `⊢natrec` that
--   uses it, `split2` OOM-killed even alone in a module.

conv₂ : {Γ : Cx} →
        subTy nrs (M₂ {Γ})
      ≅ᵀ subTy (single (monusTm (nsuc (var (vs vz)))
                                (nsuc (var (vs (vs (vs vz))))))) (M₃ {Γ})
conv₂ = eqG-red probe₂-s

conv₁ : {Γ : Cx} →
        subTy nrs (M₁ {Γ})
      ≅ᵀ subTy (single (fst (var (vs (vs vz))))) (M₂ {Γ})
conv₁ = eqG-red probe₁-s

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtA4
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3e: SPLIT 2.
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

split2 : {Γ : Ctx} →
         Prv (Θ₂ Γ) (subTy (single (fst (var (vs (vs vz))))) M₂)
split2 = prv _ (⊢natrec ⊢M₂ (prvOk leaf₂z)
                        (⊢conv (prvOk split3) (csymᵀ conv₂))
                        (⊢fst (⊢var (there (there here)))))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtA5
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3f: SPLIT 1.
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

gcdExt : {Γ : Ctx} → Prv (Γ ▹ PairT) (eqG msr gcdBody)
gcdExt = prv _ (⊢natrec ⊢M₁ (prvOk leaf₁z)
                        (⊢conv (prvOk split2) (csymᵀ conv₁))
                        (⊢snd (⊢var here)))

-- ══════════════════════════════════════════════════════════════════
-- PART: …ExamplesGcdStepExtA
-- ══════════════════════════════════════════════════════════════════
-- OCP-0009 — gcd's `StepExt`, part 3g: StepExt, DISCHARGED.
-- ⚠ SPLIT OUT OF `NbEPDirDBExamplesGcdStepExt` FOR COST, 2026-08-17.
--   Measured on a 7 GB box: the infrastructure alone checks in 4.3s, and
--   `leaf₃z` ALONE takes it to 43s — a 10x jump for ONE leaf, because the
--   two recursive leaves sit at context depth 10 and cost is ~1.7x per
--   slot.  All of it in one module OOM-killed at the cgroup cap.
--   ⭐ Splitting into Defs was NOT enough; the file had to split.

-- ⚠⚠ EVERY PIECE BELOW IS ITS OWN TOP-LEVEL Def, and that is a MEMORY
--   decision, not style.  Assembled as one term with the motives and the
--   two inner splits in a `where` block, this module OOM-KILLED at the
--   cgroup cap after 2m18s (measured 2026-08-17).  Split 3's leaves sit at
--   context depth 10 and cost is ~1.7x per slot, so the whole assembly
--   elaborated at once does not fit.  Behind names, each `natrec` is
--   elaborated and discarded separately.
--   ⭐ Read `agda-cost-is-elaborated-term-size` before re-inlining any of it.

gcdStepExt : {Δ : Ctx} → StepExt Δ PairT ⌜Nat⌝ msr gcdStp
gcdStepExt hρ a ih₁ ih₂ da d₁ d₂ pw =
  idOfRed (red-β a ih₁) (red-β a ih₂)
          (prv _ (eqGElim (⊢-cast (eqG-sub {σ = single a} msr gcdBody)
                                  (⊢[] (prvOk gcdExt) da)) d₁ d₂
                          (prvOk (pwIntro (⊢plus (⊢fst da) (⊢snd da)) pw))))
