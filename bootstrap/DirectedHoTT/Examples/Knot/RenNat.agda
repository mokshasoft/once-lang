------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ NATURALITY OF THE RENAMING ELIMINATOR.  This is
-- `ExtNSub`, the hypothesis `Lib/ISub.isubMethod-red` leaves to its
-- caller, discharged for the knot.
--
-- ★ WHY ITS OWN MODULE: split by consumption.  `Knot/RenTm` is the only
--   consumer, `Knot/RenMot` is already large, and these lemmas need
--   nothing from `RenMot` but its definitions.
--
-- ⚠⚠ AN EARLIER VERSION OF THIS HEADER CLAIMED A MEASURED REASON — that
--   putting these lemmas inside `RenMot` took it "1s → 155s" — AND THAT
--   WAS WRONG.  The 1s came from a sweep line, and in that sweep
--   `Knot/JudgeWfAA` had ALREADY BUILT `RenMot` inside its own 2295s, so
--   the 1s was DESERIALIZATION, not a build.  `RenMot`'s real cold cost
--   with these lemmas removed and every library reverted is **264s**.
--   ⇒ there was never a regression, and this split is structural, not a
--     performance fix.  See `PERF.md` §6.8 — which is the very lesson
--     that was misread, in the same session that wrote it.
--
-- ★★★ WHAT **IS** MEASURED, and it is the reason the proof looks like
--   this: `refl` ALONE proves `subTm σ extRMethsK ≡ extRMethsK`, because
--   Agda normalises all 53 methods and the sides coincide — and it costs
--   **3m41s**.  Routed through `Lib/IMeths.methsFrom-sub` — one induction
--   over the walk — the same fact is **1.38s**.  ~160×.  Both figures are
--   from the same temp module, minutes apart, so the comparison is sound
--   even though the box was busy.
--
-- ★ THE LEAVES REALLY ARE `refl`.  `constMethR` and `extRTail` are small
--   concrete terms containing no `var`, so `subTm` computes to the same
--   term cheaply.  It is the 52-fold WALK that must not be unfolded.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenNat where
open import normalizer.Syntax.Types using ( _≡_; refl; trans; cong; cong₂ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; Sub; subTm; extS; pair; lam; app; var; vz; nsuc; ielim )
open import DirectedHoTT.Lib.Wk using ( w; sub-w )
open import DirectedHoTT.Lib.IMeths using ( cdTake; methsFrom; methsFrom-sub )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar )
open import DirectedHoTT.Examples.Knot.RenMot
  using ( extRMethsK; constMethR; extRTail; extRK; extRNK )

constMethR-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (constMethR {Γ}) ≡ constMethR {Δ}
constMethR-sub σ = refl

extRTail-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (extRTail {Γ}) ≡ extRTail {Δ}
extRTail-sub σ = refl

extRMethsK-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (extRMethsK {Γ}) ≡ extRMethsK {Δ}
extRMethsK-sub σ =
  trans (methsFrom-sub (cdTake 52 KnotD) σ constMethR extRTail)
        (cong₂ (methsFrom (cdTake 52 KnotD)) (constMethR-sub σ) (extRTail-sub σ))

extRK-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (i k : RTm Γ) →
            subTm σ (extRK i k) ≡ extRK (subTm σ i) (subTm σ k)
extRK-sub σ i k =
  cong (λ z → ielim KnotD (subTm σ i) z (subTm σ k)) (extRMethsK-sub σ)

app₂-cong₃ : {Γ : Cx} {a a' b b' c c' : RTm Γ} →
             a ≡ a' → b ≡ b' → c ≡ c' → app (app a b) c ≡ app (app a' b') c'
app₂-cong₃ refl refl refl = refl

extRNK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (d n ρ : RTm Γ) →
             subTm τ (extRNK d n ρ)
             ≡ extRNK (subTm τ d) (subTm τ n) (subTm τ ρ)
extRNK-sub τ d n ρ = cong lam (app₂-cong₃ h1 (sub-w {σ = τ} n) (sub-w {σ = τ} ρ))
  where
    h1 : subTm (extS τ) (extRK (pair sVar (nsuc (w d))) (var vz))
         ≡ extRK (pair sVar (nsuc (w (subTm τ d)))) (var vz)
    h1 = trans (extRK-sub (extS τ) (pair sVar (nsuc (w d))) (var vz))
               (cong (λ z → extRK (pair sVar (nsuc z)) (var vz)) (sub-w {σ = τ} d))
