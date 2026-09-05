------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE SUBSTITUTION INSTANCE'S TWO HYPOTHESES.
--
--     extNK-sub    : ExtNSub     at `extNK`
--     fordMapK-sub : FordMapSub  at `fordMapK`
--
-- These are what `Lib/ISub.isubMethod-red` leaves to its caller, and the
-- last thing `sub-agree` was waiting on.  `Knot/RenNat` is the same pair
-- for the renaming instance.
--
-- ★★★ AND THE ASYMMETRY IS THE POINT.  At the RENAMING instantiation
--   `FordMapSub` is `refl`, because `renFordMap fi b p = p` IGNORES the
--   tag.  Here:
--
--     fordMapK fi b p = jsub (⌜Id⌝ ⌜Nat⌝ (sortMap (var vz)) (w b))
--                            (symN fi p) (idrefl ⌜Nat⌝ b)
--
--   `b` appears THREE times, so the tag must genuinely be natural.  ⇒ this
--   is the instantiation the D′ finding predicted would be the one to
--   catch a wrong `SubCon` — and it is exactly why `Knot/RenRed.wOf`
--   COMPUTES the classification instead of an emitter writing it.
--
-- ⚠ `constMethsFrom` is `Knot/SubMot`'s local `methsFrom` at a FIXED
--   method — its own header notes the duplication.  If it is ever folded
--   into `Lib/IMeths.methsFrom`, `constMethsFrom-sub` folds into
--   `methsFrom-sub` with it.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubNat where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import normalizer.Syntax.Types using ( _≡_; refl; cong; cong₂; trans )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; Sub; subTm; extS; pair; lam; app; var; vz; vs; nsuc; ielim
        ; IDesc; jsub; ⌜Id⌝; ⌜Nat⌝; idrefl )
open import DirectedHoTT.Lib.Wk using ( w; sub-w )
open import DirectedHoTT.Lib.IMeths using ( CDesc; cd-stop; cd-cons; cdTake )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.Sorts using ( sVar )
open import DirectedHoTT.Lib.ArithComm using ( symN; reflN )
open import DirectedHoTT.Examples.Knot.SubMot
  using ( extNK; extSK; extMethsK; extTail; constMethsFrom; constMeth; sortMap; fordMapK )

-- ★ `constMethsFrom` is `Knot/SubMot`'s local `methsFrom` at a FIXED
--   method, so its naturality is the same three-line induction.
--   ⚠ Its own header notes it duplicates the general shape; if it is ever
--     folded into `Lib/IMeths.methsFrom`, this lemma folds into
--     `methsFrom-sub` with it.
constMethsFrom-sub : {Γ Δ : Cx} {E : IDesc} (W : CDesc E) (σ : Sub Γ Δ) (t : RTm Γ) →
                     subTm σ (constMethsFrom W t) ≡ constMethsFrom W (subTm σ t)
constMethsFrom-sub (cd-stop E) σ t = refl
constMethsFrom-sub (cd-cons W) σ t = cong (pair constMeth) (constMethsFrom-sub W σ t)

extTail-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (extTail {Γ}) ≡ extTail {Δ}
extTail-sub σ = refl

extMethsK-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (extMethsK {Γ}) ≡ extMethsK {Δ}
extMethsK-sub σ =
  trans (constMethsFrom-sub (cdTake 51 KnotD) σ extTail)
        (cong (constMethsFrom (cdTake 51 KnotD)) (extTail-sub σ))

extSK-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (i k : RTm Γ) →
            subTm σ (extSK i k) ≡ extSK (subTm σ i) (subTm σ k)
extSK-sub σ i k =
  cong (λ z → ielim KnotD (subTm σ i) z (subTm σ k)) (extMethsK-sub σ)

app₂-cong₃ : {Γ : Cx} {a a' b b' c c' : RTm Γ} →
             a ≡ a' → b ≡ b' → c ≡ c' → app (app a b) c ≡ app (app a' b') c'
app₂-cong₃ refl refl refl = refl

-- ★★★ `ExtNSub` AT THE SUBSTITUTION INSTANTIATION — the hypothesis
--   `Lib/ISub.isubMethod-red` leaves to its caller, and the last thing
--   `sub-agree` was waiting on.
extNK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (d n σ : RTm Γ) →
            subTm τ (extNK d n σ) ≡ extNK (subTm τ d) (subTm τ n) (subTm τ σ)
extNK-sub τ d n σ = cong lam (app₂-cong₃ h1 (sub-w {σ = τ} n) (sub-w {σ = τ} σ))
  where
    h1 : subTm (extS τ) (extSK (pair sVar (nsuc (w d))) (var vz))
         ≡ extSK (pair sVar (nsuc (w (subTm τ d)))) (var vz)
    h1 = trans (extSK-sub (extS τ) (pair sVar (nsuc (w d))) (var vz))
               (cong (λ z → extSK (pair sVar (nsuc z)) (var vz)) (sub-w {σ = τ} d))

------------------------------------------------------------------------
-- ★★★ AND `FordMapSub` — WHERE THE FORD TAG IS **LIVE**.
--
--     fordMapK fi b p = jsub (⌜Id⌝ ⌜Nat⌝ (sortMap (var vz)) (w b))
--                            (symN fi p) (idrefl ⌜Nat⌝ b)
--
-- ⚠ The renaming instance discharges this by `refl` (`renFordMap fi b p =
--   p` ignores everything).  Here `b` appears THREE times, so the tag has
--   to be genuinely natural — this is the instantiation the D′ finding
--   said would be the one to catch a wrong `SubCon`.
------------------------------------------------------------------------

sortMap-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (s : RTm Γ) →
              subTm τ (sortMap s) ≡ sortMap (subTm τ s)
sortMap-sub τ s = refl

symN-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (a p : RTm Γ) →
           subTm τ (symN a p) ≡ symN (subTm τ a) (subTm τ p)
symN-sub τ a p =
  cong (λ z → jsub (⌜Id⌝ ⌜Nat⌝ (var vz) z) (subTm τ p) (reflN (subTm τ a)))
       (sub-w {σ = τ} a)

jsub-cong₃ʳ : {Γ : Cx} {M M' : RTm (Γ ∙)} {P P' T T' : RTm Γ} →
              M ≡ M' → P ≡ P' → T ≡ T' → jsub M P T ≡ jsub M' P' T'
jsub-cong₃ʳ refl refl refl = refl

fordMapK-sub : {Γ Δ : Cx} (τ : Sub Γ Δ) (fi b p : RTm Γ) →
               subTm τ (fordMapK fi b p)
               ≡ fordMapK (subTm τ fi) (subTm τ b) (subTm τ p)
fordMapK-sub τ fi b p =
  jsub-cong₃ʳ
    (cong (λ z → ⌜Id⌝ ⌜Nat⌝ (sortMap (var vz)) z) (sub-w {σ = τ} b))
    (symN-sub τ fi p)
    refl
