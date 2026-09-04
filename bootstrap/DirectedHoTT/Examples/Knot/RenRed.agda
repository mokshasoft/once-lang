------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ STEP 3's PER-ROW HEAD REDUCTION, and it is
-- EXACTLY what halves 1 and 2 of `Lib/ISubRed` were built to make
-- possible.
--
--     renTmAtK s dd m rn (icon k p)
--       ⟶  ι-ielim           app³ (sel k renMethsK) i p ih, under 2 appˡ
--       ⟶* isubMeths-sel     app³ (sdMeth renGiveK 0 renDescK k) i p ih   (half 1)
--       ⟶* isubMethod-red    icon j (isubPay w …)                          (half 2)
--
-- ★ THE FIVE-ARGUMENT SPINE MATCHES ON THE NOSE: `isubMethod-red` wants
--   `i p ih n σ`, and `renTmAtK` supplies the eliminator's three then the
--   motive's `m` and `rn`.  That was not arranged after the fact — it is
--   why `isubMethod-red` was stated at five arguments.
--
-- ★ WHY RENAMING AND NOT SUBSTITUTION.  `isubMethod-red` takes `ExtNSub`
--   and `FordMapSub` as hypotheses, and only the renaming instantiation
--   has them discharged (`Knot/RenNat.extRNK-sub`; `renFordMap fi b p = p`
--   makes the other `refl`).  `sub-agree` additionally owes `extNK`'s
--   naturality — see `TODO.md`.
--
-- ⚠⚠ AND THE `SubCon` MUST BE EMITTED PER ROW.  `sdMeth renGiveK 0
--   renDescK k` DOES compute to `isubMethod j w` for a concrete `k` — the
--   unsolved constraint prints the very `w` — but `isubPay` is a DEFINED
--   function and not injective, so Agda cannot invert
--   `isubPay _w … = <payload>` to recover it.  `pin-implicits-on-defined-
--   set-types`, fourth customer.  ⇒ the generator emits the `SubCon`; it
--   already knows each row's field list, so this is one more emitted
--   term, not a search.
--
-- ⚠ AND THE CONCLUSION IS STATED AT `fst (pair s dd)`, NOT `s`.  `βfst`
--   is a REDUCTION rule here, not a definitional equality, so a
--   conclusion phrased with `s`/`dd` cannot be discharged by half 2 at
--   all.  The two projections are the caller's to pay.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.RenRed where
open import normalizer.Syntax.Types using ( _≡_; refl; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; Var; vz; vs; app; pair; fst; snd; icon; ICon
        ; iihs; isingle; ilookupD; IDesc )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; done; step; ι-ielim )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-trans )
open import DirectedHoTT.Lib.ICast using ( ⟶*-castᵣ )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD )
open import DirectedHoTT.Examples.Knot.RenTm
  using ( renTmAtK; renTmK; renMethsK; renDescK; renGiveK
        ; hE-knot; hF-knot )
import DirectedHoTT.Lib.ISub as IS
open import DirectedHoTT.Lib.ISub using ( ttsd )
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK )
open import DirectedHoTT.Examples.Knot.RenTm using ( renSmap; renDecStable; renFordMap )
open IS.Sub extRNK renSmap renDecStable renFordMap

infixr 5 _»_
_»_ : {Γ : Cx} {t u v : RTm Γ} → t ⟶* u → u ⟶* v → t ⟶* v
done       » q = q
(step r p) » q = step r (p » q)

------------------------------------------------------------------------
-- ★ THE PER-ROW HEAD REDUCTION — half 1 then half 2, and the five-arg
--   spine of `isubMethod-red` is EXACTLY `renTmAtK`'s: the eliminator's
--   three, then the motive's `m` and `rn`.
------------------------------------------------------------------------

ren-head-red :
  {Γ : Cx} (k : ℕ) (msel : InSD? renDescK k)
  {C : ICon (ε ∙)} (w : SubCon vz C) (j : ℕ) →
  sdMeth renGiveK 0 renDescK k ≡ isubMethod j w →
  (s dd m rn p : RTm Γ) →
  renTmAtK s dd m rn (icon k p) ⟶*
    -- ⚠ `fst (pair s dd)`, NOT `s`: `βfst` is a REDUCTION rule here, not
    --   a definitional equality, so the conclusion must be stated at the
    --   shape `isubMethod-red` actually produces.  Callers pay the two
    --   projections; stating it with `s`/`dd` makes the lemma unusable.
    icon j (isubPay w (fst (pair s dd)) (snd (pair s dd)) m rn p
              (iihs KnotD renMethsK (isingle (pair s dd)) (ilookupD KnotD k) p))
ren-head-red k msel w j eq s dd m rn p =
  ⟶*-appˡ (⟶*-appˡ
    (step (ι-ielim KnotD (pair s dd) renMethsK k p)
          (⟶*-appˡ (⟶*-appˡ (⟶*-appˡ
            (⟶*-castᵣ eq (isubMeths-sel renDescK 0 k msel))))))) »
  isubMethod-red hE-knot hF-knot w j _ _ _ _ _

------------------------------------------------------------------------
-- ★ USE-SITE CHECK.  `judge-abstractions-at-the-use-site`: a helper whose
--   build is elegant and whose CALL is impossible is worth nothing.  For
--   a CONCRETE row, `sdMeth renGiveK 0 renDescK k` should COMPUTE to an
--   `isubMethod j w`, so `eq` is `refl` and Agda infers `w`/`j`.
------------------------------------------------------------------------

-- ⚠⚠ `w` MUST BE EXPLICIT.  `sdMeth renGiveK 0 renDescK 0` DOES compute
--   to `isubMethod j w` — the constraint printed the concrete `w` — but
--   `isubPay` is a DEFINED function and not injective, so Agda cannot
--   invert `isubPay _w … = <that payload>`.  Same trap as `IHAt`/`IndPW`
--   (`pin-implicits-on-defined-set-types`), fourth customer.
--   ⇒ THE GENERATOR MUST EMIT THE `SubCon` PER ROW.  It already knows
--     each row's field list, so this is one more emitted term, not a
--     search.
-- ⇒ AND IT IS CALLABLE.  `judge-abstractions-at-the-use-site`: a helper
--   whose build is elegant and whose CALL is impossible is worth nothing.
--   This is row 0, with its `SubCon` written out as the generator will.
row0-callable : {Γ : Cx} (s dd m rn p : RTm Γ) → _
row0-callable s dd m rn p =
  ren-head-red 0 ttsd (sc-κ (sk-fst n-zero done) sc-ι) 0 refl s dd m rn p
