------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `iinstK` AGREES WITH `iinst`.
--
--     iinst-agree : iinstK ⌈|Γ|⌉ ⌈j⌉ ⌈t⌉ ⌈M⌉ ⟶* ⌈ iinst j t M ⌉
--
-- Discharges the ledger's `iinstK` entry, which called the shot exactly:
--     ⬜ OWED — agreement with `iinst`; two `subTyAtK`s and no trick,
--               so a corollary of theirs.
--
--   meta   iinst j t M = subTy (single t) (subTy (extS (single j)) M)
--   object iinstK n i t M =
--            subTyAtK (nsuc n) n (singleK n t)
--              (subTyAtK (nsuc (nsuc n)) (nsuc n)
--                        (extNK (nsuc n) n (singleK n i)) M)
--
-- ★ IT IS A COROLLARY BECAUSE ALL THREE INGREDIENTS ARE DISCHARGED:
--     subTyAtK  ✅ `Knot/TyAgree.subTyAtK-agree`
--     singleK   ✅ `Knot/SubAgree.single-Represents`
--     extNK     ✅ `Knot/SubExt.extS-Represents`
--   ⇒ this module is the composition and nothing else.  That is the
--     shape the ledger predicts for the OTHER eight COMPOSITION entries
--     (`atConK`, `iextK`, `wkTyUnderK`, …): their cost is their callees\'.
--
-- ★ AND THE INDEX BOOKKEEPING IS FREE.  `num (suc n) = nsuc (num n)`
--   (`Lib/NatNum`) and `len (Γ ∙) = suc (len Γ)` (`Knot/Sorts`) are both
--   DEFINITIONAL, so `num (len ((Γ ∙) ∙))` IS `nsuc (nsuc (num (len Γ)))`
--   on the nose — no arithmetic lemma, which is the "no trick".
--
-- ⚠ `iextK` IS NOT IN THIS CLASS, despite sitting in the same module and
--   looking like a twin.  Its entry reads "VIA its factorisation
--   `iext σ t ≡ single t ∘ extS σ`" — it owes a factorisation lemma
--   FIRST, and carries the same two-step debt as `iconSK`.  Do not
--   assume the other compositions are corollaries because this one was.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IExtAgree where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; RTm; RTy; Sub; extS; subTy )
open import DirectedHoTT.Spec.Typing using ( _⟶*_; iinst; single )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-appˡ; ⟶*-ielimᵗ )
open import DirectedHoTT.Lib.RedChain using ( _»_ )
open import DirectedHoTT.Lib.NatNum using ( num )
open import DirectedHoTT.Examples.Knot.Sorts using ( len )
open import DirectedHoTT.Examples.Knot.Map using ( enTm; enTy )
open import DirectedHoTT.Examples.Knot.SubApp using ( subTyAtK )
open import DirectedHoTT.Examples.Knot.IExt using ( iinstK )
open import DirectedHoTT.Examples.Knot.TyAgree using ( subTyAtK-agree )
open import DirectedHoTT.Examples.Knot.SubAgree using ( single-Represents )
open import DirectedHoTT.Examples.Knot.SubExt using ( extS-Represents )

------------------------------------------------------------------------
-- ★ THE MISSING CONGRUENCE — `subTyAtK` in its scrutinee.
--
-- `subTyAtK dd m σ A = subAtK sTy dd m σ A = app (app (subTmK _ A) m) σ`
-- and `subTmK i x = ielim KnotD i subMethsK x`, so a reduction in `A`
-- travels out through one `ielim` and two `app`s.
--
-- ⚠ IT STAYS HERE UNTIL A SECOND CLIENT WANTS IT.  It looks like
--   `Knot/SubApp` material — that is where `subTyAtK` lives — but one
--   customer is not evidence that a lemma is shared
--   (`judge-abstractions-at-the-use-site`).  Move it when something
--   else needs it.
--
-- ⚠ IT IS STATED AT `subTyAtK`, NOT AT `subAtK`.  The sort argument is
--   what makes `subAtK` usable at both sorts, and a congruence that
--   quantified it would be no more general here — every client of this
--   lemma is at `sTy`, because that is where the nesting happens.
------------------------------------------------------------------------
⟶*-subTyAtK : {Γ : Cx} {dd m σ A A' : RTm Γ} →
              A ⟶* A' → subTyAtK dd m σ A ⟶* subTyAtK dd m σ A'
⟶*-subTyAtK h = ⟶*-appˡ (⟶*-appˡ (⟶*-ielimᵗ h))

------------------------------------------------------------------------
-- ★★★ THE AGREEMENT.
------------------------------------------------------------------------
iinst-agree : {Γ Θ : Cx} (j t : RTm Γ) (M : RTy ((Γ ∙) ∙)) →
              iinstK {Θ} (num (len Γ)) (enTm j) (enTm t) (enTy M)
              ⟶* enTy {Γ} {Θ} (iinst j t M)
-- ⚠ `extS-Represents` takes the DEPTH `d` explicitly, BEFORE the witness:
--     extS-Represents : (d : RTm Θ) → Represents σ s →
--                       Represents (extS σ) (extNK d (num (len Δ)) s)
--   and the `d` the object term uses is `nsuc n`, written here as
--   `num (len (Γ ∙))` — definitionally equal, and it says WHY it is a
--   successor rather than asserting the arithmetic.
iinst-agree {Γ} {Θ} j t M =
  ⟶*-subTyAtK
    (subTyAtK-agree
       (extS-Represents (num (len (Γ ∙))) (single-Represents (num (len Γ)))) M)
  » subTyAtK-agree (single-Represents (num (len Γ)))
                   (subTy (extS (single j)) M)
