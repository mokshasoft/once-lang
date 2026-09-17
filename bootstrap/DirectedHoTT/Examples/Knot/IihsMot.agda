------------------------------------------------------------------------
-- OCP-0009 · KNOT — `iihsK` PART 1: the motive, `D`/`ms` BUNDLED.
--
--     iihs D ms σ iι       p = unit
--     iihs D ms σ (iρ j C) p =
--       pair (ielim D (subTm σ j) ms (fst p))
--            (iihs D ms (iext σ (fst p)) C (snd p))
--     iihs D ms σ (iκ κ C) p = iihs D ms (iext σ (fst p)) C (snd p)
--
-- ⚠⚠ NOT A CLONE OF `ihsK`, measured.  Three real differences:
--     · `σ` is a passenger that CHANGES at every field (`iext`);
--     · the recursive index is `subTm σ j`, so the row applies
--       `subTmAtK`;
--     · hence FIVE passengers, not four.
--   ⇒ it composes two other object-level programs (`subTmAtK` ✅,
--     `iextK` ⬜ OWED) where `ihs` composed none.
--
-- ★ `σ`'s SOURCE depth is the SCRUTINEE's index depth — the ICon being
--   eliminated lives there and σ maps out of its telescope — so it is
--   read from the ambient index rather than passed.  That is exactly
--   `Knot/IPayTyMot`'s shape, and the ambient index is read ONCE, at
--   Π-depth 1, which is the only depth that survives `⊢methLam`'s
--   `renTy (extR (extR vs))`.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR (expected, on `ihsK`'s evidence).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.IihsMot where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; snd; Π; Σ'; Nat; εwkTy; IMu )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; ⊢var; here; there; ⊢snd; ty-Π; ty-Σ; ty-IMu; ty-Nat )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy; ty-SubTy )

iihsMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
-- ★★★ THE EXPERIMENT: `D` and `ms` as ONE `Σ'` passenger, so FOUR
--   passengers instead of five.  ⚠ It must be a KERNEL `Σ'`: `D` is at
--   `sIDesc` and `ms` at `sTm`, different sorts, so no object-level pair
--   exists — and projecting a `Σ'` is `⊢fst`/`⊢snd`, not a `Tm-fstK`
--   tower.
iihsMotK =
  Π Nat
   (Π (SubTy (snd (var (vs (vs vz)))) (var vz))
    (Π (Σ' (K (pair sIDesc (var (vs vz))))
           (K (pair sTm (var (vs (vs vz))))))
     (Π (K (pair sTm (var (vs (vs vz)))))
        (K (pair sTm (var (vs (vs (vs vz))))))))) 

⊢iihsMotK : {Γ : Ctx} →
            ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty iihsMotK
⊢iihsMotK =
  ty-Π ty-Nat
   (ty-Π (ty-SubTy (⊢snd (⊢var (there (there here)))) (⊢var here))
    (ty-Π (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
                (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here))))))
     (ty-Π (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
        (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there (there here))))))))) 

------------------------------------------------------------------------
-- ★ THE JUNK METHOD — and for `cICon-i` it is the RIGHT answer:
--   `iihs D ms σ iι p = unit`, and the junk body IS `Tm-unitK`.
--
-- ⚠ SEVEN LAMS: `⊢methLam`'s three, then the motive's FOUR passengers.
--   Counting back from the body, `n` is `there³ here` and the ambient
--   index `there⁶ here`.
--
-- ★ IT COVERS ROW 48 (`cICon-i`) TOO, quantified over `k` and `C` —
--   `iihs D ms σ iι p = unit` IS this body, so the junk is the right
--   answer there rather than a placeholder.
------------------------------------------------------------------------

open import DirectedHoTT.Spec.Syntax using ( lam; ICon; IDesc; ε )
open import DirectedHoTT.Spec.Typing using ( _⊢_∷_; ⊢lam; imethTy; IConWf )
open import DirectedHoTT.Lib.IPay using ( ⊢methLam )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-unitK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-unitKv )
open import Agda.Builtin.Nat using () renaming ( Nat to ℕ )

iihsJunk : {Γ : Cx} → RTm Γ
iihsJunk = lam (lam (lam (lam (lam (lam (lam Tm-unitK))))))

⊢iihsJunk : {Γ : Ctx} (k : ℕ) (C : ICon (ε ∙)) →
            IConWf KnotD IPair (◇ ▹ εwkTy IPair) C →
            Γ ⊢ iihsJunk ∷ imethTy KnotD IPair k C iihsMotK
⊢iihsJunk k C wC =
  ⊢methLam KnotD IPair k C KnotWf wC ⊢IPair ⊢iihsMotK
    (⊢lam ty-Nat
      (⊢lam (ty-SubTy (⊢snd (⊢var (there (there (there here))))) (⊢var here))
        (⊢lam (ty-Σ (ty-IMu KnotWf (⊢ixP ⊢sIDesc (⊢var (there here))))
                    (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here))))))
          (⊢lam (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there (there here)))))
            (⊢Tm-unitKv (var (vs (vs (vs vz))))
                        (⊢var (there (there (there here)))))))))
