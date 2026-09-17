------------------------------------------------------------------------
-- OCP-0009 · KNOT — `iihsK` PART 5: the program, and `ifieldsK`.
--
--     iihs   D ms σ C p     -- `Spec/Syntax:1222`
--     ifields D i ms σ C m p = app (app (app m i) p) (iihs D ms σ C p)
--
-- ★ `Knot/Ihs`'s shape with TWO additions, and both are what "indexed"
--   means here:
--     · the substitution `σ` is a real argument (`SubTy dd n`), where
--       the non-indexed `ihs` has none;
--     · so the ICon carries its OWN depth `dd`, distinct from the
--       target depth `n`.
--   `D` and `ms` ride as ONE kernel `Σ'` (`iihsMotK`'s bundling), so the
--   wrapper builds that pair — `⊢algK` — rather than passing two slots.
--
-- ⚠ `dd` IS LEFT GENERAL even though `ι-ielim` only ever needs
--   `dd = 1`: `ilookupD D k : ICon (ε ∙)` and `isingle i : Sub (ε ∙) Γ`,
--   so the rule's use site is `⊢ilookupDK`'s `K (pair sICon (nsuc
--   nzero))` and `⊢isingleK`'s `SubTy (num 1) n`.  The specialisation
--   belongs in the KERNEL-ORDER ADAPTER, not in the program.
--
-- ⚠ NEEDS THE COMPACTING COLLECTOR.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Iihs where

open import DirectedHoTT.Spec.Syntax
  using ( Cx; _∙; RTm; RTy; var; vz; vs; pair; fst; snd; app; lam; Π; Nat
        ; εwkTy; IMu; Σ'; renTm; ielim; nzero; nsuc )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢ty_; _⊢_∷_; ⊢var; here; there; ⊢pair; ⊢ielim
        ; ty-IMu; ty-Nat; wk-single )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; ⊢IPair; sTm; ⊢sTm; sICon; ⊢sICon; sIDesc; ⊢sIDesc; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-appK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-appKv )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast; ⊢wk )
open import normalizer.Syntax.Types using ( cong; sym )
open import DirectedHoTT.Examples.Knot.IihsMot using ( iihsMotK; ⊢iihsMotK )
open import DirectedHoTT.Examples.Knot.IihsRho using ( ⊢iihsAppK )
open import DirectedHoTT.Examples.Knot.IihsMeths using ( iihsMethsK; ⊢iihsMethsK )

------------------------------------------------------------------------
-- ★ THE BUNDLED PASSENGER — `D` and `ms` as one kernel `Σ'`.
--
-- ⚠ ONE CAST, and it is `wk-single`: the codomain `K (pair sTm (w n))`
--   is instantiated at `D`, and `subTy σ (IMu D I i) = IMu D I (subTm σ
--   i)` leaves the description alone, so only the INDEX moves.
------------------------------------------------------------------------

⊢algK : {Γ : Ctx} {n D ms : RTm ⌊ Γ ⌋} →
        Γ ⊢ n ∷ Nat → Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ ms ∷ K (pair sTm n) →
        Γ ⊢ pair D ms ∷ Σ' (K (pair sIDesc n)) (K (pair sTm (renTm vs n)))
⊢algK {n = n} {D = D} dn dD dms =
  ⊢pair (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢wk dn))) dD
        (⊢-cast (cong (λ z → K (pair sTm z)) (sym (wk-single {v = D} n))) dms)

------------------------------------------------------------------------
-- ★★★ `iihsK`, AS A FUNCTION.
------------------------------------------------------------------------

iihsK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
iihsK n dd D ms σ C p =
  app (app (app (app (ielim KnotD (pair sICon dd) iihsMethsK C) n) σ) (pair D ms)) p

⊢iihsK : {Γ : Ctx} {n dd D ms σ C p : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat →
         Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ ms ∷ K (pair sTm n) →
         Γ ⊢ σ ∷ SubTy dd n → Γ ⊢ C ∷ K (pair sICon dd) →
         Γ ⊢ p ∷ K (pair sTm n) →
         Γ ⊢ iihsK n dd D ms σ C p ∷ K (pair sTm n)
-- ⚠ `dd`/`u` PINNED: they occur only under `iinst`, which is DEFINED
--   and so not injective — `⊢ihsK` pays exactly the same.
⊢iihsK {dd = dd} {C = C} dn ddd dD dms dσ dC dp =
  ⊢iihsAppK {dd = dd} {u = C}
            (⊢ielim KnotWf ⊢iihsMotK (⊢ixP ⊢sICon ddd) ⊢iihsMethsK dC)
            dn ddd dσ (⊢algK dn dD dms) dp

------------------------------------------------------------------------
-- ★★★ AND `ifieldsK` — `app (app (app m i) p) (iihs …)`.
--
-- ⚠ THREE `Tm-appK`s, not two: `ifields` applies the method to the
--   INDEX as well as the payload (`fields` does not), which is the one
--   place the index appears in the contractum.
------------------------------------------------------------------------

ifieldsK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ →
           RTm Γ → RTm Γ → RTm Γ
ifieldsK n dd D i ms σ C m p =
  Tm-appK (Tm-appK (Tm-appK m i) p) (iihsK n dd D ms σ C p)

⊢ifieldsK : {Γ : Ctx} {n dd D i ms σ C m p : RTm ⌊ Γ ⌋} →
            Γ ⊢ n ∷ Nat → Γ ⊢ dd ∷ Nat →
            Γ ⊢ D ∷ K (pair sIDesc n) → Γ ⊢ i ∷ K (pair sTm n) →
            Γ ⊢ ms ∷ K (pair sTm n) → Γ ⊢ σ ∷ SubTy dd n →
            Γ ⊢ C ∷ K (pair sICon dd) → Γ ⊢ m ∷ K (pair sTm n) →
            Γ ⊢ p ∷ K (pair sTm n) →
            Γ ⊢ ifieldsK n dd D i ms σ C m p ∷ K (pair sTm n)
⊢ifieldsK {n = n} dn ddd dD di dms dσ dC dm dp =
  ⊢Tm-appKv n dn (⊢Tm-appKv n dn (⊢Tm-appKv n dn dm di) dp)
                 (⊢iihsK dn ddd dD dms dσ dC dp)
