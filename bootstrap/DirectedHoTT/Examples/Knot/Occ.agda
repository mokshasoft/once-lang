------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★★★ THE OCCURRENCE CHECK, OBJECT-LEVEL.
--
--     occK s n k t  ∷ Nat      -- 1 if the variable at LEVEL `k` occurs
--                              --   in the sort-`s` term `t` at depth `n`
--
-- ★★★ FIFTY-TWO OF THE FIFTY-THREE ROWS ARE `Lib/IOcc`'s GENERIC FOLD.
--   `nd = id` and `op = max` make them all come out right:
--     `lam`  → its body's answer (a LEVEL does not shift under a binder)
--     `app`  → `max` of the two, which is `∨` on 0/1
--     `Mu D` → `0`, because `Desc` is a closed sort with no variables
--
-- ⚠ THE ONE EXCEPTION IS `cVar-vz`, and it is exceptional for a precise
--   reason: it has NO `iρ` fields (`iκ ⌜Nat⌝ (iκ ford (iκ ford iι))`), so
--   the fold hands back `z` — "does not occur" — where the answer is
--   `eqNat k m`.  A `vz` at depth `nsuc m` IS the variable at level `m`.
--   ⇒ `Lib/IMeths.methsAt` splices it in; the other 52 stay computed.
--
-- ★ `cVar-vs` NEEDS NOTHING.  Its one `iρ` child is the sub-`Var`, and
--   `vs x` is at the same LEVEL as `x` — which is exactly what the
--   generic fold returns.  With indices it would have needed a shift.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.Occ where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; var; lam; app; fst; pair; unit; RTm; IDesc
        ; ICon; ielim; Nat; _◂_; ilookupD; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; ⊢var; here; there; ⊢fst; ⊢lam; ⊢app
        ; ⊢unit; ⊢ielim; ty-Nat; imethTy; imethsTy; imethsTyFrom
        ; IConWf; IDescWfFrom )
open import normalizer.Syntax.Types using ( _≡_; refl; sym; subst )
open import DirectedHoTT.Lib.IPay
  using ( ⊢methLam; ⊢methsAt; ⊢methsCons; Split; spl-nil; spl-step
        ; idwfDrop; splTake )
open import DirectedHoTT.Lib.IMeths using ( cdTake; cdRest; methsAt )
open import DirectedHoTT.Lib.NatEq using ( eqNatTm; ⊢eqNat )
open import DirectedHoTT.Lib.Strong using ( elAsNat )
open import DirectedHoTT.Lib.IOcc
  using ( OccTy; ty-OccTy; occMethod; ⊢occMethod )
open import DirectedHoTT.Examples.Knot.Sorts using ( IPair; ⊢IPair; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc
  using ( KnotD; K; cVar-vz; cVar-vs )
open import DirectedHoTT.Examples.Knot.Wf
  using ( KnotWf; cVar-vzWf; cVar-vsWf )
open import DirectedHoTT.Examples.Knot.Tags using ( tagVar-vz; tagVar-vs )

------------------------------------------------------------------------
-- ★ THE ONE REAL ROW.  ⚠ NO CODOMAIN CAST: `OccTy` is `Π Nat Nat`,
--   fully closed, so `renTy vs (iatCon k i (renTy _ OccTy))` reduces to
--   `Π Nat Nat` DEFINITIONALLY.  (`Knot/ConS`'s motive mentions the
--   index and does not get that.)
------------------------------------------------------------------------

occVz : {Γ : Cx} → RTm Γ
occVz = lam (lam (lam (lam (eqNatTm (var vz) (fst (var (vs (vs vz))))))))

⊢occVz : {Γ : Ctx} →
         Γ ⊢ occVz ∷ imethTy KnotD IPair tagVar-vz cVar-vz OccTy
⊢occVz =
  ⊢methLam KnotD IPair tagVar-vz cVar-vz KnotWf cVar-vzWf ⊢IPair ty-OccTy
    (⊢lam ty-Nat
      (⊢eqNat (⊢var here)
              (elAsNat (⊢fst (⊢var (there (there here)))))))

------------------------------------------------------------------------
-- ★ THE TUPLE — 51 computed rows, the spliced `cVar-vz`, then `cVar-vs`
--   computed again.
------------------------------------------------------------------------

OD51 : IDesc
OD51 = cdRest (cdTake 51 KnotD)

ospl51 : Split KnotD 51 OD51
ospl51 = splTake spl-nil (cdTake 51 KnotD)

-- ★ the generic method, addressed BY INDEX so `methsAt` can walk it.
occAt : {Γ : Cx} → ℕ → RTm Γ
occAt k = occMethod (ilookupD KnotD k)

occTail : {Γ : Cx} → RTm Γ
occTail = pair occVz (pair (occMethod cVar-vs) unit)

⊢occTail : {Γ : Ctx} →
           Γ ⊢ occTail ∷ imethsTyFrom KnotD IPair OccTy 51 OD51
⊢occTail =
  ⊢methsCons KnotD IPair 51 {C = cVar-vz} _ KnotWf
             (idwfDrop (spl-step ospl51) KnotWf) (spl-step ospl51)
             ⊢IPair ty-OccTy ⊢occVz
    (⊢methsCons KnotD IPair 52 {C = cVar-vs} _ KnotWf
                (idwfDrop (spl-step (spl-step ospl51)) KnotWf)
                (spl-step (spl-step ospl51))
                ⊢IPair ty-OccTy
                (⊢occMethod KnotD IPair 52 cVar-vs KnotWf cVar-vsWf ⊢IPair)
                ⊢unit)

occMethsK : {Γ : Cx} → RTm Γ
occMethsK = methsAt (cdTake 51 KnotD) occAt 0 occTail

⊢occMethsK : {Γ : Ctx} → Γ ⊢ occMethsK ∷ imethsTy KnotD IPair OccTy KnotD
⊢occMethsK =
  ⊢methsAt KnotD IPair 0 (cdTake 51 KnotD) KnotWf KnotWf spl-nil
           ⊢IPair ty-OccTy
           -- ⚠ THE PER-ROW DERIVATION MOVES ALONG `look`.  `methsAt`
           --   addresses a row by its INDEX, so the term is
           --   `occMethod (ilookupD KnotD k)` while the goal states the
           --   type at the abstract `C`; `ilookupD D k ≡ C` is exactly
           --   what the `Split` hands over to bridge them.
           (λ {k} {C} wC mem look →
              subst (λ z → _ ⊢ occAt k ∷ imethTy KnotD IPair k z OccTy)
                    look
                    (⊢occMethod KnotD IPair k (ilookupD KnotD k) KnotWf
                       (subst (IConWf KnotD IPair (◇ ▹ εwkTy IPair))
                              (sym look) wC)
                       ⊢IPair))
           occTail ⊢occTail

------------------------------------------------------------------------
-- ★★★ THE WRAPPER.  ⚠ SORT-GENERIC: `occ` runs at every sort, and the
--   motive is the same closed `Π Nat Nat` at all of them.
-- ⚠ NO CASTS.  `iinst i t OccTy` is `OccTy` definitionally (it is
--   closed), and applying it to the level gives `subTy (single k) Nat`,
--   which is `Nat`.  That is the dividend of a CLOSED motive.
------------------------------------------------------------------------

occK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ → RTm Γ → RTm Γ
occK s n k t = app (ielim KnotD (pair s n) occMethsK t) k

⊢occK : {Γ : Ctx} {s n k t : RTm ⌊ Γ ⌋} →
        Γ ⊢ s ∷ Nat → Γ ⊢ n ∷ Nat → Γ ⊢ k ∷ Nat →
        Γ ⊢ t ∷ K (pair s n) →
        Γ ⊢ occK s n k t ∷ Nat
⊢occK ds dn dk dt =
  ⊢app (⊢ielim KnotWf ty-OccTy (⊢ixP ds dn) ⊢occMethsK dt) dk
