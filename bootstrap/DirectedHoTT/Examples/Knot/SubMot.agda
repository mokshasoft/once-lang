------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ THE MOTIVE `extS`/`subTm` ELIMINATE AT, AND
-- THE 51 METHODS THAT DO NOTHING.
--
--     M(i, t) = ∀n. (Var (snd ⟨i⟩) → Tm n) → Tm n
--
-- ⚠⚠ WHY EVERY ROW GETS A METHOD.  The knot is ONE description, so
--   casing on a `Var` is an `ielim KnotD` — which demands a method for
--   all 53 rows at a motive defined at all seven SORTS.  Only the two
--   `cVar-*` rows do anything; the other 51 are noise the eliminator
--   insists on.
--
-- ★ THE MOTIVE NEED NOT BE SORT-DEPENDENT, which is the thing worth
--   checking before building anything.  The type above is uniform in the
--   sort — it simply says something UNINTERESTING at the other six.
--   ⚠ But it must still be INHABITED there, and it is: the knot has
--   CLOSED `Tm` rows (`Tm-nzeroK`), so `Tm n` is inhabited at every `n`,
--   variable or not.  Had it not been, the motive would have had to case
--   on the sort tag — a `natrec` over codes — and every one of the 51
--   would have paid for it.
--
-- ★★ AND THE METHOD IS THE SAME TERM AT EVERY ROW.  `imethTy` binds
--   exactly THREE things — the index, the payload, the IH tuple —
--   regardless of how many fields the row has; the motive adds two more.
--   So a method that ignores everything is five `lam`s and a constant,
--   and it is proved once at an ABSTRACT `C`, exactly as `Lib/IFold`
--   proves its fold method.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.SubMot where
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax
  using ( Cx; ε; _∙; vz; vs; RTy; RTm; var; pair; snd; Nat; Π; IMu; εwkTy )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ◇; _▹_; ⌊_⌋; _⊢_∷_; _⊢ty_; ⊢var; here; there
        ; ⊢snd; ty-Nat; ty-Π; ty-IMu )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; sTm; sVar; ⊢sTm; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )

------------------------------------------------------------------------
-- Binder layout.  The motive is checked at
--     Θ = Γ ▹ εwkTy IPair ▹ K (var vz)
-- so `vz` is the SCRUTINEE and `vs vz` the ambient INDEX.  Under the
-- motive's own `Π Nat`:  n = vz · t = vs vz · i = vs (vs vz).
--
-- ⚠ THE SCRUTINEE NEVER APPEARS.  That is deliberate and it is what
--   makes `iatCon` compute later: instantiating the motive at a row
--   touches only the INDEX slot.
------------------------------------------------------------------------

subMotK : {Γ : Cx} → RTy ((Γ ∙) ∙)
subMotK =
  Π Nat (Π (Π (IMu KnotD IPair (pair sVar (snd (var (vs (vs vz))))))
              (IMu KnotD IPair (pair sTm (var (vs vz)))))
           (IMu KnotD IPair (pair sTm (var (vs vz)))))

⊢subMotK : {Γ : Ctx} →
           ((Γ ▹ εwkTy IPair) ▹ IMu KnotD IPair (var vz)) ⊢ty subMotK
⊢subMotK =
  ty-Π ty-Nat
    (ty-Π (ty-Π (ty-IMu KnotWf
                   (⊢ixP ⊢sVar (⊢snd (⊢var (there (there here))))))
                (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
          (ty-IMu KnotWf (⊢ixP ⊢sTm (⊢var (there here)))))
