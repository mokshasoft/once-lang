------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ `renTm vs` AS A SUBSTITUTION, BECAUSE `wkK`
-- IS NOT IT.
--
-- ⚠⚠ `Knot/Wk`'s `wkK : K (s,d) → K (s,suc d)` IS A DIFFERENT RENAMING.
--   Read its two `Var` rows (`Knot/WkRows` §5/§7): `cVar-vz` at
--   `snd ⟨i⟩ ≡ nsuc m` is rebuilt as `cVar-vz` at `m' = nsuc m`, i.e.
--
--        wkK (var vz)     =  var vz          NOT  var (vs vz)
--        wkK (var (vs x)) =  var (vs (wkK x))
--
--   — the identity on de Bruijn INDICES.  That is the weakening which
--   appends a fresh slot at the OUTERMOST end, not `renTm vs`, which
--   appends at the innermost and shifts every index up by one.
--
-- ★★★ AND IT COULD NOT HAVE BEEN `renTm vs`.  `wkK` is DERIVED by
--   `Lib/IWk` as a generic depth-bumping fold, and a generic fold keeps
--   each row's TAG.  A renaming a fold can implement must be stable
--   under going through a binder — `extR ρ ≡ ρ` at the next depth — and
--   the outermost insertion is the only weakening that is.  `renTm vs`
--   becomes `renTm (extR vs)` under a `lam`, a genuinely different
--   renaming, so no tag-preserving fold can be it.
--
-- ⇒ THE TWO AGREE ON CLOSED TERMS AND ONLY THERE.  `payTy D C` is closed
--   (its clauses build `Unit`/`Σ'`/`Mu D`/`εwkTy A` from closed data), so
--   `Knot/PayTy`'s use of `wkK` is sound.  Anything weakening an OPEN
--   term needs this module instead.
--
-- ★ THE FIX IS FREE: `subTm` already handles binders (that is the whole
--   of `Knot/SubMot`), so `renTm vs` is `subTm` at the substitution
--   `x ↦ var (vs x)` — two lines — and `renTm (extR vs)` is `extNK` of
--   it, which `Knot/SubMot` also already has.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.Knot.WkSub where
open import DirectedHoTT.Spec.Syntax
  using ( Cx; RTm; RTy; var; vz; lam; pair; nsuc; Nat; renTm; vs; IMu )
open import DirectedHoTT.Spec.Typing
  using ( Ctx; ⌊_⌋; _⊢_∷_; ⊢var; here; ⊢lam; ⊢nsuc; ty-IMu )
open import DirectedHoTT.Metatheory.SubjectReduction using ( ⊢wk )
open import DirectedHoTT.Examples.Knot.Sorts
  using ( IPair; sTy; ⊢sTy; sTm; ⊢sTm; sVar; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vsK; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.RenMot using ( extRNK; ⊢extRNK )
open import DirectedHoTT.Examples.Knot.RenTm
  using ( renTmAtK; ⊢renTmAtK; vsRenK; ⊢vsRenK )

------------------------------------------------------------------------
-- ★★★ `renTy vs` AND `renTm vs` — AND THEY ARE ONE FUNCTION NOW.
--
-- ⚠⚠ REWRITTEN 2026-09-03 ON `Knot/RenTm` (`PLAN-RENAMING.md` §6 step
--   1c).  The first version expressed `renTm vs` as `subTm` at the
--   substitution `x ↦ var (vs x)`, which is CORRECT but CANNOT COVER THE
--   FAMILY: `extS σ (vs x) = renTm vs (σ x)`, so `Knot/SubMot` needs
--   `renTm vs` and this module imported `Knot/SubMot`.  The kernel
--   defines renaming BEFORE substitution precisely so that cycle does
--   not arise, and now so does the encoding.
--
-- ★ WHAT THAT BUYS, beyond the cycle: `wkTmK` and `wkTyK` are now THE
--   SAME function at two sorts — `renTmAtK` at `sTm` and at `sTy` —
--   where before they were separate `subTmAtK`/`subTyAtK` calls, and
--   neither needs a `sortMap` stability premise.
------------------------------------------------------------------------

-- ★ `vs`, as a RENAMING value.  ⚠ `Knot/RenTm.vsRenK` is the thing
--   `Knot/Wk.wkK` never had: the renaming, NAMED.

wkTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTyK n A = renTmAtK sTy n (nsuc n) (vsRenK n) A

⊢wkTyK : {Γ : Ctx} {n A : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ A ∷ K (pair sTy n) →
         Γ ⊢ wkTyK n A ∷ K (pair sTy (nsuc n))
⊢wkTyK dn dA = ⊢renTmAtK ⊢sTy dn (⊢nsuc dn) (⊢vsRenK dn) dA

wkTmK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTmK n t = renTmAtK sTm n (nsuc n) (vsRenK n) t

⊢wkTmK : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ t ∷ K (pair sTm n) →
         Γ ⊢ wkTmK n t ∷ K (pair sTm (nsuc n))
⊢wkTmK dn dt = ⊢renTmAtK ⊢sTm dn (⊢nsuc dn) (⊢vsRenK dn) dt

-- ★ `renTy (extR vs)` — weakening UNDER one binder, which is `extRNK`
--   of the same renaming.  ⚠ `extR` is where the kernel's layering shows
--   itself: extending a RENAMING needs no `renTm`, which is why
--   `Knot/RenMot` can sit below `Knot/SubMot`.
wkTyUnderK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTyUnderK n A =
  renTmAtK sTy (nsuc n) (nsuc (nsuc n)) (extRNK n (nsuc n) (vsRenK n)) A

⊢wkTyUnderK : {Γ : Ctx} {n A : RTm ⌊ Γ ⌋} →
              Γ ⊢ n ∷ Nat → Γ ⊢ A ∷ K (pair sTy (nsuc n)) →
              Γ ⊢ wkTyUnderK n A ∷ K (pair sTy (nsuc (nsuc n)))
⊢wkTyUnderK dn dA =
  ⊢renTmAtK ⊢sTy (⊢nsuc dn) (⊢nsuc (⊢nsuc dn))
            (⊢extRNK dn (⊢nsuc dn) (⊢vsRenK dn)) dA
