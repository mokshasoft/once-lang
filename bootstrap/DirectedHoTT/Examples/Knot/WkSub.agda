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
  using ( IPair; sTy; sTm; ⊢sTm; sVar; ⊢sVar; ⊢ixP )
open import DirectedHoTT.Examples.Knot.Desc using ( KnotD; K )
open import DirectedHoTT.Examples.Knot.Wf using ( KnotWf )
open import DirectedHoTT.Examples.Knot.Ctors using ( Tm-varK )
open import DirectedHoTT.Examples.Knot.CtorsV using ( ⊢Tm-varKv )
open import DirectedHoTT.Examples.Knot.Build using ( Var-vsK; ⊢Var-vsKt )
open import DirectedHoTT.Examples.Knot.Terms using ( SubTy )
open import DirectedHoTT.Examples.Knot.SubMot using ( extNK; ⊢extNK )
open import DirectedHoTT.Examples.Knot.SubApp
  using ( subTyAtK; ⊢subTyAtK; subTmAtK; ⊢subTmAtK )

------------------------------------------------------------------------
-- ★ `vs`, AS A SUBSTITUTION.  ⚠ It RAISES, like `nrs` and unlike
--   `single`/`extS` — and unlike `nrs` it does not step the variable.
------------------------------------------------------------------------

wkSubK : {Γ : Cx} → RTm Γ → RTm Γ
wkSubK n = lam (Tm-varK (Var-vsK (renTm vs n) (var vz)))

⊢wkSubK : {Γ : Ctx} {n : RTm ⌊ Γ ⌋} →
          Γ ⊢ n ∷ Nat → Γ ⊢ wkSubK n ∷ SubTy n (nsuc n)
⊢wkSubK dn =
  ⊢lam (ty-IMu KnotWf (⊢ixP ⊢sVar dn))
       (⊢Tm-varKv _ (⊢nsuc (⊢wk dn)) (⊢Var-vsKt (⊢wk dn) (⊢var here)))

------------------------------------------------------------------------
-- ★★ `renTy vs` AND `renTy (extR vs)`, THE TWO THE RULES ACTUALLY NAME.
--   ⚠ `extR vs` is `extS` of `vs`, so it is `extNK` of `wkSubK` — the
--   same relationship the kernel's two renamings have.
------------------------------------------------------------------------

wkTyK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTyK n A = subTyAtK n (nsuc n) (wkSubK n) A

⊢wkTyK : {Γ : Ctx} {n A : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ A ∷ K (pair sTy n) →
         Γ ⊢ wkTyK n A ∷ K (pair sTy (nsuc n))
⊢wkTyK dn dA = ⊢subTyAtK dn (⊢nsuc dn) (⊢wkSubK dn) dA

wkTmK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTmK n t = subTmAtK n (nsuc n) (wkSubK n) t

⊢wkTmK : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} →
         Γ ⊢ n ∷ Nat → Γ ⊢ t ∷ K (pair sTm n) →
         Γ ⊢ wkTmK n t ∷ K (pair sTm (nsuc n))
⊢wkTmK dn dt = ⊢subTmAtK dn (⊢nsuc dn) (⊢wkSubK dn) dt

-- ★ `renTy (extR vs)` — weakening UNDER one binder.
wkTyUnderK : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkTyUnderK n A = subTyAtK (nsuc n) (nsuc (nsuc n)) (extNK n (nsuc n) (wkSubK n)) A

⊢wkTyUnderK : {Γ : Ctx} {n A : RTm ⌊ Γ ⌋} →
              Γ ⊢ n ∷ Nat → Γ ⊢ A ∷ K (pair sTy (nsuc n)) →
              Γ ⊢ wkTyUnderK n A ∷ K (pair sTy (nsuc (nsuc n)))
⊢wkTyUnderK dn dA =
  ⊢subTyAtK (⊢nsuc dn) (⊢nsuc (⊢nsuc dn)) (⊢extNK dn (⊢nsuc dn) (⊢wkSubK dn)) dA
