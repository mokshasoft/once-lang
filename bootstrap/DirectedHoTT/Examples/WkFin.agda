-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · EXAMPLES — ★★★ SPIKE: CAN AN `ielim` PRODUCE AN ELEMENT OF
-- ITS OWN FAMILY AT A **SHIFTED INDEX**?
--
-- HANDOFF-2026-08-26 step A, second half — the gate on the judgement
-- layer.  `_∋_∷_`'s `here` is
--
--     here : (Γ ▹ A) ∋ vz ∷ renTy vs A
--
-- so its index mentions `renTy`, a FUNCTION of an encoded term.  For the
-- judgement to be describable, weakening must EXIST object-level: an
-- `ielim` returning a KNOT ELEMENT at a different index.  `Lib/IFold`
-- does not reach it — that folds into a CONSTANT `Nat` motive, and this
-- needs a motive that MOVES THE INDEX.
--
-- ★ THE SMALLEST THING WITH BOTH FEATURES is `wkFin : Fin n → Fin (suc n)`
--   over `Examples/Scoped`'s `Fin`: two constructors, and
--
--     M(i, t) = Fin (suc ⟨i⟩)
--
--   is a motive that mentions the INDEX slot and lands in the family
--   being eliminated.
--
-- ★ `Fin` IS FIBRED OVER ℕ (`Lib/FinFam`, `Lib/NatFib`): `Fin 0 = ∅`,
--   `Fin (suc m) = fzero | fsuc (Fin m)`.  So the method is a case on
--   the index, each constructor's method sits at `suc m` — where `fsuc`'s
--   field is at `m` DEFINITIONALLY — and weakening is
--
--       fzero  ↦ fzero        fsuc y ↦ fsuc (wk y)
--
--   with NO transport.  (Under the Forded `Fin` the `fsuc` case needed a
--   `jsub` along its equation: 2026-09-27's version of this file.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkFin where
open import normalizer.Syntax.Types using ( _,_; cong; sym ) renaming ( subst to subst' )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢wk; ⊢-cast )
open import DirectedHoTT.Lib.Sugar using ( Cons; []; _∷_; nth-z; nth-s; []ᵈ; selF; subC; tag )
open import DirectedHoTT.Lib.Tel
open import DirectedHoTT.Lib.MethAt
open import DirectedHoTT.Lib.NatFib
open import DirectedHoTT.Lib.FinFam

-- `El (⌜IMu⌝ ⌜Nat⌝ FinD n) ≅ᵀ Fin n`
fromFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD n) → Γ ⊢ t ∷ FinI n
fromFin d = ⊢conv d (credᵀ El-⌜IMu⌝)

toFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ FinI n → Γ ⊢ t ∷ El (⌜IMu⌝ ⌜Nat⌝ FinD n)
toFin d = ⊢conv d (csymᵀ (credᵀ El-⌜IMu⌝))

------------------------------------------------------------------------
-- 1. THE MOTIVE THAT MOVES THE INDEX:  M(i, t) = Fin (suc i).
------------------------------------------------------------------------

wkMot : {Γ : Cx} → RTy ((Γ ∙) ∙)
wkMot = FinI (nsuc (var (vs vz)))

⊢wkMot : {Γ : Ctx} → ((Γ ▹ El ⌜Nat⌝) ▹ FinI (var vz)) ⊢ty wkMot
⊢wkMot = ty-IMu ⊢⌜Nat⌝ ⊢FinD (⊢isuc (⊢var (there here)))

------------------------------------------------------------------------
-- 2. THE METHODS, at the successor case's index `suc m`: the method
--    context is `m`, the payload, the hypotheses.
------------------------------------------------------------------------

mfz mfs : {Γ : Cx} → RTm Γ
mfz = lam (lam ffz)                          -- fzero  ↦ fzero
mfs = lam (lam (ffs (fst (var vz))))         -- fsuc y ↦ fsuc (wk y)

WkMs : {Γ : Cx} → Cons Γ 2
WkMs = mfz ∷ mfs ∷ []

wkM : {Γ : Cx} → RTm Γ
wkM = methN (methAt []) (methAt WkMs)

module _ {Γ : Ctx} where
  private
    dS = allD (⊢wk ⊢⌜Nat⌝) (FinOK {Γ})
    -- `m`, two binders out
    dm₂ : {A : RTy _} {B : RTy _} → (((Γ ▹ El ⌜Nat⌝) ▹ A) ▹ B) ⊢ var (vs (vs vz)) ∷ El ⌜Nat⌝
    dm₂ = ⊢var (there (there here))

  perS : PerKAt (Γ ▹ El ⌜Nat⌝) ⌜Nat⌝ (renTm vs FinD) (wk1M wkMot) (nsuc (var vz))
                (selF (subC τS ⌜ FinTs ⌝ₛ)) zero WkMs
  perS = entN {Ts = FinTs} {T = fzeroT} []ᵈ FinOK ⊢wkMot nthᵗ-z (⊢ffz (⊢isuc dm₂))
      ∷ₐ entN {Ts = FinTs} {T = fsucT} []ᵈ FinOK ⊢wkMot (nthᵗ-s nthᵗ-z) (⊢ffs (⊢isuc dm₂) (⊢fst (⊢var here)))
      ∷ₐ []ₐ

  ⊢wkM : Γ ⊢ wkM ∷ MethTy ⌜Nat⌝ FinD wkMot
  ⊢wkM = ⊢methN ⊢FinD ⊢wkMot (⊢caseZ []ᵈ dS ⊢wkMot []ₐ) (⊢caseS []ᵈ dS ⊢wkMot perS)

------------------------------------------------------------------------
-- 3. ★★★ OBJECT-LEVEL WEAKENING: `Fin n → Fin (suc n)`, by `ielim`.
------------------------------------------------------------------------

wkFinTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkFinTm n k = ielim FinD n wkM k

-- ⚠ ONE `wk-single`: `iinst n k M` weakens the index past the scrutinee
--   binder and substitutes it back — the residue every two-slot motive pays.
⊢wkFinTm : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ k ∷ FinI n → Γ ⊢ wkFinTm n k ∷ FinI (nsuc n)
⊢wkFinTm {n = n} dn dk =
  ⊢-cast (cong (λ z → FinI (nsuc z)) (wk-single n))
    (⊢ielim ⊢⌜Nat⌝ ⊢FinD ⊢wkMot ⊢wkM dn dk)

------------------------------------------------------------------------
-- 4. ★★ …AND IT COMPUTES: `fz : Fin 1` weakens to `fzero` at index 2 —
--    the index case, the tag selection, two β.
------------------------------------------------------------------------

wk-fz : {Γ : Cx} → wkFinTm {Γ} (nsuc nzero) ffz ⟶* ffz
wk-fz {Γ} =
  ⟶*-trans ιN-s
    (subst' (λ X → app (app X q) h ⟶* ffz) (sym (methAt-sub (single nzero) WkMs))
      (⟶*-trans (methAt-β nth-z) (step (ξ-appˡ (β _ _)) (step (β _ _) done))))
  where
    q : RTm Γ
    q = pair (tag zero) unit
    h = dih FinD wkM (app FinD (nsuc nzero)) q
