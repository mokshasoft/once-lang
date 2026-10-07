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
-- ★ `Fin` is the KERNEL's, indexed by a Nat TERM (S7b step 2): `fcase`
--   splits `Fin (suc m)` into `fzero | fsuc (Fin m)`, and the recursion
--   on the index is `natrec` at the motive `Fin n → Fin (suc n)`:
--
--       0     ↦ λ x. fcase0 x
--       suc m ↦ λ x. fcase x fzero (λ y. fsuc (r y))
--
--   with NO transport: every substitution is at variables.  (Its first
--   form was an `ielim` over a Lib family `FinFam`, deleted 2026-10-05;
--   before that a Forded `Fin` needed a `jsub` per `fsuc`.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Examples.WkFin where
import DirectedHoTT.Examples.Lib0 as Lib0
open import DirectedHoTT.Spec.Syntax using ( ∅ᴷ )
open import normalizer.Syntax.Types using ( cong )
open import DirectedHoTT.Spec.Syntax
open Lib0.Spec-Typing hiding ( _×_; _,,_ )
open Lib0.Metatheory-TySub using ( ⊢-cast; wk-cancel-tm )
open Lib0.Lib-NatCode using ( fromI )

-- `El (⌜Fin⌝ n) ≅ᵀ Fin n`
fromFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ El (⌜Fin⌝ n) → Γ ⊢ t ∷ Fin n
fromFin d = ⊢conv d (credᵀ El-⌜Fin⌝)

toFin : {Γ : Ctx} {n t : RTm ⌊ Γ ⌋} → Γ ⊢ t ∷ Fin n → Γ ⊢ t ∷ El (⌜Fin⌝ n)
toFin d = ⊢conv d (csymᵀ (credᵀ El-⌜Fin⌝))

------------------------------------------------------------------------
-- 1. THE MOTIVE THAT MOVES THE INDEX:  M(n) = Fin n → Fin (suc n).
------------------------------------------------------------------------

wkMot : {Γ : Cx} → RTy (Γ ∙)
wkMot = Π (Fin (var vz)) (Fin (nsuc (var (vs vz))))

⊢wkMot : {Γ : Ctx} → (Γ ▹ Nat) ⊢ty wkMot
⊢wkMot = ty-Π (ty-Fin (⊢var here)) (ty-Fin (⊢nsuc (⊢var (there here))))

------------------------------------------------------------------------
-- 2. THE TWO CASES.
------------------------------------------------------------------------

wkZ : {Γ : Cx} → RTm Γ                      -- Fin 0 is empty
wkZ = lam (fcase0 (var vz))

wkS : {Γ : Cx} → RTm ((Γ ∙) ∙)              -- fzero ↦ fzero ; fsuc y ↦ fsuc (r y)
wkS = lam (fcase (var vz) fzero (fsuc (app (var (vs (vs vz))) (var vz))))

module _ {Γ : Ctx} where
  ⊢wkZ : Γ ⊢ wkZ ∷ subTy (single nzero) wkMot
  ⊢wkZ = ⊢lam (ty-Fin ⊢nzero) (⊢fcase0 (ty-Fin (⊢nsuc ⊢nzero)) (⊢var here))

  ⊢wkS : ((Γ ▹ Nat) ▹ wkMot) ⊢ wkS ∷ subTy nrs wkMot
  ⊢wkS = ⊢lam (ty-Fin (⊢nsuc (⊢var (there here))))
           (⊢fcase (ty-Fin (⊢nsuc (⊢nsuc (⊢var (there (there (there here)))))))
                   (⊢var here)
                   (⊢fzero (⊢nsuc (⊢var (there (there here)))))
                   (⊢fsuc (⊢app (⊢var (there (there here))) (⊢var here))))

------------------------------------------------------------------------
-- 3. ★★★ OBJECT-LEVEL WEAKENING: `Fin n → Fin (suc n)`, by `natrec`.
------------------------------------------------------------------------

wkFinTm : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
wkFinTm n k = app (natrec wkZ wkS n) k

⊢wkFinTm : {Γ : Ctx} {n k : RTm ⌊ Γ ⌋} →
           Γ ⊢ n ∷ El ⌜Nat⌝ → Γ ⊢ k ∷ Fin n → Γ ⊢ wkFinTm n k ∷ Fin (nsuc n)
⊢wkFinTm {n = n} {k} dn dk =
  ⊢-cast (cong (λ z → Fin (nsuc z)) (wk-cancel-tm k n))
    (⊢app (⊢natrec ⊢wkMot ⊢wkZ ⊢wkS (fromI dn)) dk)

------------------------------------------------------------------------
-- 4. ★★ …AND IT COMPUTES: `fzero : Fin 1` weakens to `fzero` at index 2 —
--    one natrec step, one β, one fcase.
------------------------------------------------------------------------

wk-fz : {Γ : Cx} → wkFinTm {Γ} (nsuc nzero) fzero ⟶* fzero
wk-fz = step (ξ-appˡ (natrec-suc _ _ _)) (step (β _ _) (step (fcase-z _ _) done))
