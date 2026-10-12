-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · KNOT — ★ THE DEFINITION CONTEXT'S FORMATION, internally
-- (PLAN-REF K4, the image of `Spec/SigWf`).
--
-- Over a quoted signature `q`, entry `m` is well-formed when its declared
-- type is a type and its body inhabits it, both judged by the Knot's
-- typing family at the parameter `(q , m)`: the entry's PREFIX is the
-- bound, so an entry cannot cite itself or a later name (acyclicity, as
-- `Spec/SigWf.WfUpTo`):
--
--     ⌜EntryOK⌝ q m   = ⌜⊢ty⌝ (q , m) ◇ (typesQ q m)  ×  ⌜⊢⌝ (q , m) ◇ (bodiesQ q m) (typesQ q m)
--     ⌜WfUpTo⌝ q 0     = Unit
--     ⌜WfUpTo⌝ q (k+1) = ⌜WfUpTo⌝ q k  ×  ⌜EntryOK⌝ q k
--     ⌜WfK⌝ q          = ⌜WfUpTo⌝ q (sizeQ q)
--
-- `Spec/SigWf.WfK` itself, not its `EntriesOK` reading (`Π m. m+1 ≤ size →
-- …`): that form's ENCODING needs one internal function of a variable `m`
-- returning entry m's closed proof — a table built by internal case
-- analysis — where the recursive form is nested pairs.
--
-- Faithfulness (`⌜WfK⌝ ⌜𝒮⌝` inhabited iff `WfK 𝒮`) reads entry m at the
-- bound m: the K5 layer is at every bound `𝓃` (PLAN-REF 2026-10-12).
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
open import DirectedHoTT.Spec.SigExtend using ( _⊑ᴰ_ )
import DirectedHoTT.Examples.PwCore as Core₀
open import DirectedHoTT.Spec.Base hiding ( _,,_; _×_ )
module DirectedHoTT.Examples.Knot.SigWf (𝒮 : Defs) (wf : WfK 𝒮) (core : Core₀.Kc ⊑ᴰ 𝒮) where

open import normalizer.Syntax.Types using ( _≡_; refl; cong )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 (Defs.size 𝒮)
open import DirectedHoTT.Metatheory.TySub 𝒮 (Defs.size 𝒮) using ( ⊢wk )
open import DirectedHoTT.Lib.Strong 𝒮 (Defs.size 𝒮) using ( natAsEl; elAsNat )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf using ( dep; ⊢dep' )
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx; ⊢quoteCtx )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝; tAt; ⊢tAt; sizeQ; typesQ; bodiesQ; ⊢sizeQ; ⊢typesQ; ⊢bodiesQ; wkQ )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; ⊢JT; tyIx; tmIx; ⊢tyIx; ⊢tmIx )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf core using ( D⊢; ⊢D⊢ )

private
  variable
    Δ : Cx

------------------------------------------------------------------------
-- 1. ★ ONE ENTRY, judged at its prefix
------------------------------------------------------------------------

-- `◇ ⊢ty typesQ q m` and `◇ ⊢ bodiesQ q m ∷ typesQ q m`, at the bound m
⌜EntryTy⌝ ⌜EntryTm⌝ : RTm Δ → RTm Δ → RTm Δ
⌜EntryTy⌝ q m = ⌜IMu⌝ JT (D⊢ (tAt q m)) (tyIx (dep ε) (quoteCtx ◇) (typesQ q m))
⌜EntryTm⌝ q m = ⌜IMu⌝ JT (D⊢ (tAt q m)) (tmIx (dep ε) (quoteCtx ◇) (bodiesQ q m) (typesQ q m))

⌜EntryOK⌝ : RTm Δ → RTm Δ → RTm Δ
⌜EntryOK⌝ q m = ⌜Σ⌝ (⌜EntryTy⌝ q m) (renTm vs (⌜EntryTm⌝ q m))

module _ {Ξ : Ctx} {q m : RTm ⌊ Ξ ⌋} (dq : Ξ ⊢ q ∷ El ⌜QSig⌝) (dm : Ξ ⊢ m ∷ El ⌜Nat⌝) where
  ⊢⌜EntryTy⌝ : Ξ ⊢ ⌜EntryTy⌝ q m ∷ U
  ⊢⌜EntryTy⌝ = ⊢⌜IMu⌝ ⊢JT (⊢D⊢ (⊢tAt dq dm)) (⊢tyIx (⊢dep' ε) (⊢quoteCtx ◇) (⊢typesQ dq dm))

  ⊢⌜EntryTm⌝ : Ξ ⊢ ⌜EntryTm⌝ q m ∷ U
  ⊢⌜EntryTm⌝ = ⊢⌜IMu⌝ ⊢JT (⊢D⊢ (⊢tAt dq dm)) (⊢tmIx (⊢dep' ε) (⊢quoteCtx ◇) (⊢bodiesQ dq dm) (⊢typesQ dq dm))

  ⊢⌜EntryOK⌝ : Ξ ⊢ ⌜EntryOK⌝ q m ∷ U
  ⊢⌜EntryOK⌝ = ⊢⌜Σ⌝ ⊢⌜EntryTy⌝ (⊢wk {Ξ} {El (⌜EntryTy⌝ q m)} {⌜EntryTm⌝ q m} {U} ⊢⌜EntryTm⌝)

------------------------------------------------------------------------
-- 2. ★ THE WHOLE SIGNATURE: Spec's `WfUpTo`, literally — the entries below
--    `k`, each judged at its prefix, as an iterated Σ by recursion on `k`
--    (a `natrec` into `U`, as `Lib/DvdArith.nfam`)
------------------------------------------------------------------------

-- WfUpTo 𝒮 zero = ⊤ ;  WfUpTo 𝒮 (suc m) = WfUpTo 𝒮 m × EntryOK 𝒮 m m
⌜WfUpTo⌝ : RTm Δ → RTm Δ → RTm Δ
⌜WfUpTo⌝ q k = natrec ⌜Unit⌝ (⌜Σ⌝ (var vz) (renTm vs (⌜EntryOK⌝ (renTm vs (renTm vs q)) (var (vs vz))))) k

⌜WfK⌝ : RTm Δ → RTm Δ
⌜WfK⌝ q = ⌜WfUpTo⌝ q (sizeQ q)

⊢⌜WfUpTo⌝ : {Ξ : Ctx} {q k : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ k ∷ El ⌜Nat⌝ → Ξ ⊢ ⌜WfUpTo⌝ q k ∷ U
⊢⌜WfUpTo⌝ {Ξ} {q} dq dk = ⊢natrec ty-U ⊢⌜Unit⌝ stepᵁ (elAsNat dk)
  where
  Ξ₂ : Ctx
  Ξ₂ = (Ξ ▹ Nat) ▹ U
  E : RTm ⌊ Ξ₂ ⌋
  E = ⌜EntryOK⌝ (renTm vs (renTm vs q)) (var (vs vz))
  stepᵁ : Ξ₂ ⊢ ⌜Σ⌝ (var vz) (renTm vs E) ∷ U
  stepᵁ = ⊢⌜Σ⌝ (⊢var here) (⊢wk {Ξ₂} {El (var vz)} {E} {U} (⊢⌜EntryOK⌝ (wkQ (wkQ dq)) (natAsEl (⊢var (there here)))))

⊢⌜WfK⌝ : {Ξ : Ctx} {q : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ ⌜WfK⌝ q ∷ U
⊢⌜WfK⌝ dq = ⊢⌜WfUpTo⌝ dq (⊢sizeQ dq)
