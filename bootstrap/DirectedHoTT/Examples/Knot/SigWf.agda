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
--     ⌜EntryOK⌝ q m = ⌜⊢ty⌝ (q , m) ◇ (typesQ q m)  ×  ⌜⊢⌝ (q , m) ◇ (bodiesQ q m) (typesQ q m)
--     ⌜WfK⌝ q       = Π (m : Nat) → m + 1 ≤ sizeQ q → ⌜EntryOK⌝ q m
--
-- The Π form is Spec's own `EntriesOK` (`∀ {d} → d <ˢ n → EntryOK d`),
-- with the bound stated as the `Hom Nat` premise of the δ / ⊢ref rows
-- (`Knot/Ref`, `Knot/RefJudge`; decoded by `QuoteSig.homLt`).  No large
-- elimination is needed.
--
-- Faithfulness (`⌜WfK⌝ ⌜𝒮⌝` inhabited iff `WfK 𝒮`) needs the typing
-- agreement at every bound `m ≤ size`, not only at `size` (`t𝒮`): see
-- PLAN-REF 2026-10-12.
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
open import DirectedHoTT.Lib.NatCode 𝒮 (Defs.size 𝒮) using ( ⊢isuc )
open import DirectedHoTT.Examples.Knot.Terms 𝒮 wf using ( dep; ⊢dep' )
open import DirectedHoTT.Examples.Knot.Ctx 𝒮 wf using ( quoteCtx; ⊢quoteCtx )
open import DirectedHoTT.Examples.Knot.QSig 𝒮 wf using ( ⌜QSig⌝; ⌜TSig⌝; sizeQ; typesQ; bodiesQ; ⊢sizeQ; ⊢typesQ; ⊢bodiesQ; wkQ )
open import DirectedHoTT.Examples.Knot.JudgeIx 𝒮 wf using ( JT; ⊢JT; tyIx; tmIx; ⊢tyIx; ⊢tmIx )
open import DirectedHoTT.Examples.Knot.Judge 𝒮 wf core using ( D⊢; ⊢D⊢ )

private
  variable
    Δ : Cx

------------------------------------------------------------------------
-- 1. The typing parameter at a quoted signature and a bound
------------------------------------------------------------------------

tAt : RTm Δ → RTm Δ → RTm Δ
tAt q m = pair q m

⊢tAt : {Ξ : Ctx} {q m : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ m ∷ El ⌜Nat⌝ → Ξ ⊢ tAt q m ∷ El ⌜TSig⌝
⊢tAt dq dm = ⊢conv (⊢pair (ty-El ⊢⌜Nat⌝) dq dm) (csymᵀ (credᵀ (El-⌜Σ⌝ ⌜QSig⌝ ⌜Nat⌝)))

------------------------------------------------------------------------
-- 2. ★ ONE ENTRY, judged at its prefix
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
-- 3. ★ THE WHOLE SIGNATURE: every name below the size is a well-formed
--    entry (`WfK`, in Spec's `EntriesOK` form)
------------------------------------------------------------------------

⌜WfK⌝ : RTm Δ → RTm Δ
⌜WfK⌝ q = ⌜Π⌝ ⌜Nat⌝ (⌜Π⌝ (⌜Hom⌝ ⌜Nat⌝ (nsuc (var vz)) (sizeQ (renTm vs q)))
                        (⌜EntryOK⌝ (renTm vs (renTm vs q)) (var (vs vz))))

⊢⌜WfK⌝ : {Ξ : Ctx} {q : RTm ⌊ Ξ ⌋} → Ξ ⊢ q ∷ El ⌜QSig⌝ → Ξ ⊢ ⌜WfK⌝ q ∷ U
⊢⌜WfK⌝ {Ξ} {q} dq =
  ⊢⌜Π⌝ ⊢⌜Nat⌝ (⊢⌜Π⌝ (⊢⌜Hom⌝ ⊢⌜Nat⌝ (⊢isuc dm) (⊢sizeQ (wkQ dq)))
                    (⊢⌜EntryOK⌝ (wkQ (wkQ dq)) (⊢var (there here))))
  where
  dm : (Ξ ▹ El ⌜Nat⌝) ⊢ var vz ∷ El ⌜Nat⌝
  dm = ⊢var here
