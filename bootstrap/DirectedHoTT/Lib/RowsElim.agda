-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · Lib — a ROW-BY-ROW DISPATCH, without a pattern lambda
-- (PLAN-FAITHFUL F6, the decoders' cost).
--
-- `rows-dec` returns which row of a (concrete) row list an inhabitant is,
-- as an `Nth` proof.  A decoder used to dispatch with
-- `▷ λ { (… nth-z …) → h₀ … ; (… nth-s nth-z …) → h₁ … ; … }`; that lambda
-- is lifted and coverage-checked at every head — measured ~1 s per row in
-- RedDecode (2026-10-04).  Here: one HANDLER per row, the matching one
-- picked by recursion on the `Nth` proof — half the cost.
--
-- `--safe`, ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
open import DirectedHoTT.Spec.Syntax using ( Defs; _<ˢ_; _<ˢ?_ )
open import DirectedHoTT.Spec.SigWf using ( WfK )
import DirectedHoTT.Metatheory.Entries as Entries
module DirectedHoTT.Lib.RowsElim (𝒮 : Defs) (wf : WfK 𝒮) where

-- ★ PLAN-REF: at a well-formed signature, all its names
private
  n = Defs.size 𝒮
  ok = Entries.sigOK 𝒮 n wf
  refs = Entries.refsOK 𝒮 n (λ p → p) wf


open import normalizer.Syntax.Types using ( Σ; _,_; _×_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Unit using ( ⊤ )

-- the empty handler list (re-exported for the generated dispatchers)
open import Agda.Builtin.Unit public using ( tt )
open import DirectedHoTT.Spec.Syntax hiding ( Fin )
open import DirectedHoTT.Spec.Typing 𝒮 n hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.LogicalRelation 𝒮 using ( IsNormal )
open import DirectedHoTT.Lib.Sugar 𝒮 n ok using ( Cons; []; _∷_; Nth; nth-z; nth-s )
open import DirectedHoTT.Lib.Decode 𝒮 wf using ( RowsDec )
open import DirectedHoTT.Lib.Size 𝒮 wf using ( _<_; <ᶜ )
open import DirectedHoTT.Metatheory.Canonicity 𝒮 wf using ( sz; _≤_ )

-- one handler per row of the list
Handlers : (I D : RTm ε) {m : ℕ} → Cons ε m → Set → Set
Handlers I D []       R = ⊤
Handlers I D (C ∷ Cs) R = ({q : RTm ε} → ◇ ⊢ q ∷ El (dpay I D C) → IsNormal q → R) × Handlers I D Cs R

nth-elim : {I D C q : RTm ε} {m k : ℕ} {Cs : Cons ε m} {R : Set} →
           Nth Cs k C → ◇ ⊢ q ∷ El (dpay I D C) → IsNormal q → Handlers I D Cs R → R
nth-elim nth-z      dq nq (h , hs) = h dq nq
nth-elim (nth-s nt) dq nq (h , hs) = nth-elim nt dq nq hs

-- ★ the dispatch: the row `rows-dec` found, handled by its handler
rows-elim : {I D x : RTm ε} {m : ℕ} {Cs : Cons ε m} {R : Set} → RowsDec I D Cs x → Handlers I D Cs R → R
rows-elim (k , (C , (q , (nt , (e , (dq , nq)))))) hs = nth-elim nt dq nq hs

-- …and the same, each handler given its payload's size bound: a decoder that
--   recurses on the inhabitant's size (`JudgeDecode`)
Handlers< : ℕ → (I D : RTm ε) {m : ℕ} → Cons ε m → Set → Set
Handlers< N I D []       R = ⊤
Handlers< N I D (C ∷ Cs) R = ({q : RTm ε} → sz q < N → ◇ ⊢ q ∷ El (dpay I D C) → IsNormal q → R) × Handlers< N I D Cs R

nth-elim< : {N : ℕ} {I D C q : RTm ε} {m k : ℕ} {Cs : Cons ε m} {R : Set} →
            Nth Cs k C → sz q < N → ◇ ⊢ q ∷ El (dpay I D C) → IsNormal q → Handlers< N I D Cs R → R
nth-elim< nth-z      h dq nq (f , fs) = f h dq nq
nth-elim< (nth-s nt) h dq nq (f , fs) = nth-elim< nt h dq nq fs

rows-elim< : {N : ℕ} {I D x : RTm ε} {m : ℕ} {Cs : Cons ε m} {R : Set} →
             RowsDec I D Cs x → sz x ≤ N → Handlers< N I D Cs R → R
rows-elim< (k , (C , (q , (nt , (e , (dq , nq)))))) h hs = nth-elim< nt (<ᶜ e h) dq nq hs
