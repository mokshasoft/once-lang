-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Examples.AbstractCataFoldInduction
--
-- Plan 0.30: the ABSTRACT-MACHINE analogue of `NatFoldLoopInduction`.
-- Where that proves the compiled x86 descend-loop folds EVERY heap-Nat
-- (∀-n, by induction over `Semantics.exec`'s fuel), this proves the same
-- for the abstract machine's `exec-loop` + branching `exec-case-dispatch`.
--
-- It is a genuine ∀-n correctness proof (not a concrete `refl`): the
-- abstract cata descend-loop counts the `suc`s of any heap-μ-value into
-- the `Input2` accumulator. The fuel here is `exec-loop`'s own fuel — the
-- same device that carries the x86 proof; "structured" just means the
-- loop stays a node so the fuel-induction applies directly.
--
-- Clean because — unlike the x86 CPU — `alloc`, `heapMem` and `stackMem`
-- are all INVARIANT through the descend loop (the body touches only
-- registers), so the loop state stays in the `st r` family keyed on the
-- register file alone.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Examples.AbstractCataFoldInduction
  (FS : FrameSemantics)
  where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.CCC.Machine.SMCore
open MemOps {FS}
open AbstractExec {FS}

------------------------------------------------------------------------
-- The descend-loop body (identical to IRToTrace's Cata clause).
------------------------------------------------------------------------

descend-body : AbstractTrace
descend-body =
  instr-case-on-tag
    (instr-reg-op scratch-zero ∷ [])
    (instr-reg-op input2-inc ∷ load-indirect-suc ∷ mov-to-input ∷ [])
  ∷ []

------------------------------------------------------------------------
-- Heap representation of a NatF μ-value: tagged nodes, child at sucHL.
--   zero  : h hl = Tag 0
--   suc n : h hl = Tag 1 ; h (sucHL hl) = Ptr child ; HeapNat child n
------------------------------------------------------------------------

data HeapNat (h : HeapMem FS) : HeapLocation → ℕ → Set where
  hz : ∀ {hl} → h hl ≡ just (SV-Tag 0) → HeapNat h hl 0
  hs : ∀ {hl child n}
     → h hl ≡ just (SV-Tag 1)
     → h (sucHL hl) ≡ just (SV-Ptr (AtDynamic child))
     → HeapNat h child n
     → HeapNat h hl (suc n)

------------------------------------------------------------------------
-- Fuel to fold a Nat of value n: one exec-loop step per suc, one for the
-- zero node (sets the break flag), one for the break check.
------------------------------------------------------------------------

needed : ℕ → ℕ
needed zero    = 2
needed (suc n) = suc (needed n)

module _ (h : HeapMem FS) (alloc : AllocState {FS}) where

  -- Loop state keyed on the register file (heap/stack/alloc invariant).
  st : Registers FS → LocState FS
  st r = mkLocState r (λ _ _ → nothing) h false

  -- Registers at a loop head: Input1 = node ptr, Input2 = Tag acc,
  -- Scratch = Tag 1 (active). Output/stackSlot are spectators.
  rg : HeapLocation → ℕ → StoredValue FS → ℕ → Registers FS
  rg hl acc out ss = mkRegs (SV-Ptr (AtDynamic hl)) (SV-Tag acc) out ss (SV-Tag 1)

  ------------------------------------------------------------------------
  -- One suc-iteration: exec-loop peels one fuel, bumping the accumulator
  -- and descending to the child. The two heap reads (tag, child) are the
  -- only neutrals; rewriting them lets exec-loop reduce by refl.
  ------------------------------------------------------------------------
  iter : ∀ (fuel : ℕ) (hl child : HeapLocation) (acc : ℕ) (out : StoredValue FS) (ss : ℕ)
       → h hl ≡ just (SV-Tag 1)
       → h (sucHL hl) ≡ just (SV-Ptr (AtDynamic child))
       → exec-loop (suc fuel) descend-body (st (rg hl acc out ss)) alloc
         ≡ exec-loop fuel descend-body (st (rg child (suc acc) (SV-Ptr (AtDynamic child)) ss)) alloc
  iter fuel hl child acc out ss tag-eq child-eq
    rewrite tag-eq | child-eq = refl

  ------------------------------------------------------------------------
  -- ∀-n: from a loop head over a HeapNat of value n with accumulator acc,
  -- the descend-loop terminates with Input2 = Tag (acc + n).
  ------------------------------------------------------------------------
  fold-correct : ∀ (n extra : ℕ) (hl : HeapLocation) (acc : ℕ) (out : StoredValue FS) (ss : ℕ)
               → HeapNat h hl n
               → input2 (regs (proj₁ (exec-loop (needed n + extra) descend-body (st (rg hl acc out ss)) alloc)))
                 ≡ SV-Tag (acc + n)
  -- zero: tag 0 → scratch-zero sets the break flag; next exec-loop breaks.
  fold-correct zero extra hl acc out ss (hz tag0-eq)
    rewrite tag0-eq | +-identityʳ acc = refl
  -- suc k: one iter bumps acc and descends; IH folds the child.
  fold-correct (suc k) extra hl acc out ss (hs tag-eq child-eq hchild) =
    trans (cong (λ s → input2 (regs (proj₁ s)))
                (iter (needed k + extra) hl _ acc out ss tag-eq child-eq))
          (trans (fold-correct k extra _ (suc acc) (SV-Ptr (AtDynamic _)) ss hchild)
                 (cong SV-Tag (sym (+-suc acc k))))

  ------------------------------------------------------------------------
  -- Corollary: from a clean accumulator (Input2 = Tag 0), the loop yields
  -- exactly the μ-value's depth n.
  ------------------------------------------------------------------------
  fold-clean : ∀ (n extra : ℕ) (hl : HeapLocation) (out : StoredValue FS) (ss : ℕ)
             → HeapNat h hl n
             → input2 (regs (proj₁ (exec-loop (needed n + extra) descend-body (st (rg hl 0 out ss)) alloc)))
               ≡ SV-Tag n
  fold-clean n extra hl out ss hn = fold-correct n extra hl 0 out ss hn
