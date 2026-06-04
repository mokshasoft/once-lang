-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FlatComposition
--
-- Plan 0.32 Phase D (composition, Stage 1): the BLOCK-OFFSET machinery
-- for the abstract↔x86 plus-simulation. Each abstract instruction lowers
-- to a contiguous x86 BLOCK (1 instr for most, 2 for alloc-heap, …), so
-- the x86 pc is NOT the flat pc — it is `x86-off prog (flat-pc)`, the sum
-- of block lengths before it. This module proves the load-bearing
-- `find-label` preservation: a jump that lands at flat index `j` lands at
-- x86 index `x86-off prog j` in the compiled program. (Injective encodings
-- + a non-lockstep simulation — see the plus-simulation design.)
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Target.X86-64.FlatComposition (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; instr-ctrl; c-label)
open import Once.CCC.Label using (Label)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X
open import Once.CCC.Target.X86-64.Syntax
  using ( Instr; Program
        ; mov; lea; add; sub; cmp; test; jmp; je; jne; call; call-sym
        ; ret; push; pop; nop; ud2; syscall; label)
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-abstract; compile-trace)

------------------------------------------------------------------------
-- Block lengths and the cumulative x86 offset of a flat pc.
------------------------------------------------------------------------
x86-len : AbstractInstr → ℕ
x86-len i = length (compile-abstract i)

-- x86-off prog j = number of x86 instructions before flat index j.
x86-off : AbstractTrace → ℕ → ℕ
x86-off _        zero    = zero
x86-off []       (suc _) = zero
x86-off (i ∷ is) (suc j) = x86-len i + x86-off is j

------------------------------------------------------------------------
-- A label-free x86 block: find-label scans past it, advancing the index
-- by the block length, without matching.
------------------------------------------------------------------------
has-label : Program → Bool
has-label []            = false
has-label (label _ ∷ _) = true
has-label (_ ∷ is)      = has-label is

find-label-go-skip : ∀ (target : Label) (block rest : Program) (xi : ℕ)
  → has-label block ≡ false
  → X.find-label-go target (block ++ rest) xi ≡ X.find-label-go target rest (xi + length block)
find-label-go-skip target []             rest xi _  =
  cong (X.find-label-go target rest) (sym (+-identityʳ xi))
find-label-go-skip target (label _ ∷ bs) rest xi ()
find-label-go-skip target (mov _ _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (lea _ _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (add _ _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (sub _ _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (cmp _ _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (test _ _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (jmp _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (je _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (jne _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (call _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (call-sym _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (ret ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (push _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (pop _ ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (nop ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (ud2 ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
find-label-go-skip target (syscall ∷ bs) rest xi nl =
  trans (find-label-go-skip target bs rest (suc xi) nl)
        (cong (X.find-label-go target rest) (sym (+-suc xi (length bs))))
