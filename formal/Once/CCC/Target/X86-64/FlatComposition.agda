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

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label; once)
open import Once.Type using (FitsInReg; fits-int; fits-float)
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

------------------------------------------------------------------------
-- HeadView: per-instruction evidence that confines the constructor
-- enumeration to `headView`, so `find-label-pres` stays structural.
-- Either the head is `instr-ctrl (c-label m)` (compiles to a single
-- `label (once m)`) or its x86 block is label-free; in both cases we
-- record how flat `fl-go` reduces on the head.
------------------------------------------------------------------------
data HeadView (i : AbstractInstr) : Set where
  hv-clabel : (m : ℕ)
    → compile-abstract i ≡ label (once m) ∷ []
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-label-match (m ≡ᵇ tgt) rest tgt acc)
    → HeadView i
  hv-plain : has-label (compile-abstract i) ≡ false
    → (∀ rest tgt acc → fl-go (i ∷ rest) tgt acc ≡ fl-go rest tgt (suc acc))
    → HeadView i

reg-op-no-label : ∀ (op : RegOp) → has-label (compile-abstract (instr-reg-op op)) ≡ false
reg-op-no-label scratch-one = refl
reg-op-no-label scratch-zero = refl
reg-op-no-label scratch-dec = refl
reg-op-no-label scratch-load-count = refl
reg-op-no-label input2-zero = refl
reg-op-no-label input2-inc = refl

const-no-label : ∀ {A} (p : FitsInReg A) (v : _) → has-label (compile-abstract (instr-load-const p v)) ≡ false
const-no-label fits-int   v = refl
const-no-label fits-float v = refl

headView : ∀ (i : AbstractInstr) → HeadView i
headView mov-to-output = hv-plain refl (λ _ _ _ → refl)
headView mov-to-input = hv-plain refl (λ _ _ _ → refl)
headView mov-output-to-input2 = hv-plain refl (λ _ _ _ → refl)
headView mov-input2-to-output = hv-plain refl (λ _ _ _ → refl)
headView load-indirect = hv-plain refl (λ _ _ _ → refl)
headView load-indirect-suc = hv-plain refl (λ _ _ _ → refl)
headView store-indirect = hv-plain refl (λ _ _ _ → refl)
headView store-indirect-suc = hv-plain refl (λ _ _ _ → refl)
headView instr-pop-frame = hv-plain refl (λ _ _ _ → refl)
headView instr-call-closure = hv-plain refl (λ _ _ _ → refl)
headView instr-save-closure-reg = hv-plain refl (λ _ _ _ → refl)
headView (load-from-slot _) = hv-plain refl (λ _ _ _ → refl)
headView (store-at-slot _) = hv-plain refl (λ _ _ _ → refl)
headView (lea-slot _) = hv-plain refl (λ _ _ _ → refl)
headView (restore-input _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-alloc-stack _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-dealloc-stack _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-reclaim-to _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-push-frame _) = hv-plain refl (λ _ _ _ → refl)
headView (worklist-init _) = hv-plain refl (λ _ _ _ → refl)
headView (worklist-push _) = hv-plain refl (λ _ _ _ → refl)
headView (worklist-pop _) = hv-plain refl (λ _ _ _ → refl)
headView (worklist-check _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-load-code-addr _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-load-tag-lit _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-alloc-heap _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-loop _) = hv-plain refl (λ _ _ _ → refl)
headView (instr-sigop si) = hv-plain refl (λ _ _ _ → refl)
headView (instr-load-const p v) = hv-plain (const-no-label p v) (λ _ _ _ → refl)
headView (instr-case-on-tag f g) = hv-plain refl (λ _ _ _ → refl)
headView (instr-reg-op op) = hv-plain (reg-op-no-label op) (λ _ _ _ → refl)
headView (instr-ctrl (c-label m)) = hv-clabel m refl (λ _ _ _ → refl)
headView (instr-ctrl (c-jmp m)) = hv-plain refl (λ _ _ _ → refl)
headView (instr-ctrl (c-je m)) = hv-plain refl (λ _ _ _ → refl)
headView (instr-ctrl c-test-tag) = hv-plain refl (λ _ _ _ → refl)
headView (instr-ctrl c-test-scratch) = hv-plain refl (λ _ _ _ → refl)
