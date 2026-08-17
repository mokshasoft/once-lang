-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-32.FlatComposition
--
-- Plan 0.66 X2, x86-32's copy of x86-64's arch-specific composition surface.
--
-- Plan 0.32 Phase D (composition, Stage 1): the BLOCK-OFFSET machinery
-- for the abstract↔x86 plus-simulation. Each abstract instruction lowers
-- to a contiguous x86 BLOCK (1 instr for most, 2 for alloc-heap, …), so
-- the x86 pc is NOT the flat pc — it is `blk-off prog (flat-pc)`, the sum
-- of block lengths before it. This module proves the load-bearing
-- `find-label` preservation: a jump that lands at flat index `j` lands at
-- x86 index `blk-off prog j` in the compiled program. (Injective encodings
-- + a non-lockstep simulation — see the plus-simulation design.)
--
-- Plan 0.65 G1b: ALL OF THAT IS NOW ARCH-GENERIC and lives in
-- `…FlatCore.{HeadView,FlatComposition}`. What is left here is what only an
-- ISA can say — which instructions are labels (`is-label?`), that the scan
-- steps past the ones that are not (`skip-law`) and decides on the ones that
-- are (`label-hit` / `label-miss`), and how THIS emitter lowers each abstract
-- instruction (`headView`, 39 clauses). The correspondence gets the theorems
-- back by instantiation.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.Adequacy.ArchCorrectness.X86-32.FlatComposition (FS : FrameSemantics) where

open import Data.Nat using (ℕ; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label; once; thunk; _≡ᵇᴸ_)
open import Once.Type using (FitsInReg; fits-int; fits-float)
import Once.CCC.Target.X86-32.Semantics as X
import Once.CCC.Target.X86-32.Syntax as XS
open import Once.CCC.Target.X86-32.Syntax
  using ( Instr; Program
        ; mov; lea; add; sub; cmp; test; jmp; je; jne; call; call-sym
        ; ret; push; pop; nop; ud2; label; mov-code; jmp-l
        ; Operand; reg; imm; esp; slots)
open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-abstract; compile-trace)

------------------------------------------------------------------------
-- WHICH INSTRUCTIONS ARE LABELS, and the three scan equations that follow.
-- One `refl` per constructor: the case split is what makes
-- `X.find-label-go`'s catch-all reduce, and it is the enumeration this module
-- used to carry inside `find-label-go-skip`. Same evidence; it now lives where
-- the constructors do, and the correspondence gets a three-line induction.
------------------------------------------------------------------------
is-label? : XS.Instr → Bool
is-label? (label _) = true
is-label? (mov _ _) = false
is-label? (lea _ _) = false
is-label? (add _ _) = false
is-label? (sub _ _) = false
is-label? (cmp _ _) = false
is-label? (test _ _) = false
is-label? (jmp _) = false
is-label? (je _) = false
is-label? (jne _) = false
is-label? (call _) = false
is-label? (call-sym _) = false
is-label? ret = false
is-label? (push _) = false
is-label? (pop _) = false
is-label? nop = false
is-label? ud2 = false
is-label? (mov-code _ _) = false
is-label? (jmp-l _) = false

-- The scan steps past a non-label. One `refl` per constructor: the case split
-- is what makes `X.find-label-go`'s catch-all reduce.
skip-law : ∀ (t : Label) (i : XS.Instr) (rest : Program) (xi : ℕ)
         → is-label? i ≡ false
         → X.find-label-go t (i ∷ rest) xi ≡ X.find-label-go t rest (suc xi)
skip-law t (label _) rest xi ()
skip-law t (mov _ _) rest xi _ = refl
skip-law t (lea _ _) rest xi _ = refl
skip-law t (add _ _) rest xi _ = refl
skip-law t (sub _ _) rest xi _ = refl
skip-law t (cmp _ _) rest xi _ = refl
skip-law t (test _ _) rest xi _ = refl
skip-law t (jmp _) rest xi _ = refl
skip-law t (je _) rest xi _ = refl
skip-law t (jne _) rest xi _ = refl
skip-law t (call _) rest xi _ = refl
skip-law t (call-sym _) rest xi _ = refl
skip-law t ret rest xi _ = refl
skip-law t (push _) rest xi _ = refl
skip-law t (pop _) rest xi _ = refl
skip-law t nop rest xi _ = refl
skip-law t ud2 rest xi _ = refl
skip-law t (mov-code _ _) rest xi _ = refl
skip-law t (jmp-l _) rest xi _ = refl

-- The scan DECIDES on a label instruction, by `_≡ᵇᴸ_`. (`label-miss`
-- subsumes what Plan 0.63 called `find-label-go-skip-other`: a `thunk` label
-- against a `once` target, where the `false` is `_≡ᵇᴸ_`'s catch-all.)
label-hit : ∀ (ℓ t : Label) (rest : Program) (xi : ℕ)
          → (ℓ ≡ᵇᴸ t) ≡ true
          → X.find-label-go t (label ℓ ∷ rest) xi ≡ just xi
label-hit ℓ t rest xi eq rewrite eq = refl

label-miss : ∀ (ℓ t : Label) (rest : Program) (xi : ℕ)
           → (ℓ ≡ᵇᴸ t) ≡ false
           → X.find-label-go t (label ℓ ∷ rest) xi ≡ X.find-label-go t rest (suc xi)
label-miss ℓ t rest xi eq rewrite eq = refl

-- `has-label` and the `HeadView` datatype are generic; only the 39-clause
-- `headView` below is about this emitter.
open import Once.Adequacy.ArchCorrectness.FlatCore.HeadView
       FS XS.Instr compile-abstract is-label? label
  public

reg-op-no-label : ∀ (op : RegOp) → has-label (compile-abstract (instr-reg-op op)) ≡ false
reg-op-no-label scratch-one = refl
reg-op-no-label scratch-zero = refl
reg-op-no-label scratch-dec = refl
reg-op-no-label scratch-load-count = refl
reg-op-no-label count-zero = refl
reg-op-no-label count-inc = refl

const-no-label : ∀ {A} (p : FitsInReg A) (v : _) → has-label (compile-abstract (instr-load-const p v)) ≡ false
const-no-label fits-int   v = refl
const-no-label fits-float v = refl

headView : ∀ (i : AbstractInstr) → HeadView i
headView mov-to-output = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView mov-to-input = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView load-indirect = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView load-indirect-suc = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView store-indirect = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView store-indirect-suc = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView instr-pop-frame = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView instr-call-closure = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView instr-save-closure-reg = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (load-from-slot _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (store-at-slot _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (lea-slot _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (lea-indexed _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (restore-input _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-alloc-stack _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-dealloc-stack _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-reclaim-to _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-push-frame _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-init _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-push _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-pop _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (worklist-check _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-load-code-addr _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-load-tag-lit _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-alloc-heap _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-loop _) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-sigop si) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-load-const p v) = hv-plain (const-no-label p v) (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-case-on-tag f g) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-reg-op op) = hv-plain (reg-op-no-label op) (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-label m)) = hv-clabel m refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-thunk m b)) =
  hv-otherlabel m (sub (reg esp) (imm (slots b)) ∷ []) refl refl
                (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-ret b)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-jmp m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-branch-scratch-zero m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)
headView (instr-ctrl (c-branch-tag-zero m)) = hv-plain refl (λ _ _ _ → refl) (λ _ _ _ → refl)

------------------------------------------------------------------------
-- …and that is the whole arch-specific surface. The block-offset machinery,
-- the two scan-preservation theorems and their negative direction, and the
-- `fetch-block-*` family all come back by instantiating the core.
--
-- Note what x86-32 discharges with `refl`: `compile-trace`'s two defining
-- equations, all three `fetch` equations, and the empty scan — the same list
-- x86-64 and riscv64 discharge. The ISA surface that genuinely differs is
-- three lines: no `syscall`, and two constructors x86-64 does not have
-- (`mov-code`, `jmp-l`, both non-labels).
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition FS XS.Instr
       compile-abstract compile-trace refl (λ _ _ → refl)
       X.fetch (λ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl)
       is-label? label X.find-label-go (λ _ _ → refl) skip-law
       label-hit label-miss headView
  public
