-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Target.X86-32.FileSymbols — plan 0.107 phase d, layer 1: THE LOWERING IS
-- SYMBOL-FAITHFUL. The symbols the lowered program defines and references are
-- exactly the abstract image's (`Once.CCC.Codegen.ImageSymbols`): one clause
-- per abstract instruction, each `refl` — its lowering is a concrete list, so
-- the file's symbol walk computes through it.
------------------------------------------------------------------------

module Once.CCC.Target.X86-32.FileSymbols where

import Data.Nat
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Once.Type using (fits-int; fits-float)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; instr-refs; adefs; arefs; part-refs; stack-refs)
open import Once.CCC.Target.X86-32.AbstractToX86-32 using (compile-abstract; compile-trace; fits-or-out; room-code; room-fits?; start-tail; part; heap-room; stack-room; heap-code; stack-code; room-code′; lower-code; lower-pick)
open import Data.List.Properties using (++-assoc)
open import Data.Bool using (Bool; true; false)
open import Once.Target.SymbolFresh using (host-exhausted-symbol; alloc-record-symbol)
open import Once.CCC.Target.X86-32.File using (label-defs; refs)
open import Once.CCC.Target.X86-32.Syntax using (Program)

-- D488: a check is its code or its call; both define nothing and reference `once_exhausted`
-- (`T`: what follows it in the instruction's block)
private
  fo-defs : ∀ (c : Bool) (k : Data.Nat.ℕ) (T r : Program)
          → label-defs ((fits-or-out c (room-code k) ++ T) ++ r) ≡ label-defs (T ++ r)
  fo-defs true  k T r = refl
  fo-defs false k T r = refl
  fo-refs : ∀ (c : Bool) (k : Data.Nat.ℕ) (T r : Program)
          → refs ((fits-or-out c (room-code k) ++ T) ++ r) ≡ host-exhausted-symbol ∷ refs (T ++ r)
  fo-refs true  k T r = refl
  fo-refs false k T r = refl
  fo-defs₁ : ∀ (c : Bool) (k : Data.Nat.ℕ) (r : Program)
           → label-defs (fits-or-out c (room-code k) ++ r) ≡ label-defs r
  fo-defs₁ true  k r = refl
  fo-defs₁ false k r = refl
  fo-refs₁ : ∀ (c : Bool) (k : Data.Nat.ℕ) (r : Program)
           → refs (fits-or-out c (room-code k) ++ r) ≡ host-exhausted-symbol ∷ refs r
  fo-refs₁ true  k r = refl
  fo-refs₁ false k r = refl

-- D488 (a3): a check's two parts define nothing; each reads the record, then may call
private
  pdefs : ∀ (c : Bool) (code r : Program) → label-defs (code ++ r) ≡ label-defs r → label-defs (part c code ++ r) ≡ label-defs r
  pdefs true  code r e = e
  pdefs false code r e = refl
  prefs : ∀ (c : Bool) (code r : Program) → refs (code ++ r) ≡ alloc-record-symbol ∷ host-exhausted-symbol ∷ refs r
        → refs (part c code ++ r) ≡ alloc-record-symbol ∷ host-exhausted-symbol ∷ refs r
  prefs true  code r e = e
  prefs false code r e = refl
  hc-defs : ∀ (h : Data.Nat.ℕ) (r : Program) → label-defs (heap-code h ++ r) ≡ label-defs r
  hc-defs Data.Nat.zero      r = refl
  hc-defs h@(Data.Nat.suc _) r = pdefs (room-fits? h) (heap-room h) r refl
  sc-defs : ∀ (k : Data.Nat.ℕ) (r : Program) → label-defs (stack-code k ++ r) ≡ label-defs r
  sc-defs Data.Nat.zero      r = refl
  sc-defs k@(Data.Nat.suc _) r = pdefs (room-fits? k) (stack-room k) r refl
  hc-refs : ∀ (h : Data.Nat.ℕ) (r : Program) → refs (heap-code h ++ r) ≡ part-refs h ++ refs r
  hc-refs Data.Nat.zero      r = refl
  hc-refs h@(Data.Nat.suc _) r = prefs (room-fits? h) (heap-room h) r refl
  sc-refs : ∀ (k : Data.Nat.ℕ) (r : Program) → refs (stack-code k ++ r) ≡ part-refs k ++ refs r
  sc-refs Data.Nat.zero      r = refl
  sc-refs k@(Data.Nat.suc _) r = prefs (room-fits? k) (stack-room k) r refl
  -- D491: the limit's part, in either form, defines no label and names the record, then
  -- `once_exhausted`, then the record
  lp-defs : ∀ (c : Bool) (h k : Data.Nat.ℕ) (r : Program) → label-defs (lower-pick c h k ++ r) ≡ label-defs r
  lp-defs true  h k r = fo-defs (room-fits? (h Data.Nat.+ k)) (h Data.Nat.+ k) _ r
  lp-defs false h k r = refl
  lp-refs : ∀ (c : Bool) (h k : Data.Nat.ℕ) (r : Program)
          → refs (lower-pick c h k ++ r) ≡ alloc-record-symbol ∷ host-exhausted-symbol ∷ alloc-record-symbol ∷ refs r
  lp-refs true  h k r = cong (alloc-record-symbol ∷_) (fo-refs (room-fits? (h Data.Nat.+ k)) (h Data.Nat.+ k) _ r)
  lp-refs false h k r = refl
  room-defs : ∀ (h k : Data.Nat.ℕ) (r : Program) → label-defs (room-code′ h k ++ r) ≡ label-defs r
  room-defs h Data.Nat.zero      r = hc-defs h r
  room-defs h k@(Data.Nat.suc _) r =
    trans (cong label-defs (++-assoc (lower-code h k) (heap-code h) r))
          (trans (lp-defs (room-fits? k) h k (heap-code h ++ r)) (hc-defs h r))
  room-refs : ∀ (h k : Data.Nat.ℕ) (r : Program)
            → refs (room-code′ h k ++ r) ≡ (stack-refs k ++ part-refs h) ++ refs r
  room-refs h Data.Nat.zero      r = hc-refs h r
  room-refs h k@(Data.Nat.suc _) r =
    trans (cong refs (++-assoc (lower-code h k) (heap-code h) r))
          (trans (lp-refs (room-fits? k) h k (heap-code h ++ r))
                 (cong (λ x → alloc-record-symbol ∷ host-exhausted-symbol ∷ alloc-record-symbol ∷ x) (hc-refs h r)))

defs-step : ∀ (i : AbstractInstr) (r : Program)
          → label-defs (compile-abstract i ++ r) ≡ instr-defs i ++ label-defs r
defs-step mov-to-output r = refl
defs-step mov-to-input r = refl
defs-step load-indirect r = refl
defs-step load-indirect-suc r = refl
defs-step (load-from-slot s) r = refl
defs-step (store-at-slot s) r = refl
defs-step store-indirect r = refl
defs-step store-indirect-suc r = refl
defs-step (lea-slot s) r = refl
defs-step (restore-input s) r = refl
defs-step (instr-alloc-stack k) r = refl
defs-step (instr-dealloc-stack k) r = refl
defs-step (instr-reclaim-to k) r = refl
defs-step (instr-free-heap k) r = refl
defs-step (load-at k) r = refl
defs-step (store-at k) r = refl
defs-step (addr-at k) r = refl
defs-step (load-rec k) r = refl
defs-step (store-rec k) r = refl
defs-step (instr-room q) r = room-defs (Room.room-h q) (Room.room-s q) r
defs-step (instr-push-frame k) r = refl
defs-step instr-pop-frame r = refl
defs-step instr-call-closure r = refl
defs-step (worklist-init s) r = refl
defs-step (worklist-push s) r = refl
defs-step (worklist-pop s) r = refl
defs-step (worklist-check s) r = refl
defs-step (instr-sigop si) r = refl
defs-step (instr-load-const fits-int v) r = refl
defs-step (instr-load-const fits-float v) r = refl
defs-step (instr-load-code-addr n) r = refl
defs-step instr-save-closure-reg r = refl
defs-step (instr-load-tag-lit k) r = refl
defs-step (instr-alloc-heap k) r = refl
defs-step (instr-reg-op out-nz) r = refl
defs-step (instr-ctrl (c-label n)) r = refl
defs-step (instr-ctrl (c-jmp n)) r = refl
defs-step (instr-ctrl (c-branch-tag-zero n)) r = refl
defs-step (instr-ctrl (c-entry e b)) r = refl
defs-step (instr-ctrl (c-ret b)) r = refl
defs-step (instr-ctrl (c-call-fn f)) r = refl
defs-step (instr-ctrl (c-start b)) r = fo-defs (room-fits? (start-stack-words Data.Nat.+ b)) (start-stack-words Data.Nat.+ b) (start-tail b) r
defs-step (instr-ctrl c-leave) r = refl

refs-step : ∀ (i : AbstractInstr) (r : Program)
          → refs (compile-abstract i ++ r) ≡ instr-refs i ++ refs r
refs-step mov-to-output r = refl
refs-step mov-to-input r = refl
refs-step load-indirect r = refl
refs-step load-indirect-suc r = refl
refs-step (load-from-slot s) r = refl
refs-step (store-at-slot s) r = refl
refs-step store-indirect r = refl
refs-step store-indirect-suc r = refl
refs-step (lea-slot s) r = refl
refs-step (restore-input s) r = refl
refs-step (instr-alloc-stack k) r = refl
refs-step (instr-dealloc-stack k) r = refl
refs-step (instr-reclaim-to k) r = refl
refs-step (instr-free-heap k) r = refl
refs-step (load-at k) r = refl
refs-step (store-at k) r = refl
refs-step (addr-at k) r = refl
refs-step (load-rec k) r = refl
refs-step (store-rec k) r = refl
refs-step (instr-room q) r = room-refs (Room.room-h q) (Room.room-s q) r
refs-step (instr-push-frame k) r = refl
refs-step instr-pop-frame r = refl
refs-step instr-call-closure r = refl
refs-step (worklist-init s) r = refl
refs-step (worklist-push s) r = refl
refs-step (worklist-pop s) r = refl
refs-step (worklist-check s) r = refl
refs-step (instr-sigop si) r = refl
refs-step (instr-load-const fits-int v) r = refl
refs-step (instr-load-const fits-float v) r = refl
refs-step (instr-load-code-addr n) r = refl
refs-step instr-save-closure-reg r = refl
refs-step (instr-load-tag-lit k) r = refl
refs-step (instr-alloc-heap k) r = refl
refs-step (instr-reg-op out-nz) r = refl
refs-step (instr-ctrl (c-label n)) r = refl
refs-step (instr-ctrl (c-jmp n)) r = refl
refs-step (instr-ctrl (c-branch-tag-zero n)) r = refl
refs-step (instr-ctrl (c-entry e b)) r = refl
refs-step (instr-ctrl (c-ret b)) r = refl
refs-step (instr-ctrl (c-call-fn f)) r = refl
refs-step (instr-ctrl (c-start b)) r = fo-refs (room-fits? (start-stack-words Data.Nat.+ b)) (start-stack-words Data.Nat.+ b) (start-tail b) r
refs-step (instr-ctrl c-leave) r = refl

defs-lower : ∀ (t : AbstractTrace) → label-defs (compile-trace t) ≡ adefs t
defs-lower []       = refl
defs-lower (i ∷ is) = trans (defs-step i (compile-trace is)) (cong (instr-defs i ++_) (defs-lower is))

refs-lower : ∀ (t : AbstractTrace) → refs (compile-trace t) ≡ arefs t
refs-lower []       = refl
refs-lower (i ∷ is) = trans (refs-step i (compile-trace is)) (cong (instr-refs i ++_) (refs-lower is))
