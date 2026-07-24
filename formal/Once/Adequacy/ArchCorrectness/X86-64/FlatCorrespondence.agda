-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence
--
-- Plan 0.32 M3 Phase D: the value-encoding correspondence between the
-- FLAT abstract machine (`exec-flat`, typed StoredValue) and the x86-64
-- `Semantics.State` (untyped Word). Because both machines are now FLAT
-- (same pc/jump/fuel control), the correspondence is a 1-to-1 register
-- relabel + a uniform `StoredValue → Word` value encoding — no
-- structured↔flat bridge.
--
-- This is the relation the real-path correctness proof carries through
-- execution (per-instruction simulation + fuel induction land on top in
-- the continuation). It is parameterised over the heap-address layout
-- `enc-hl : HeapLocation → Word` so the relation is independent of the
-- concrete bump-allocator addressing (the layout's successor law is added
-- when the indirect-load instructions need it).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)   -- heap-address layout (Word = ℕ)
  -- CompCert-style MEMORY INJECTION: `enc-hl` is injective ONLY on LIVE cells
  -- (`LiveIn as hl` = hl is an in-bounds slot of a block allocated in state `as`).
  -- This is the sound premise the ALLOCATOR INTERFACE supplies (`blocks-disjoint`
  -- on live blocks) — a GLOBAL injection over `HeapOffset = ℕ` is unsatisfiable
  -- (would prove ⊥). `store-heap-eq` compares only live cells, so distinctness is
  -- purely this live-injection; dead cells carry no correspondence.
  (LiveIn : AllocState {FS} → HeapLocation → Set)
  (enc-hl-inj-live : ∀ (as : AllocState {FS}) {a b : HeapLocation}
                   → LiveIn as a → LiveIn as b → enc-hl a ≡ enc-hl b → a ≡ b)
  where

open import Data.Nat using (zero; suc; _+_; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.List using ([])
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)

import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; mkflags; _<ᵇ_; writeMem)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (rax; rbx; rsi; rdi; rsp)
open import Once.CCC.Target.X86-64.AbstractToX86 using (slot-to-disp)
open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeHeapMem)
open ExecFinal {FS} using (exec-load-via-resolved; exec-load-suc-via-resolved; exec-load-with-value
                          ; exec-store-via-resolved; exec-store-suc-via-resolved)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open AbstractExec {FS} using (exec-abstract; exec-load-from-slot-with-value)

------------------------------------------------------------------------
-- Value encoding: typed StoredValue → untyped x86 Word.
--   SV-Tag n        → n              (sum/loop-flag/depth tags)
--   SV-Ptr (heap hl)→ enc-hl hl      (heap pointers — the cata's cursors)
-- The non-cata shapes (stack pointers, primitive literals, code addrs)
-- get placeholder encodings for now — they don't occur in cata traces;
-- a faithful primitive-literal encoding is future work (Phase D'').
------------------------------------------------------------------------
enc-sv : StoredValue FS → X.Word
enc-sv (SV-Tag n)               = n
enc-sv (SV-Ptr (AtDynamic hl))  = enc-hl hl
enc-sv (SV-Ptr (AtStack _ _))   = 0
enc-sv (SV-Lit _ _)             = 0
enc-sv (SV-Code n)              = n

enc-maybe : Maybe (StoredValue FS) → Maybe X.Word
enc-maybe (just v) = just (enc-sv v)
enc-maybe nothing  = nothing

------------------------------------------------------------------------
-- The correspondence: a FlatState and an x86 State agree on the four
-- abstract registers (under enc-sv), the pc, the zero-flag, the halt
-- flag, the heap memory (under enc-hl + enc-sv), and the CURRENT-FRAME
-- stack memory (rsp-relative, under enc-sv).
--
-- `stack-eq`: the current frame's slot `k` lives at x86 address
-- `rsp + slot-to-disp k` (the `%rsp`-relative frameless layout the
-- compiler emits — `AbstractToX86`), and holds the same value as the
-- abstract `stackMem (current-frame) k` under `enc-sv`. Only the current
-- frame is related (rsp points at its base); older frames sit at higher
-- addresses and are re-synced across push/pop-frame. This unlocks the
-- slot/frame/worklist cluster (load/store-at-slot, restore-input, …).
------------------------------------------------------------------------
record FlatCorr (fs : FlatState) (s : X.State) : Set where
  field
    rdi-eq  : X.readReg (X.State.regs s) rdi ≡ enc-sv (readReg (regs (floc fs)) Input1)
    rsi-eq  : X.readReg (X.State.regs s) rsi ≡ enc-sv (readReg (regs (floc fs)) Input2)
    rax-eq  : X.readReg (X.State.regs s) rax ≡ enc-sv (readReg (regs (floc fs)) Output)
    rbx-eq  : X.readReg (X.State.regs s) rbx ≡ enc-sv (readReg (regs (floc fs)) Scratch)
    halt-eq : X.State.halted s ≡ halted (floc fs)
    heap-eq : ∀ (hl : HeapLocation) → LiveIn (falloc fs) hl →
              X.readMem (X.State.memory s) (enc-hl hl) ≡ enc-maybe (heapMem (floc fs) hl)
    stack-eq : ∀ (k : Slot) →
              X.readMem (X.State.memory s) (X.readReg (X.State.regs s) rsp + slot-to-disp k)
              ≡ enc-maybe (stackMem (floc fs) (current-frame (falloc fs)) k)
open FlatCorr public

------------------------------------------------------------------------
-- Per-instruction simulation (Plan 0.32 M3 Phase D). Each lemma: one
-- exec-flat step on `i` corresponds to running compile-abstract i on the
-- x86 state, preserving FlatCorr. Because both machines are flat, the
-- value encoding is preserved field-by-field. (1-to-1 instructions;
-- multi-x86 `alloc-heap` + the jump pc-offset are the continuation.)
--
-- First: mov-to-output (Output := Input1) ↔ `mov rax, rdi`.
-- new rax (= old rdi) corresponds to new Output (= old Input1), so
-- rax-eq is exactly the old rdi-eq.
------------------------------------------------------------------------
sim-mov-to-output : ∀ (fs : FlatState) (s : X.State)
  → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rdi))
                      (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-output fs s corr = record
  { rdi-eq  = rdi-eq corr
  ; rax-eq  = rdi-eq corr
  ; rsi-eq  = rsi-eq corr
  ; rbx-eq  = rbx-eq corr
  ; halt-eq = halt-eq corr
  ; heap-eq = heap-eq corr
  ; stack-eq = stack-eq corr
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-to-input [] fs)
             (mkstate (xwriteReg (xregs s) rdi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-input fs s corr = record
  { rdi-eq = rax-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- mov-input2-to-output (Output := Input2) ↔ `mov rax, rsi`.
sim-mov-input2-to-output : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-input2-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-input2-to-output fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rsi-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- mov-output-to-input2 (Input2 := Output) ↔ `mov rsi, rax`.
sim-mov-output-to-input2 : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-output-to-input2 [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-output-to-input2 fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rax-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n ⟹ rax-eq=refl.
sim-load-tag-lit : ∀ (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-load-tag-lit n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-tag-lit n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`. rbx-eq=refl.
sim-reg-scratch-one : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-one) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 1) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-one fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`. rbx-eq=refl.
sim-reg-scratch-zero : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-zero fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op input2-zero (Input2 := SV-Tag 0) ↔ `mov rsi, 0`. rsi-eq=refl.
sim-reg-input2-zero : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op input2-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rsi 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-input2-zero fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = refl ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-load-count (Scratch := Input2) ↔ `mov rbx, rsi`. rbx-eq=rsi-eq.
sim-reg-scratch-load-count : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-load-count) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-load-count fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rsi-eq corr
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Boolean bridge for the conditional-branch correspondence (Plan 0.34):
-- the typed `sv-is-zero (SV-Tag n)` and the untyped `n ≡ᵇ 0` agree.
-- (sim-test-scratch / sim-test-tag retired — c-test-*/c-je folded into the
-- single c-branch-* instruction; the branch correspondence is built in the
-- Stage-2 block-step. sv-tag-zero / enc-zero retained for reuse there.)
------------------------------------------------------------------------
sv-tag-zero : ∀ (n : ℕ) → sv-is-zero (SV-Tag {FS} n) ≡ (n ≡ᵇ 0)
sv-tag-zero zero    = refl
sv-tag-zero (suc _) = refl

enc-zero : ∀ (v : StoredValue FS) (n : ℕ) → v ≡ SV-Tag n → (enc-sv v ≡ᵇ 0) ≡ sv-is-zero v
enc-zero .(SV-Tag n) n refl = sym (sv-tag-zero n)

------------------------------------------------------------------------
-- Heap load: load-indirect-suc (Output := *(sucLoc Input1)) ↔
-- `mov rax, [rdi + slot-size]`. Hypotheses (cata cursor + live child
-- cell): Input1 = SV-Ptr (AtDynamic hl),  heapMem (sucHL hl) = just w.
-- The x86 ADDRESS law (enc-hl (sucHL hl) = enc-hl hl + slot-size) is a
-- separate concern (proving execInstr REACHES this post-state); here we
-- relate the read VALUES: new rax = enc-sv w = enc-sv (new Output).
------------------------------------------------------------------------
sim-load-indirect-suc : ∀ (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → FlatCorr (flat-exec-instr load-indirect-suc [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-suc hl w fs s corr i-eq h-eq =
  subst (λ z → FlatCorr z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    -- cong/trans (not rewrite) so the `readReg _ Input1 → input1` and
    -- `heapMem` reductions go through definitionally.
    floc-eq : exec-load-suc-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-suc-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) h-eq)
    reduces : flat-exec-instr load-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Heap load (no offset): load-indirect (Output := *Input1) ↔
-- `mov rax, [rdi]`. Sibling of load-indirect-suc; reads the cell Input1
-- points to directly. Same reduce-then-correspond structure.
------------------------------------------------------------------------
sim-load-indirect : ∀ (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) hl ≡ just w
  → FlatCorr (flat-exec-instr load-indirect [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect hl w fs s corr i-eq h-eq =
  subst (λ z → FlatCorr z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-load-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) h-eq)
    reduces : flat-exec-instr load-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- STACK LOAD: `load-from-slot slot` (Output := stack[current-frame, slot]) ↔
-- `mov rax, [rsp + slot-to-disp slot]`. The read VALUE comes from `stack-eq`
-- (memory s at rsp+disp = enc-maybe of the slot's abstract value); the x86 post
-- is identical in shape to `sim-load-indirect` (rax := enc-sv w). Only the
-- SUCCESS case (slot holds `just w`) — the empty-slot (`nothing`→halt) case is
-- routed as a WF residual, exactly like load-indirect's bad case. This is the
-- FIRST consumer of the new `stack-eq` field (via block-step-load-from-slot).
------------------------------------------------------------------------
sim-load-from-slot : ∀ (slot : Slot) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → FlatCorr (flat-exec-instr (load-from-slot slot) [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-from-slot slot w fs s corr st-eq =
  subst (λ z → FlatCorr z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    ex-eq : exec-abstract (load-from-slot slot) (floc fs) (falloc fs)
            ≡ (record (floc fs) { regs = writeReg (regs (floc fs)) Output w } , falloc fs)
    ex-eq = cong (λ mv → exec-load-from-slot-with-value mv (floc fs) (falloc fs)) st-eq
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    reduces : flat-exec-instr (load-from-slot slot) [] fs ≡ cleanFlat
    reduces = cong (λ p → record fs { floc = proj₁ p ; falloc = proj₂ p ; fpc = suc (fpc fs) }) ex-eq
    corr-clean : FlatCorr cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Heap STORES (Plan 0.32 Phase D). A heap write ↔ x86 `mov [addr], reg`.
-- The crux: relate the typed heap update `writeHeapMem` (decides cells by
-- ≟HL) to the x86 memory update `writeMem` (decides addresses by ≡ᵇ).
-- They agree because enc-hl is INJECTIVE (the memory injection).
------------------------------------------------------------------------
≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≢→≡ᵇfalse : ∀ {m n : ℕ} → (m ≡ n → ⊥) → (m ≡ᵇ n) ≡ false
≢→≡ᵇfalse {zero}  {zero}  ¬p = ⊥-elim (¬p refl)
≢→≡ᵇfalse {zero}  {suc n} _  = refl
≢→≡ᵇfalse {suc m} {zero}  _  = refl
≢→≡ᵇfalse {suc m} {suc n} ¬p = ≢→≡ᵇfalse {m} {n} (λ p → ¬p (cong suc p))

-- The store correspondence: writing `v` at heap cell `hl` (x86: enc-hl hl)
-- preserves the heap agreement at every other cell, and installs enc-sv v
-- at `hl`. Case-split on ≟HL; enc-hl-inj turns cell-distinctness into
-- address-distinctness so the x86 `≡ᵇ` test resolves the same way.
-- store-heap-eq now works over LIVE cells only: the write target `hl` is live,
-- and the correspondence + result quantify over live `hl'`. Distinctness for the
-- no-alias case is `enc-hl-inj-live` (the allocator's `blocks-disjoint` on live
-- blocks) — dead cells are never compared.
store-heap-eq : ∀ (as : AllocState {FS}) (hl : HeapLocation) (v : StoredValue FS) (s : X.State) (ls : LocState FS)
  → LiveIn as hl
  → (∀ hl' → LiveIn as hl' → X.readMem (memory s) (enc-hl hl') ≡ enc-maybe (heapMem ls hl'))
  → ∀ hl' → LiveIn as hl' → X.readMem (writeMem (memory s) (enc-hl hl) (enc-sv v)) (enc-hl hl')
            ≡ enc-maybe (writeHeapMem (heapMem ls) hl v hl')
-- (writeHeapMem is with-free now, so the `with hl ≟HL hl'` below reduces
-- it directly — no read-after-write accessor lemmas needed.)
store-heap-eq as hl v s ls live-hl pre hl' live-hl' with hl ≟HL hl'
... | yes refl rewrite ≡ᵇ-refl (enc-hl hl) = refl
... | no ¬p rewrite ≢→≡ᵇfalse {enc-hl hl'} {enc-hl hl}
      (λ q → ¬p (sym (enc-hl-inj-live as live-hl' live-hl q))) = pre hl' live-hl'

-- STACK preservation under a HEAP store: writing the x86 memory at heap
-- address `addr` (= `enc-hl hl`) leaves every current-frame stack slot value
-- unchanged, GIVEN heap/stack disjointness (`disj`: no current-frame slot
-- aliases the heap write target). The abstract `stackMem` is untouched by a
-- heap write, so the current-frame stack correspondence is preserved — the
-- rsp-relative analogue of `store-heap-eq`'s no-alias branch. `stk` is the
-- current frame's slot→value slice (`stackMem ls (current-frame …)`).
store-stack-eq : ∀ (addr : ℕ) (v' : X.Word) (s : X.State) (stk : Slot → Maybe (StoredValue FS))
  → (∀ k → X.readMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp k) ≡ enc-maybe (stk k))
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ addr) → ⊥)
  → ∀ k → X.readMem (writeMem (memory s) addr v') (X.readReg (xregs s) rsp + slot-to-disp k)
          ≡ enc-maybe (stk k)
store-stack-eq addr v' s stk pre disj k rewrite ≢→≡ᵇfalse (disj k) = pre k

-- store-indirect: *Input1 := Output ↔ `mov [rdi], rax`. Hypotheses:
--   Input1 = SV-Ptr (AtDynamic hl)   (destination is a heap cell)
--   the value is heap-storable (writeLoc reduces to writeLocToHeap) — the
--   caller discharges this by `refl` for any non-stack-pointer value (all
--   cata-stored values: tags + heap pointers).
sim-store-indirect : ∀ (hl : HeapLocation) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) hl        -- the store target is a live block (store-WF)
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  -- heap/stack disjointness: the heap write target does NOT alias any
  -- current-frame stack slot (heap and stack occupy disjoint x86 regions).
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ enc-hl hl) → ⊥)
  → FlatCorr (flat-exec-instr store-indirect [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (enc-hl hl) (enc-sv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect hl fs s corr i-eq live-hl guard disj =
  subst (λ z → FlatCorr z xpost) (sym reduces) corr-clean
  where
    v = readReg (regs (floc fs)) Output
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (enc-hl hl) (enc-sv v)) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToHeap (floc fs) hl v ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) v (floc fs)
              ≡ writeLocToHeap (floc fs) hl v
    floc-eq = trans (cong (λ m → exec-store-via-resolved m v (floc fs)) (cong sv-as-loc i-eq)) guard
    reduces : flat-exec-instr store-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr
      ; heap-eq = store-heap-eq (falloc fs) hl v s (floc fs) live-hl (heap-eq corr)
      ; stack-eq = store-stack-eq (enc-hl hl) (enc-sv v) s
                     (stackMem (floc fs) (current-frame (falloc fs))) (stack-eq corr) disj }

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [rdi+slot], rax`.
sim-store-indirect-suc : ∀ (hl : HeapLocation) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → LiveIn (falloc fs) (sucHL hl)     -- the store target (second cell) is live
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  -- heap/stack disjointness for the second-cell write target.
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ enc-hl (sucHL hl)) → ⊥)
  → FlatCorr (flat-exec-instr store-indirect-suc [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (enc-hl (sucHL hl)) (enc-sv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-suc hl fs s corr i-eq live-shl guard disj =
  subst (λ z → FlatCorr z xpost) (sym reduces) corr-clean
  where
    v = readReg (regs (floc fs)) Output
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (enc-hl (sucHL hl)) (enc-sv v)) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToHeap (floc fs) (sucHL hl) v ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-suc-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) v (floc fs)
              ≡ writeLocToHeap (floc fs) (sucHL hl) v
    floc-eq = trans (cong (λ m → exec-store-suc-via-resolved m v (floc fs)) (cong sv-as-loc i-eq)) guard
    reduces : flat-exec-instr store-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr
      ; heap-eq = store-heap-eq (falloc fs) (sucHL hl) v s (floc fs) live-shl (heap-eq corr)
      ; stack-eq = store-stack-eq (enc-hl (sucHL hl)) (enc-sv v) s
                     (stackMem (floc fs) (current-frame (falloc fs))) (stack-eq corr) disj }

------------------------------------------------------------------------
-- Arithmetic reg-ops (Plan 0.34: flag-free, so the post is parametric over
-- the x86 flags). input2-inc / scratch-dec increment/decrement a TAG.
------------------------------------------------------------------------
inc-enc : ∀ (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k → enc-sv v + 1 ≡ enc-sv (sv-succ v)
inc-enc .(SV-Tag k) k refl = +-comm k 1

dec-enc : ∀ (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k → enc-sv v ∸ 1 ≡ enc-sv (sv-pred v)
dec-enc .(SV-Tag zero)    zero    refl = refl
dec-enc .(SV-Tag (suc m)) (suc m) refl = refl

sim-reg-input2-inc : ∀ (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Input2 ≡ SV-Tag k
  → FlatCorr (flat-exec-instr (instr-reg-op input2-inc) [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rsi + 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-input2-inc k newFlags fs s corr i2-eq = record
  { rdi-eq = rdi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; rsi-eq = trans (cong (_+ 1) (rsi-eq corr)) (inc-enc (readReg (regs (floc fs)) Input2) k i2-eq)
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

sim-reg-scratch-dec : ∀ (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-dec) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rbx ∸ 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-scratch-dec k newFlags fs s corr sc-eq = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr
  ; rbx-eq = trans (cong (_∸ 1) (rbx-eq corr)) (dec-enc (readReg (regs (floc fs)) Scratch) k sc-eq)
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }
