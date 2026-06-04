-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Target.X86-64.FlatCorrespondence
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
open import Data.Nat using (ℕ)

module Once.CCC.Target.X86-64.FlatCorrespondence
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)   -- heap-address layout (Word = ℕ)
  where

open import Data.Nat using (zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Properties using (+-comm)
open import Data.Bool using (Bool; false)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; mkflags; _<ᵇ_)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (rax; rbx; rsi; rdi)
open import Once.CCC.Machine.SMCore
open ExecFinal {FS} using (exec-load-via-resolved; exec-load-suc-via-resolved; exec-load-with-value)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

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
-- flag, and the heap memory (under enc-hl + enc-sv).
-- (Stack memory correspondence is added with the stack-using lemmas;
-- the cata is heap-only.)
------------------------------------------------------------------------
record FlatCorr (fs : FlatState) (s : X.State) : Set where
  field
    rdi-eq  : X.readReg (X.State.regs s) rdi ≡ enc-sv (readReg (regs (floc fs)) Input1)
    rsi-eq  : X.readReg (X.State.regs s) rsi ≡ enc-sv (readReg (regs (floc fs)) Input2)
    rax-eq  : X.readReg (X.State.regs s) rax ≡ enc-sv (readReg (regs (floc fs)) Output)
    rbx-eq  : X.readReg (X.State.regs s) rbx ≡ enc-sv (readReg (regs (floc fs)) Scratch)
    pc-eq   : X.State.pc s ≡ fpc fs
    zf-eq   : X.Flags.zf (X.State.flags s) ≡ fzf fs
    halt-eq : X.State.halted s ≡ halted (floc fs)
    heap-eq : ∀ (hl : HeapLocation) →
              X.readMem (X.State.memory s) (enc-hl hl) ≡ enc-maybe (heapMem (floc fs) hl)
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
  ; pc-eq   = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq   = zf-eq corr
  ; halt-eq = halt-eq corr
  ; heap-eq = heap-eq corr
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-to-input [] fs)
             (mkstate (xwriteReg (xregs s) rdi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-input fs s corr = record
  { rdi-eq = rax-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- mov-input2-to-output (Output := Input2) ↔ `mov rax, rsi`.
sim-mov-input2-to-output : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-input2-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-input2-to-output fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rsi-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- mov-output-to-input2 (Input2 := Output) ↔ `mov rsi, rax`.
sim-mov-output-to-input2 : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr mov-output-to-input2 [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-output-to-input2 fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rax-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n ⟹ rax-eq=refl.
sim-load-tag-lit : ∀ (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-load-tag-lit n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-tag-lit n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`. rbx-eq=refl.
sim-reg-scratch-one : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-one) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 1) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-one fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`. rbx-eq=refl.
sim-reg-scratch-zero : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-zero fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op input2-zero (Input2 := SV-Tag 0) ↔ `mov rsi, 0`. rsi-eq=refl.
sim-reg-input2-zero : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op input2-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rsi 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-input2-zero fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = refl ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

-- instr-reg-op scratch-load-count (Scratch := Input2) ↔ `mov rbx, rsi`. rbx-eq=rsi-eq.
sim-reg-scratch-load-count : ∀ (fs : FlatState) (s : X.State) → FlatCorr fs s
  → FlatCorr (flat-exec-instr (instr-reg-op scratch-load-count) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-load-count fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rsi-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

------------------------------------------------------------------------
-- Control test: instr-ctrl c-test-scratch (fzf := Scratch≟0) ↔ `cmp rbx,0`.
-- This is the FLAT-CONTROL correspondence — the loop's conditional branch.
-- Needs "Scratch holds a tag" (always true for the cata's loop flag).
-- Boolean bridge: the typed `sv-is-zero (SV-Tag n)` and the untyped
-- `n ≡ᵇ 0` agree (both decide n=0). The `<ᵇ` (sign flag) is irrelevant —
-- FlatCorr only tracks `zf` (the `≡ᵇ` result).
------------------------------------------------------------------------
sv-tag-zero : ∀ (n : ℕ) → sv-is-zero (SV-Tag {FS} n) ≡ (n ≡ᵇ 0)
sv-tag-zero zero    = refl
sv-tag-zero (suc _) = refl

enc-zero : ∀ (v : StoredValue FS) (n : ℕ) → v ≡ SV-Tag n → (enc-sv v ≡ᵇ 0) ≡ sv-is-zero v
enc-zero .(SV-Tag n) n refl = sym (sv-tag-zero n)

sim-test-scratch : ∀ (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag n
  → FlatCorr (flat-exec-instr (instr-ctrl c-test-scratch) [] fs)
             (mkstate (xregs s) (memory s)
                      (mkflags (xreadReg (xregs s) rbx ≡ᵇ 0) (xreadReg (xregs s) rbx <ᵇ 0) false)
                      (pc s + 1) (xhalted s))
sim-test-scratch n fs s corr sc-eq = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
  ; zf-eq = trans (cong (_≡ᵇ 0) (rbx-eq corr)) (enc-zero (readReg (regs (floc fs)) Scratch) n sc-eq)
  ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

------------------------------------------------------------------------
-- Control test on a HEAP tag: instr-ctrl c-test-tag (fzf := *Input1 ≟0)
-- ↔ `cmp [rdi], 0`. Like c-test-scratch but the tag lives in the heap
-- cell Input1 points to. Hypotheses (true on every cata step — the
-- cursor points to a live cell holding a tag):
--   Input1 = SV-Ptr (AtDynamic hl),  heapMem hl = just (SV-Tag k).
-- The abstract-halt vs x86-`nothing` Maybe mismatch dissolves: the read
-- succeeds on both sides, so neither halts. We reduce the (stuck) flat
-- step under the hypotheses, then transport the clean correspondence.
------------------------------------------------------------------------
sim-test-tag : ∀ (hl : HeapLocation) (k : ℕ) (fs : FlatState) (s : X.State) → FlatCorr fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) hl ≡ just (SV-Tag k)
  → FlatCorr (flat-exec-instr (instr-ctrl c-test-tag) [] fs)
             (mkstate (xregs s) (memory s)
                      (mkflags (k ≡ᵇ 0) (k <ᵇ 0) false) (pc s + 1) (xhalted s))
sim-test-tag hl k fs s corr i-eq h-eq =
  subst (λ z → FlatCorr z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xregs s) (memory s) (mkflags (k ≡ᵇ 0) (k <ᵇ 0) false) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { fpc = suc (fpc fs) ; fzf = sv-is-zero (SV-Tag {FS} k) }
    -- Reduce the (stuck) heap read via cong/trans (NOT rewrite: `readReg
    -- _ Input1` reduces to the `input1` projection, so a syntactic rewrite
    -- can't match — cong checks definitional equality and goes through).
    fzf-eq : tag-zf (flat-read-tag (floc fs)) ≡ sv-is-zero (SV-Tag {FS} k)
    fzf-eq = cong tag-zf (trans (cong (flat-read-at (floc fs)) (cong sv-as-loc i-eq)) h-eq)
    reduces : flat-exec-instr (instr-ctrl c-test-tag) [] fs ≡ cleanFlat
    reduces = cong (λ b → record fs { fpc = suc (fpc fs) ; fzf = b }) fzf-eq
    corr-clean : FlatCorr cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
      ; zf-eq = sym (sv-tag-zero k)
      ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

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
      ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
      ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }

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
      ; pc-eq = trans (cong (_+ 1) (pc-eq corr)) (+-comm (fpc fs) 1)
      ; zf-eq = zf-eq corr ; halt-eq = halt-eq corr ; heap-eq = heap-eq corr }
