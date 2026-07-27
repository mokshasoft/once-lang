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
open import Once.Word using (Carrier)
open import Once.Type using (Int; Float; fits-int; fits-float)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence
  (FS : FrameSemantics)
  where

open import Data.Nat using (zero; suc; _+_; _∸_; _*_; _≡ᵇ_; _≟_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; +-assoc; +-cancelˡ-≡; *-cancelʳ-≡; n∸n≡0
                                      ; m≤m+n; <-irrefl; <-trans; <-transʳ; <-transˡ
                                      ; +-monoʳ-<; *-monoˡ-<; ≤-refl; ≤-trans; m<n⇒m<1+n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; Dec)
open import Data.List using ([])
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

open import Once.Memory.HeapAddress
  using (HeapRef; sucHL; heap-loc; mkHeapRef; heap-ref; heap-offset; ref-id; _≟HL_; offsetHL)
import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; mkflags; _<ᵇ_; writeMem)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (rax; rbx; rsi; rdi; rsp; r12; r15; slot-size; slots)
open import Once.CCC.Target.X86-64.AbstractToX86 using (slot-to-disp)
open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeHeapMem
                       ; readLoc; writeLoc-read-same-stack; writeLoc-preserves-other)
open ExecFinal {FS} using (exec-load-via-resolved; exec-load-suc-via-resolved; exec-load-with-value
                          ; exec-store-via-resolved; exec-store-suc-via-resolved)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below)
open AbstractExec {FS} using (exec-abstract; exec-load-from-slot-with-value; exec-restore-input-with-value)
open FrameSemantics FS using (Frame)

------------------------------------------------------------------------
-- THE CARRIED HEAP INJECTION (`HeapView`).
--
-- The heap address map is NOT a global function fixed once and for all: the
-- address a fresh block gets is decided by the CONCRETE allocator at run time
-- (the `%r15` bump), and the abstract state — a block-ID counter — does not
-- record block SIZES, so no state-indexed pure function `HeapLocation → ℕ`
-- can predict the next block's address. (A global law
-- `addr(block (suc st)) ≡ addr(block st) + 8·n` is outright INCONSISTENT: `n`
-- varies per allocation site while the left-hand side does not depend on it.)
--
-- So, CompCert-style, the injection is CARRIED BY THE CORRESPONDENCE and
-- EXTENDED at each allocation: `haddr`/`HDom` is the map built so far,
-- `hfront` the concrete frontier (`%r15`). Non-allocating steps thread the
-- same view; `instr-alloc-heap` extends it (fresh block ↦ the old frontier).
-- The three laws are exactly what the extension must re-establish and what
-- the load/store steps consume.
------------------------------------------------------------------------
record HeapView : Set₁ where
  constructor mkHV
  field
    -- The address map. Total (an unconstrained value off-domain is harmless —
    -- only `HDom` cells carry correspondence), CONTIGUOUS within a block.
    haddr     : HeapLocation → ℕ
    -- The cells this view maps: the in-bounds slots of the blocks allocated so far.
    HDom      : HeapLocation → Set
    -- The allocation frontier: the address the NEXT block will start at (= %r15).
    hfront    : ℕ
    haddr-suc : ∀ (hl : HeapLocation) → haddr (sucHL hl) ≡ haddr hl + slot-size
    -- Injective ON THE DOMAIN — the allocator's `blocks-disjoint`, no more.
    haddr-inj : ∀ {a b : HeapLocation} → HDom a → HDom b → haddr a ≡ haddr b → a ≡ b
    -- Everything allocated lies BELOW the frontier: what makes the next
    -- allocation's cells fresh (and keeps the extension injective).
    dom-below : ∀ {hl : HeapLocation} → HDom hl → haddr hl < hfront
open HeapView public

------------------------------------------------------------------------
-- Value encoding: typed StoredValue → untyped x86 Word.
--   SV-Tag n        → n              (sum/loop-flag/depth tags)
--   SV-Ptr (heap hl)→ haddr hv hl    (heap pointers — the cata's cursors)
-- The non-cata shapes (stack pointers, primitive literals, code addrs)
-- get placeholder encodings for now — they don't occur in cata traces;
-- a faithful primitive-literal encoding is future work (Phase D'').
------------------------------------------------------------------------
-- ⟦ Int ⟧ = Carrier = ℕ = X.Word; the explicit Carrier→Word target forces the
-- parameterised-module projection `⟦ Int ⟧` to reduce (it stays stuck when the
-- return type is bare `ℕ`). This is the `mov rax, imm v` immediate value.
lit-word : Carrier → X.Word
lit-word x = x

enc-sv : HeapView → StoredValue FS → X.Word
enc-sv hv (SV-Tag n)                = n
enc-sv hv (SV-Ptr (AtDynamic hl))   = haddr hv hl
enc-sv hv (SV-Ptr (AtStack _ _))    = 0
-- A register-fittable INT literal encodes to its own value — exactly the immediate
-- `compile-const fits-int v = mov rax, v` loads (so load-const's rax-eq is refl and
-- literal values flow through FlatCorr instead of collapsing to 0). Float is
-- unimplemented (`compile-const fits-float` traps to ud2), so it gets no register
-- correspondence — encode 0.
-- ENUMERATED (no catch-all): a `SV-Lit _ _` catch-all does not survive the
-- case-tree translation, so `enc-sv hv (SV-Lit fits-float v)` would not reduce
-- and the extension-stability lemma below could not be stated by `refl`.
enc-sv hv (SV-Lit fits-int v)       = lit-word v
enc-sv hv (SV-Lit fits-float v)     = 0
enc-sv hv (SV-Code n)               = n

enc-maybe : HeapView → Maybe (StoredValue FS) → Maybe X.Word
enc-maybe hv (just v) = just (enc-sv hv v)
enc-maybe hv nothing  = nothing

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
record FlatCorr (hv : HeapView) (fs : FlatState) (s : X.State) : Set where
  field
    rdi-eq  : X.readReg (X.State.regs s) rdi ≡ enc-sv hv (readReg (regs (floc fs)) Input1)
    rsi-eq  : X.readReg (X.State.regs s) rsi ≡ enc-sv hv (readReg (regs (floc fs)) Input2)
    rax-eq  : X.readReg (X.State.regs s) rax ≡ enc-sv hv (readReg (regs (floc fs)) Output)
    rbx-eq  : X.readReg (X.State.regs s) rbx ≡ enc-sv hv (readReg (regs (floc fs)) Scratch)
    halt-eq : X.State.halted s ≡ halted (floc fs)
    -- THE FRONTIER: `%r15` (the bump allocator's heap top) IS the view's frontier.
    -- This is what makes the next `instr-alloc-heap` provable: the fresh block's
    -- address is read off the concrete machine, not predicted from the abstract state.
    r15-eq  : X.readReg (X.State.regs s) r15 ≡ hfront hv
    -- Every mapped cell belongs to a block the ABSTRACT allocator has handed out
    -- (ref-id below the abstract counter). Together with `dom-below` this is what
    -- makes the next allocation fresh on BOTH sides.
    dom-fresh : ∀ {hl : HeapLocation} → HDom hv hl →
                ref-id (heap-ref hl) < next-heap-ref (falloc fs)
    heap-eq : ∀ (hl : HeapLocation) → HDom hv hl →
              X.readMem (X.State.memory s) (haddr hv hl) ≡ enc-maybe hv (heapMem (floc fs) hl)
    -- BOUNDED to the current frame's live RUNTIME slots (k < stackSlot). An
    -- UNBOUNDED ∀ k would be unsatisfiable (it would claim the CALLER's slots,
    -- above rsp, holding live data, ≡ the abstract `nothing`). The bound is the
    -- RUNTIME slot counter `stackSlot` (the "like rsp, as slot count" register
    -- that tracks rsp: rsp = INIT − stackSlot·8), NOT the compile-time frontier
    -- next-slot — so frame ops that move rsp (alloc/dealloc-stack) shrink/grow
    -- the bound in lockstep with rsp, and reclaim-to (next-slot only) leaves it
    -- stable. Mirrors heap-eq's LiveIn bound.
    stack-eq : ∀ (k : Slot) → k < stackSlot (regs (floc fs)) →
              X.readMem (X.State.memory s) (X.readReg (X.State.regs s) rsp + slot-to-disp k)
              ≡ enc-maybe hv (stackMem (floc fs) (current-frame (falloc fs)) k)
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
sim-mov-to-output : {hv : HeapView} (fs : FlatState) (s : X.State)
  → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rdi))
                      (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-output {hv} fs s corr = record
  { rdi-eq  = rdi-eq corr
  ; rax-eq  = rdi-eq corr
  ; rsi-eq  = rsi-eq corr
  ; rbx-eq  = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
  ; heap-eq = heap-eq corr
  ; stack-eq = stack-eq corr
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-to-input [] fs)
             (mkstate (xwriteReg (xregs s) rdi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-input {hv} fs s corr = record
  { rdi-eq = rax-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- mov-input2-to-output (Output := Input2) ↔ `mov rax, rsi`.
sim-mov-input2-to-output : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-input2-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-input2-to-output {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rsi-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- mov-output-to-input2 (Input2 := Output) ↔ `mov rsi, rax`.
sim-mov-output-to-input2 : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-output-to-input2 [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-output-to-input2 {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rax-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n ⟹ rax-eq=refl.
sim-load-tag-lit : {hv : HeapView} (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-tag-lit n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-tag-lit {hv} n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`. rbx-eq=refl.
sim-reg-scratch-one : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-one) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 1) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-one {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`. rbx-eq=refl.
sim-reg-scratch-zero : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-zero {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op input2-zero (Input2 := SV-Tag 0) ↔ `mov rsi, 0`. rsi-eq=refl.
sim-reg-input2-zero : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op input2-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rsi 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-input2-zero {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = refl ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-load-count (Scratch := Input2) ↔ `mov rbx, rsi`. rbx-eq=rsi-eq.
sim-reg-scratch-load-count : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-load-count) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-load-count {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rsi-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

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

enc-zero : ∀ {hv : HeapView} (v : StoredValue FS) (n : ℕ) → v ≡ SV-Tag n → (enc-sv hv v ≡ᵇ 0) ≡ sv-is-zero v
enc-zero .(SV-Tag n) n refl = sym (sv-tag-zero n)

------------------------------------------------------------------------
-- Heap load: load-indirect-suc (Output := *(sucLoc Input1)) ↔
-- `mov rax, [rdi + slot-size]`. Hypotheses (cata cursor + live child
-- cell): Input1 = SV-Ptr (AtDynamic hl),  heapMem (sucHL hl) = just w.
-- The x86 ADDRESS law (haddr hv (sucHL hl) = haddr hv hl + slot-size) is a
-- separate concern (proving execInstr REACHES this post-state); here we
-- relate the read VALUES: new rax = enc-sv hv w = enc-sv hv (new Output).
------------------------------------------------------------------------
sim-load-indirect-suc : {hv : HeapView} (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → FlatCorr hv (flat-exec-instr load-indirect-suc [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-suc {hv} hl w fs s corr i-eq h-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Heap load (no offset): load-indirect (Output := *Input1) ↔
-- `mov rax, [rdi]`. Sibling of load-indirect-suc; reads the cell Input1
-- points to directly. Same reduce-then-correspond structure.
------------------------------------------------------------------------
sim-load-indirect : {hv : HeapView} (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) hl ≡ just w
  → FlatCorr hv (flat-exec-instr load-indirect [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect {hv} hl w fs s corr i-eq h-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-load-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) h-eq)
    reduces : flat-exec-instr load-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- STACK LOAD: `load-from-slot slot` (Output := stack[current-frame, slot]) ↔
-- `mov rax, [rsp + slot-to-disp slot]`. The read VALUE comes from `stack-eq`
-- (memory s at rsp+disp = enc-maybe hv of the slot's abstract value); the x86 post
-- is identical in shape to `sim-load-indirect` (rax := enc-sv hv w). Only the
-- SUCCESS case (slot holds `just w`) — the empty-slot (`nothing`→halt) case is
-- routed as a WF residual, exactly like load-indirect's bad case. This is the
-- FIRST consumer of the new `stack-eq` field (via block-step-load-from-slot).
------------------------------------------------------------------------
sim-load-from-slot : {hv : HeapView} (slot : Slot) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → FlatCorr hv (flat-exec-instr (load-from-slot slot) [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-from-slot {hv} slot w fs s corr st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    ex-eq : exec-abstract (load-from-slot slot) (floc fs) (falloc fs)
            ≡ (record (floc fs) { regs = writeReg (regs (floc fs)) Output w } , falloc fs)
    ex-eq = cong (λ mv → exec-load-from-slot-with-value mv (floc fs) (falloc fs)) st-eq
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    reduces : flat-exec-instr (load-from-slot slot) [] fs ≡ cleanFlat
    reduces = cong (λ p → record fs { floc = proj₁ p ; falloc = proj₂ p ; fpc = suc (fpc fs) }) ex-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Heap STORES (Plan 0.32 Phase D). A heap write ↔ x86 `mov [addr], reg`.
-- The crux: relate the typed heap update `writeHeapMem` (decides cells by
-- ≟HL) to the x86 memory update `writeMem` (decides addresses by ≡ᵇ).
-- They agree because haddr hv is INJECTIVE (the memory injection).
------------------------------------------------------------------------
≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≢→≡ᵇfalse : ∀ {m n : ℕ} → (m ≡ n → ⊥) → (m ≡ᵇ n) ≡ false
≢→≡ᵇfalse {zero}  {zero}  ¬p = ⊥-elim (¬p refl)
≢→≡ᵇfalse {zero}  {suc n} _  = refl
≢→≡ᵇfalse {suc m} {zero}  _  = refl
≢→≡ᵇfalse {suc m} {suc n} ¬p = ≢→≡ᵇfalse {m} {n} (λ p → ¬p (cong suc p))

-- The store correspondence: writing `v` at heap cell `hl` (x86: haddr hv hl)
-- preserves the heap agreement at every other cell, and installs enc-sv v
-- at `hl`. Case-split on ≟HL; enc-hl-inj turns cell-distinctness into
-- address-distinctness so the x86 `≡ᵇ` test resolves the same way.
-- store-heap-eq now works over LIVE cells only: the write target `hl` is live,
-- and the correspondence + result quantify over live `hl'`. Distinctness for the
-- no-alias case is `enc-hl-inj-live` (the allocator's `blocks-disjoint` on live
-- blocks) — dead cells are never compared.
store-heap-eq : ∀ (hv : HeapView) (hl : HeapLocation) (v : StoredValue FS) (s : X.State) (ls : LocState FS)
  → HDom hv hl
  → (∀ hl' → HDom hv hl' → X.readMem (memory s) (haddr hv hl') ≡ enc-maybe hv (heapMem ls hl'))
  → ∀ hl' → HDom hv hl' → X.readMem (writeMem (memory s) (haddr hv hl) (enc-sv hv v)) (haddr hv hl')
            ≡ enc-maybe hv (writeHeapMem (heapMem ls) hl v hl')
-- (writeHeapMem is with-free now, so the `with hl ≟HL hl'` below reduces
-- it directly — no read-after-write accessor lemmas needed.)
store-heap-eq hv hl v s ls live-hl pre hl' live-hl' with hl ≟HL hl'
... | yes refl rewrite ≡ᵇ-refl (haddr hv hl) = refl
... | no ¬p rewrite ≢→≡ᵇfalse {haddr hv hl'} {haddr hv hl}
      (λ q → ¬p (sym (haddr-inj hv live-hl' live-hl q))) = pre hl' live-hl'

-- STACK preservation under a HEAP store: writing the x86 memory at heap
-- address `addr` (= `haddr hv hl`) leaves every current-frame stack slot value
-- unchanged, GIVEN heap/stack disjointness (`disj`: no current-frame slot
-- aliases the heap write target). The abstract `stackMem` is untouched by a
-- heap write, so the current-frame stack correspondence is preserved — the
-- rsp-relative analogue of `store-heap-eq`'s no-alias branch. `stk` is the
-- current frame's slot→value slice (`stackMem ls (current-frame …)`).
store-stack-eq : ∀ {hv : HeapView} (addr : ℕ) (v' : X.Word) (s : X.State) (stk : Slot → Maybe (StoredValue FS)) (bound : ℕ)
  → (∀ k → k < bound → X.readMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp k) ≡ enc-maybe hv (stk k))
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ addr) → ⊥)
  → ∀ k → k < bound → X.readMem (writeMem (memory s) addr v') (X.readReg (xregs s) rsp + slot-to-disp k)
          ≡ enc-maybe hv (stk k)
store-stack-eq {hv} addr v' s stk bound pre disj k k<b rewrite ≢→≡ᵇfalse (disj k) = pre k k<b

-- store-indirect: *Input1 := Output ↔ `mov [rdi], rax`. Hypotheses:
--   Input1 = SV-Ptr (AtDynamic hl)   (destination is a heap cell)
--   the value is heap-storable (writeLoc reduces to writeLocToHeap) — the
--   caller discharges this by `refl` for any non-stack-pointer value (all
--   cata-stored values: tags + heap pointers).
sim-store-indirect : {hv : HeapView} (hl : HeapLocation) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the store target is a live block (store-WF)
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  -- heap/stack disjointness: the heap write target does NOT alias any
  -- current-frame stack slot (heap and stack occupy disjoint x86 regions).
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ haddr hv hl) → ⊥)
  → FlatCorr hv (flat-exec-instr store-indirect [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (haddr hv hl) (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect {hv} hl fs s corr i-eq live-hl guard disj =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    v = readReg (regs (floc fs)) Output
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (haddr hv hl) (enc-sv hv v)) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToHeap (floc fs) hl v ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) v (floc fs)
              ≡ writeLocToHeap (floc fs) hl v
    floc-eq = trans (cong (λ m → exec-store-via-resolved m v (floc fs)) (cong sv-as-loc i-eq)) guard
    reduces : flat-exec-instr store-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; heap-eq = store-heap-eq hv hl v s (floc fs) live-hl (heap-eq corr)
      ; stack-eq = store-stack-eq (haddr hv hl) (enc-sv hv v) s
                     (stackMem (floc fs) (current-frame (falloc fs))) (stackSlot (regs (floc fs))) (stack-eq corr) disj }

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [rdi+slot], rax`.
sim-store-indirect-suc : {hv : HeapView} (hl : HeapLocation) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the store target (second cell) is live
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  -- heap/stack disjointness for the second-cell write target.
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ haddr hv (sucHL hl)) → ⊥)
  → FlatCorr hv (flat-exec-instr store-indirect-suc [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (haddr hv (sucHL hl)) (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-suc {hv} hl fs s corr i-eq live-shl guard disj =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    v = readReg (regs (floc fs)) Output
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (haddr hv (sucHL hl)) (enc-sv hv v)) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToHeap (floc fs) (sucHL hl) v ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-suc-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) v (floc fs)
              ≡ writeLocToHeap (floc fs) (sucHL hl) v
    floc-eq = trans (cong (λ m → exec-store-suc-via-resolved m v (floc fs)) (cong sv-as-loc i-eq)) guard
    reduces : flat-exec-instr store-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; heap-eq = store-heap-eq hv (sucHL hl) v s (floc fs) live-shl (heap-eq corr)
      ; stack-eq = store-stack-eq (haddr hv (sucHL hl)) (enc-sv hv v) s
                     (stackMem (floc fs) (current-frame (falloc fs))) (stackSlot (regs (floc fs))) (stack-eq corr) disj }

------------------------------------------------------------------------
-- STACK RESTORE: `restore-input slot` (Input1 := stack[current-frame, slot]) ↔
-- `mov rdi, [rsp + slot-to-disp slot]`. Identical to load-from-slot but the
-- destination is Input1/rdi (not Output/rax). Success case only; empty slot
-- routed as a residual.
------------------------------------------------------------------------
sim-restore-input : {hv : HeapView} (slot : Slot) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → FlatCorr hv (flat-exec-instr (restore-input slot) [] fs)
             (mkstate (xwriteReg (xregs s) rdi (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-restore-input {hv} slot w fs s corr st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rdi (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    ex-eq : exec-abstract (restore-input slot) (floc fs) (falloc fs)
            ≡ (record (floc fs) { regs = writeReg (regs (floc fs)) Input1 w } , falloc fs)
    ex-eq = cong (λ mv → exec-restore-input-with-value mv (floc fs) (falloc fs)) st-eq
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Input1 w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    reduces : flat-exec-instr (restore-input slot) [] fs ≡ cleanFlat
    reduces = cong (λ p → record fs { floc = proj₁ p ; falloc = proj₂ p ; fpc = suc (fpc fs) }) ex-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = refl ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- STACK STORE: `store-at-slot slot` (stack[current-frame, slot] := Output) ↔
-- `mov [rsp + slot-to-disp slot], rax`. The write UPDATES the current-frame
-- stack correspondence; distinct slots map to distinct x86 addresses (slot-to-
-- disp injective under +-cancel/*-cancel), so the x86 `≡ᵇ` address test and the
-- abstract `slot ≟ k` decision agree cell-by-cell — the rsp-relative analogue of
-- `store-heap-eq`. A stack write must also leave the HEAP correspondence intact,
-- which needs stack/heap address-disjointness (`disj`, a layout invariant).
------------------------------------------------------------------------

-- slot-address injectivity: same base ⇒ equal x86 slot addresses ⇒ equal slots.
slot-addr-inj : ∀ (base : ℕ) (k slot : Slot)
              → (base + slot-to-disp k ≡ base + slot-to-disp slot) → k ≡ slot
slot-addr-inj base k slot eq =
  *-cancelʳ-≡ k slot slot-size (+-cancelˡ-≡ base (slot-to-disp k) (slot-to-disp slot) eq)

atstack-slot-inj : ∀ (cf : Frame) {a b : Slot} → AtStack {FS} cf a ≡ AtStack cf b → a ≡ b
atstack-slot-inj cf refl = refl

-- HEAP preservation under a STACK store: symmetric to store-stack-eq — writing at
-- the stack address `waddr` leaves every live heap cell `haddr hv hl'` unchanged,
-- given stack/heap disjointness (`disj`).
store-slot-heap-eq : ∀ (hv : HeapView) (waddr : ℕ) (v' : X.Word) (s : X.State) (ls : LocState FS)
  → (∀ hl' → HDom hv hl' → X.readMem (memory s) (haddr hv hl') ≡ enc-maybe hv (heapMem ls hl'))
  → (∀ hl' → HDom hv hl' → (waddr ≡ haddr hv hl') → ⊥)
  → ∀ hl' → HDom hv hl' → X.readMem (writeMem (memory s) waddr v') (haddr hv hl') ≡ enc-maybe hv (heapMem ls hl')
store-slot-heap-eq hv waddr v' s ls pre disj hl' live
  rewrite ≢→≡ᵇfalse {haddr hv hl'} {waddr} (λ eq → disj hl' live (sym eq)) = pre hl' live

-- STACK read-back under the stack store: reading slot `k` after writing slot `slot`
-- (same current frame `cf`) — `k ≡ slot` ⇒ the written value; else the old value.
-- The x86 side (writeMem/≡ᵇ) and abstract side (writeLoc/≟) agree via slot-addr-inj.
-- J-style aux over the slot decision (passed as a value, NOT `with`): a `with slot ≟ k`
-- would abstract the scrutinee inside the abstract `writeStackMem-aux (… ≟F …) (slot ≟ k)`
-- as `yes refl`, diverging from the read-back lemma's `slot ≟ slot` form. Feeding the
-- Dec to `go` keeps the goal's readLoc/writeLoc intact so the lemmas apply.
store-slot-stack-eq : ∀ {hv : HeapView} (base : ℕ) (slot : Slot) (Out : StoredValue FS) (s : X.State) (ls : LocState FS) (cf : Frame) (bound : ℕ)
  → (∀ k → k < bound → X.readMem (memory s) (base + slot-to-disp k) ≡ enc-maybe hv (stackMem ls cf k))
  → ∀ k → k < bound → X.readMem (writeMem (memory s) (base + slot-to-disp slot) (enc-sv hv Out)) (base + slot-to-disp k)
          ≡ enc-maybe hv (readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k))
store-slot-stack-eq {hv} base slot Out s ls cf bound old k k<b = go (k ≟ slot)
  where go : Dec (k ≡ slot)
           → X.readMem (writeMem (memory s) (base + slot-to-disp slot) (enc-sv hv Out)) (base + slot-to-disp k)
             ≡ enc-maybe hv (readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k))
        go (yes refl) rewrite ≡ᵇ-refl (base + slot-to-disp slot)
                            | writeLoc-read-same-stack ls cf slot Out = refl
        go (no  p)    rewrite ≢→≡ᵇfalse {base + slot-to-disp k} {base + slot-to-disp slot}
                                (λ eq → p (slot-addr-inj base k slot eq))
                            | writeLoc-preserves-other ls (AtStack cf slot) (AtStack cf k) Out
                                (λ eq → p (sym (atstack-slot-inj cf eq))) = old k k<b

sim-store-at-slot : {hv : HeapView} (slot : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  -- stack/heap disjointness: the written slot address aliases no live heap cell.
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) rsp + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → FlatCorr hv (flat-exec-instr (store-at-slot slot) [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp slot)
                                (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-at-slot {hv} slot fs s corr disj = corr-clean
  where
    base = X.readReg (xregs s) rsp
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (base + slot-to-disp slot) (enc-sv hv Out))
                    (flags s) (pc s + 1) (xhalted s)
    corr-clean : FlatCorr hv (flat-exec-instr (store-at-slot slot) [] fs) xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
      ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp slot) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; stack-eq = store-slot-stack-eq base slot Out s (floc fs) cf (stackSlot (regs (floc fs))) (stack-eq corr) }

------------------------------------------------------------------------
-- STACK ALLOCATION: `instr-alloc-stack n` (reserve n slots) ↔ `sub rsp, n*8`.
-- The abstract advances the slot frontier (next-slot += n) and the stackSlot
-- counter; the x86 lowers rsp by n*8. Because alloc-stack sits at a FRAME
-- ENTRY (`next-slot ≡ 0`, WF), the bounded stack-eq covers ONLY the fresh new
-- slots k < n — no existing slots to re-anchor across the rsp shift. Those
-- fresh slots are uninitialised on BOTH sides (abstract stackMem = nothing;
-- the fresh x86 stack region below rsp is unwritten), so the new correspondence
-- is `nothing ≡ nothing`. The 4 tracked registers, halt, and heap are untouched
-- (heap liveness is invariant under a next-slot change — `liveinv`). Flags are
-- clobbered by `sub` but FlatCorr is flag-free, so the post is flag-parametric.
------------------------------------------------------------------------
sim-alloc-stack : {hv : HeapView} (n : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → stackSlot (regs (floc fs)) ≡ 0                  -- WF: alloc-stack at frame entry (runtime depth 0)
  → (∀ k → k < n → stackMem (floc fs) (current-frame (falloc fs)) k ≡ nothing)   -- fresh (abstract)
  → (∀ k → k < n → X.readMem (memory s) ((X.readReg (xregs s) rsp ∸ slots n) + slot-to-disp k) ≡ nothing)  -- fresh (x86)
  → FlatCorr hv (flat-exec-instr (instr-alloc-stack n) [] fs)
             (mkstate (xwriteReg (xregs s) rsp (X.readReg (xregs s) rsp ∸ slots n))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-alloc-stack {hv} n newFlags fs s corr entry fresh-abs fresh-x86 = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
  ; heap-eq = heap-eq corr
  ; stack-eq = λ k k<ns → stk k (subst (k <_) (cong (_+ n) entry) k<ns) }
  where
    stk : ∀ k → k < n → X.readMem (memory s) ((X.readReg (xregs s) rsp ∸ slots n) + slot-to-disp k)
            ≡ enc-maybe hv (stackMem (floc fs) (current-frame (falloc fs)) k)
    stk k k<n = trans (fresh-x86 k k<n) (sym (cong (enc-maybe hv) (fresh-abs k k<n)))

------------------------------------------------------------------------
-- STACK DEALLOCATION: `instr-dealloc-stack n` (free n slots) ↔ `add rsp, n*8`.
-- The abstract lowers the runtime depth (stackSlot −= n); the x86 raises rsp by
-- n*8. At a FULL-frame exit (stackSlot ≡ n ⇒ post stackSlot = n∸n = 0), the
-- bounded stack-eq post is VACUOUS (k < 0), so it holds trivially — no need to
-- re-anchor the freed slots across the rsp shift. The 4 tracked regs / halt /
-- heap are untouched (dealloc changes neither falloc nor stackMem). Flag-parametric.
------------------------------------------------------------------------
sim-dealloc-stack : {hv : HeapView} (n : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → stackSlot (regs (floc fs)) ≡ n                  -- WF: full-frame exit (runtime depth n → 0)
  → FlatCorr hv (flat-exec-instr (instr-dealloc-stack n) [] fs)
             (mkstate (xwriteReg (xregs s) rsp (X.readReg (xregs s) rsp + slots n))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-dealloc-stack {hv} n newFlags fs s corr full = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
  ; heap-eq = heap-eq corr
  ; stack-eq = λ k k<ss → ⊥-elim (bad k k<ss) }
  where
    ss≡0 : stackSlot (regs (floc fs)) ∸ n ≡ 0
    ss≡0 = trans (cong (_∸ n) full) (n∸n≡0 n)
    bad : ∀ k → k < stackSlot (regs (floc fs)) ∸ n → ⊥
    bad k k<ss with subst (k <_) ss≡0 k<ss
    ... | ()

------------------------------------------------------------------------
-- FRAME PUSH: `instr-push-frame cap` ↔ `push rbp; mov rbp,rsp; sub rsp,cap*8`.
-- The abstract RESETS the runtime depth (writeStackSlot 0) — a fresh frame — so
-- the bounded stack-eq post is VACUOUS (stackSlot ≡ 0 ⇒ k < 0), holding trivially.
-- The x86 3-instruction prologue touches only rbp/rsp (the 4 tracked registers,
-- rdi/rsi/rax/rbx, are preserved) and writes ONE cell (the saved rbp at [rsp−8]).
-- So the sim is parametric over the post state `xp` + the preservation facts the
-- block-step establishes (4 regs unchanged; halt unchanged; heap unchanged at every
-- LIVE cell — the block-step discharges that via a heap/stack disjointness for the
-- push write). Only the vacuous stack-eq is proved here.
------------------------------------------------------------------------
sim-push-frame : {hv : HeapView} (n : ℕ) (fs : FlatState) (s xp : X.State) → FlatCorr hv fs s
  → X.readReg (X.State.regs xp) rdi ≡ X.readReg (X.State.regs s) rdi
  → X.readReg (X.State.regs xp) rsi ≡ X.readReg (X.State.regs s) rsi
  → X.readReg (X.State.regs xp) rax ≡ X.readReg (X.State.regs s) rax
  → X.readReg (X.State.regs xp) rbx ≡ X.readReg (X.State.regs s) rbx
  → X.State.halted xp ≡ X.State.halted s
  → X.readReg (X.State.regs xp) r15 ≡ X.readReg (X.State.regs s) r15
  → (∀ hl → HDom hv hl → X.readMem (X.State.memory xp) (haddr hv hl)
                                  ≡ X.readMem (X.State.memory s) (haddr hv hl))
  → FlatCorr hv (flat-exec-instr (instr-push-frame n) [] fs) xp
sim-push-frame {hv} n fs s xp corr rdi-p rsi-p rax-p rbx-p halt-p r15-p heap-p = record
  { rdi-eq = trans rdi-p (rdi-eq corr) ; rsi-eq = trans rsi-p (rsi-eq corr)
  ; rax-eq = trans rax-p (rax-eq corr) ; rbx-eq = trans rbx-p (rbx-eq corr)
  ; halt-eq = trans halt-p (halt-eq corr) ; r15-eq = trans r15-p (r15-eq corr) ; dom-fresh = dom-fresh corr
  ; heap-eq = λ hl live → trans (heap-p hl live) (heap-eq corr hl live)
  ; stack-eq = λ _ () }   -- writeStackSlot 0 ⇒ post stackSlot ≡ 0 ⇒ k < 0 absurd

------------------------------------------------------------------------
-- FRAME POP: `instr-pop-frame` ↔ `mov rsp,rbp; pop rbp`. The abstract is IDENTITY
-- ("frame restoration is external"). At a well-formed frame teardown the callee's
-- slots are already freed (stackSlot ≡ 0), so the bounded stack-eq post is VACUOUS
-- — no callee slots to re-anchor across the rsp restore. `pop` only READS memory,
-- so heap-eq copies through with NO disjointness. The 4 tracked regs (rdi/rsi/rax/
-- rbx) are untouched (mov/pop hit only rsp/rbp). Parametric over the post + facts,
-- exactly like sim-push-frame; only the vacuous stack-eq is proved here.
------------------------------------------------------------------------
sim-pop-frame : {hv : HeapView} (fs : FlatState) (s xp : X.State) → FlatCorr hv fs s
  → stackSlot (regs (floc fs)) ≡ 0                 -- WF: frame emptied before pop
  → X.readReg (X.State.regs xp) rdi ≡ X.readReg (X.State.regs s) rdi
  → X.readReg (X.State.regs xp) rsi ≡ X.readReg (X.State.regs s) rsi
  → X.readReg (X.State.regs xp) rax ≡ X.readReg (X.State.regs s) rax
  → X.readReg (X.State.regs xp) rbx ≡ X.readReg (X.State.regs s) rbx
  → X.State.halted xp ≡ X.State.halted s
  → X.readReg (X.State.regs xp) r15 ≡ X.readReg (X.State.regs s) r15
  → (∀ hl → HDom hv hl → X.readMem (X.State.memory xp) (haddr hv hl)
                                  ≡ X.readMem (X.State.memory s) (haddr hv hl))
  → FlatCorr hv (flat-exec-instr instr-pop-frame [] fs) xp
sim-pop-frame {hv} fs s xp corr ss0 rdi-p rsi-p rax-p rbx-p halt-p r15-p heap-p = record
  { rdi-eq = trans rdi-p (rdi-eq corr) ; rsi-eq = trans rsi-p (rsi-eq corr)
  ; rax-eq = trans rax-p (rax-eq corr) ; rbx-eq = trans rbx-p (rbx-eq corr)
  ; halt-eq = trans halt-p (halt-eq corr) ; r15-eq = trans r15-p (r15-eq corr) ; dom-fresh = dom-fresh corr
  ; heap-eq = λ hl live → trans (heap-p hl live) (heap-eq corr hl live)
  ; stack-eq = λ k k<ss → ⊥-elim (bad k k<ss) }
  where
    bad : ∀ k → k < stackSlot (regs (floc fs)) → ⊥
    bad k k<ss with subst (k <_) ss0 k<ss
    ... | ()

------------------------------------------------------------------------
-- LOAD CONST (int): `instr-load-const fits-int v` (Output := SV-Lit fits-int v)
-- ↔ `mov rax, imm v`. With enc-sv(SV-Lit fits-int v) = v, the loaded immediate
-- matches the encoded literal exactly, so rax-eq is refl; nothing else changes
-- (writeReg Output preserves the other regs / stack / heap / halt).
------------------------------------------------------------------------
sim-load-const : {hv : HeapView} (v : Carrier) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-const fits-int v) [] fs)
             (mkstate (xwriteReg (xregs s) rax (lit-word v)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-const {hv} v fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- LOAD CODE ADDR: `instr-load-code-addr n` (Output := SV-Code n) ↔ `lea rax,
-- [rip+label n]`. The x86 effective address of a label is `n` (linker-resolved,
-- abstract), and enc-sv(SV-Code n) = n, so rax := n matches — rax-eq is refl.
------------------------------------------------------------------------
sim-load-code-addr : {hv : HeapView} (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-code-addr n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-code-addr {hv} n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- SAVE CLOSURE REG: `instr-save-closure-reg` ↔ `mov r12, rdi`. Abstract identity;
-- x86 writes r12 (the reserved closure pointer), which FlatCorr does NOT track —
-- so the whole correspondence is unchanged. Only the fpc bumps.
------------------------------------------------------------------------
sim-save-closure-reg : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr instr-save-closure-reg [] fs)
             (mkstate (xwriteReg (xregs s) r12 (xreadReg (xregs s) rdi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-save-closure-reg {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Arithmetic reg-ops (Plan 0.34: flag-free, so the post is parametric over
-- the x86 flags). input2-inc / scratch-dec increment/decrement a TAG.
------------------------------------------------------------------------
inc-enc : ∀ {hv : HeapView} (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k → enc-sv hv v + 1 ≡ enc-sv hv (sv-succ v)
inc-enc .(SV-Tag k) k refl = +-comm k 1

dec-enc : ∀ {hv : HeapView} (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k → enc-sv hv v ∸ 1 ≡ enc-sv hv (sv-pred v)
dec-enc .(SV-Tag zero)    zero    refl = refl
dec-enc .(SV-Tag (suc m)) (suc m) refl = refl

sim-reg-input2-inc : {hv : HeapView} (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input2 ≡ SV-Tag k
  → FlatCorr hv (flat-exec-instr (instr-reg-op input2-inc) [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rsi + 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-input2-inc {hv} k newFlags fs s corr i2-eq = record
  { rdi-eq = rdi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; rsi-eq = trans (cong (_+ 1) (rsi-eq corr)) (inc-enc (readReg (regs (floc fs)) Input2) k i2-eq)
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

sim-reg-scratch-dec : {hv : HeapView} (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-dec) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rbx ∸ 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-scratch-dec {hv} k newFlags fs s corr sc-eq = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr
  ; rbx-eq = trans (cong (_∸ 1) (rbx-eq corr)) (dec-enc (readReg (regs (floc fs)) Scratch) k sc-eq)
  ; halt-eq = halt-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; heap-eq = heap-eq corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- HEAP ALLOCATION: `instr-alloc-heap n` ↔ `mov rax, r15 ; add r15, n*8`.
--
-- THE step the carried view exists for. The abstract allocator hands out block
-- `st = next-heap-ref` — an ID carrying NO address; the concrete bump allocator
-- puts that block at the current frontier `%r15`. So the post-state correspondence
-- is at the EXTENDED view: the fresh block's cells map to `hfront + 8·offset`, the
-- frontier moves to `hfront + 8·n`, and every previously-mapped cell KEEPS its
-- address (its ref-id is below `st`, by `dom-fresh`) — a genuine memory-injection
-- EXTENSION, not a re-choice.
------------------------------------------------------------------------

-- The extended address map, aux-style on the ref decision so downstream proofs
-- reduce it by feeding the `Dec` (a `with` would not reduce under the callers).
ext-addr-aux : (hv : HeapView) (hl : HeapLocation) (st : ℕ)
             → Dec (ref-id (heap-ref hl) ≡ st) → ℕ
ext-addr-aux hv hl st (yes _) = hfront hv + slot-to-disp (heap-offset hl)
ext-addr-aux hv hl st (no  _) = haddr hv hl

ext-addr : (hv : HeapView) (st : ℕ) → HeapLocation → ℕ
ext-addr hv st hl = ext-addr-aux hv hl st (ref-id (heap-ref hl) ≟ st)

-- The extended domain: the old cells, plus the fresh block's `n` in-bounds slots.
data ExtDom (hv : HeapView) (st n : ℕ) (hl : HeapLocation) : Set where
  ext-old   : HDom hv hl → ExtDom hv st n hl
  ext-fresh : ref-id (heap-ref hl) ≡ st → heap-offset hl < n → ExtDom hv st n hl

-- Below the fresh ref the map is UNCHANGED — this is what makes it an extension.
ext-addr-old : ∀ (hv : HeapView) (st : ℕ) (hl : HeapLocation)
             → ref-id (heap-ref hl) < st → ext-addr hv st hl ≡ haddr hv hl
ext-addr-old hv st hl lt = go (ref-id (heap-ref hl) ≟ st)
  where go : ∀ (d : Dec (ref-id (heap-ref hl) ≡ st)) → ext-addr-aux hv hl st d ≡ haddr hv hl
        go (yes p) = ⊥-elim (<-irrefl p lt)
        go (no  _) = refl

-- … and AT the fresh ref it is the frontier-relative layout.
ext-addr-fresh : ∀ (hv : HeapView) (st : ℕ) (hl : HeapLocation) → ref-id (heap-ref hl) ≡ st
               → ext-addr hv st hl ≡ hfront hv + slot-to-disp (heap-offset hl)
ext-addr-fresh hv st hl req = go (ref-id (heap-ref hl) ≟ st)
  where go : ∀ (d : Dec (ref-id (heap-ref hl) ≡ st))
           → ext-addr-aux hv hl st d ≡ hfront hv + slot-to-disp (heap-offset hl)
        go (yes _) = refl
        go (no  p) = ⊥-elim (p req)

-- The fresh block's BASE sits exactly at the frontier — the equation `rax-eq`
-- rides at the allocation step.
ext-addr-base : ∀ (hv : HeapView) (st : ℕ)
              → ext-addr hv st (heap-loc (mkHeapRef st) 0) ≡ hfront hv
ext-addr-base hv st =
  trans (ext-addr-fresh hv st (heap-loc (mkHeapRef st) 0) refl) (+-comm (hfront hv) 0)

-- m + k is never < m — the frontier-ordering fact the extension laws lean on.
+-not-< : ∀ (m k : ℕ) → m + k < m → ⊥
+-not-< m k lt = <-irrefl refl (<-transʳ (m≤m+n m k) lt)

ext-suc-aux : ∀ (hv : HeapView) (st : ℕ) (r : HeapRef) (o : ℕ)
              (d : Dec (ref-id r ≡ st))
            → ext-addr-aux hv (heap-loc r (suc o)) st d
              ≡ ext-addr-aux hv (heap-loc r o) st d + slot-size
ext-suc-aux hv st r o (yes _) =
  trans (cong (hfront hv +_) (+-comm slot-size (o * slot-size)))
        (sym (+-assoc (hfront hv) (o * slot-size) slot-size))
ext-suc-aux hv st r o (no  _) = haddr-suc hv (heap-loc r o)

ext-suc : ∀ (hv : HeapView) (st : ℕ) (hl : HeapLocation)
        → ext-addr hv st (sucHL hl) ≡ ext-addr hv st hl + slot-size
ext-suc hv st (heap-loc r o) = ext-suc-aux hv st r o (ref-id r ≟ st)

-- THE EXTENDED VIEW. `fresh` (every mapped cell's ref-id is below the fresh ref —
-- FlatCorr's `dom-fresh`) is what keeps the extension injective: old cells stay
-- put BELOW the frontier, the new block starts AT it.
extend-view : (hv : HeapView) (st n : ℕ)
            → (∀ {hl : HeapLocation} → HDom hv hl → ref-id (heap-ref hl) < st)
            → HeapView
extend-view hv st n fresh = record
  { haddr     = ext-addr hv st
  ; HDom      = ExtDom hv st n
  ; hfront    = hfront hv + slots n
  ; haddr-suc = ext-suc hv st
  ; haddr-inj = inj
  ; dom-below = below
  }
  where
    below : ∀ {hl : HeapLocation} → ExtDom hv st n hl → ext-addr hv st hl < hfront hv + slots n
    below {hl} (ext-old d) =
      subst (_< hfront hv + slots n) (sym (ext-addr-old hv st hl (fresh d)))
            (<-transˡ (dom-below hv d) (m≤m+n (hfront hv) (slots n)))
    below {hl} (ext-fresh req o<n) =
      subst (_< hfront hv + slots n) (sym (ext-addr-fresh hv st hl req))
            (+-monoʳ-< (hfront hv) (*-monoˡ-< slot-size o<n))
    -- old ↔ fresh can never collide: the old address is BELOW the frontier, the
    -- fresh one is at-or-above it.
    cross : ∀ (a b : HeapLocation) → HDom hv a → ref-id (heap-ref b) ≡ st
          → ext-addr hv st a ≡ ext-addr hv st b → ⊥
    cross a b da rb eq =
      +-not-< (hfront hv) (slot-to-disp (heap-offset b))
        (subst (_< hfront hv)
               (trans (sym (ext-addr-old hv st a (fresh da))) (trans eq (ext-addr-fresh hv st b rb)))
               (dom-below hv da))
    inj : ∀ {a b : HeapLocation} → ExtDom hv st n a → ExtDom hv st n b
        → ext-addr hv st a ≡ ext-addr hv st b → a ≡ b
    inj {a} {b} (ext-old da) (ext-old db) eq =
      haddr-inj hv da db
        (trans (sym (ext-addr-old hv st a (fresh da)))
               (trans eq (ext-addr-old hv st b (fresh db))))
    inj {a} {b} (ext-old da)        (ext-fresh rb _) eq = ⊥-elim (cross a b da rb eq)
    inj {a} {b} (ext-fresh ra _)    (ext-old db)     eq = ⊥-elim (cross b a db ra (sym eq))
    inj {heap-loc ra oa} {heap-loc rb ob} (ext-fresh ra≡ _) (ext-fresh rb≡ _) eq =
      cong₂ heap-loc (cong mkHeapRef (trans ra≡ (sym rb≡))) off-eq
      where
        addr-eq : hfront hv + slot-to-disp oa ≡ hfront hv + slot-to-disp ob
        addr-eq = trans (sym (ext-addr-fresh hv st (heap-loc ra oa) ra≡))
                        (trans eq (ext-addr-fresh hv st (heap-loc rb ob) rb≡))
        off-eq : oa ≡ ob
        off-eq = *-cancelʳ-≡ oa ob slot-size
                   (+-cancelˡ-≡ (hfront hv) (slot-to-disp oa) (slot-to-disp ob) addr-eq)

-- "NO FORWARD POINTERS" (`sv-below`, from `Once.CCC.Machine.FlatStoreWF`): a
-- stored value never references a block the abstract allocator has not handed
-- out yet. This is the store-WF side-condition the extension needs — the only
-- values whose ENCODING an extension could move are pointers into the fresh
-- ref, and a well-formed flat state has none (`FlatStoreWF.flat-wf-step`).

-- Encoding stability across the extension, for every value that is below the
-- fresh ref: the extension only ADDS addresses.
enc-ext : ∀ (hv : HeapView) (st n : ℕ)
            (pf : ∀ {hl : HeapLocation} → HDom hv hl → ref-id (heap-ref hl) < st)
            (v : StoredValue FS) → sv-below st v
        → enc-sv (extend-view hv st n pf) v ≡ enc-sv hv v
enc-ext hv st n pf (SV-Ptr (AtDynamic hl)) lt = ext-addr-old hv st hl lt
enc-ext hv st n pf (SV-Ptr (AtStack _ _))  _  = refl
enc-ext hv st n pf (SV-Tag _)              _  = refl
enc-ext hv st n pf (SV-Lit fits-int v)     _  = refl
enc-ext hv st n pf (SV-Lit fits-float v)   _  = refl
enc-ext hv st n pf (SV-Code _)             _  = refl

enc-ext-maybe : ∀ (hv : HeapView) (st n : ℕ)
                  (pf : ∀ {hl : HeapLocation} → HDom hv hl → ref-id (heap-ref hl) < st)
                  (mv : Maybe (StoredValue FS)) → svm-below st mv
              → enc-maybe (extend-view hv st n pf) mv ≡ enc-maybe hv mv
enc-ext-maybe hv st n pf (just v) wf = cong just (enc-ext hv st n pf v wf)
enc-ext-maybe hv st n pf nothing  _  = refl


-- THE ALLOCATION STEP. The abstract `instr-alloc-heap n` writes a fresh
-- `SV-Ptr (AtDynamic (block st))` to Output and bumps the block counter; the x86
-- `mov rax, r15 ; add r15, n*8` writes the frontier to rax and bumps it. The post
-- correspondence is at the EXTENDED view, where the fresh block sits exactly at
-- the old frontier — so `rax-eq` is `r15-eq` transported by `ext-addr-base`.
-- The store-WF premises are what make the extension INVISIBLE to everything else
-- (no live value referenced the not-yet-allocated ref).
sim-alloc-heap : ∀ {hv : HeapView} (n : ℕ) (newFlags : X.Flags) (newPc : ℕ)
                 (fs : FlatState) (s : X.State) (corr : FlatCorr hv fs s)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input1)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input2)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Scratch)
  → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
  → (∀ k → k < stackSlot (regs (floc fs))
         → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) (current-frame (falloc fs)) k))
  → (∀ hl → ref-id (heap-ref hl) ≡ next-heap-ref (falloc fs) → heapMem (floc fs) hl ≡ nothing)
  → (∀ i → i < n → X.readMem (memory s) (hfront hv + slot-to-disp i) ≡ nothing)
  → FlatCorr (extend-view hv (next-heap-ref (falloc fs)) n (dom-fresh corr))
             (flat-exec-instr (instr-alloc-heap n) [] fs)
             (mkstate (xwriteReg (xwriteReg (xregs s) rax (X.readReg (xregs s) r15)) r15
                                 (X.readReg (xregs s) r15 + slots n))
                      (memory s) newFlags newPc (xhalted s))
sim-alloc-heap {hv} n newFlags newPc fs s corr wf1 wf2 wfs wf-heap wf-stack fresh-abs fresh-x86 = record
  { rdi-eq  = trans (rdi-eq corr) (sym (enc-ext hv st n dfr (readReg (regs (floc fs)) Input1) wf1))
  ; rsi-eq  = trans (rsi-eq corr) (sym (enc-ext hv st n dfr (readReg (regs (floc fs)) Input2) wf2))
  ; rax-eq  = trans (r15-eq corr) (sym (ext-addr-base hv st))
  ; rbx-eq  = trans (rbx-eq corr) (sym (enc-ext hv st n dfr (readReg (regs (floc fs)) Scratch) wfs))
  ; halt-eq = halt-eq corr
  ; r15-eq  = cong (_+ slots n) (r15-eq corr)
  ; dom-fresh = df
  ; heap-eq = hp
  ; stack-eq = λ k k< → trans (stack-eq corr k k<)
                              (sym (enc-ext-maybe hv st n dfr
                                     (stackMem (floc fs) (current-frame (falloc fs)) k)
                                     (wf-stack k k<)))
  }
  where
    st  = next-heap-ref (falloc fs)
    dfr = dom-fresh corr
    hv' = extend-view hv st n dfr
    df : ∀ {hl : HeapLocation} → ExtDom hv st n hl → ref-id (heap-ref hl) < suc st
    df (ext-old d)       = m<n⇒m<1+n (dfr d)
    df (ext-fresh req _) = subst (_< suc st) (sym req) ≤-refl
    hp : ∀ (hl : HeapLocation) → ExtDom hv st n hl
       → X.readMem (memory s) (ext-addr hv st hl) ≡ enc-maybe hv' (heapMem (floc fs) hl)
    hp hl (ext-old d) =
      trans (cong (X.readMem (memory s)) (ext-addr-old hv st hl (dfr d)))
            (trans (heap-eq corr hl d)
                   (sym (enc-ext-maybe hv st n dfr (heapMem (floc fs) hl) (wf-heap hl d))))
    hp hl (ext-fresh req off<n) =
      trans (cong (X.readMem (memory s)) (ext-addr-fresh hv st hl req))
            (trans (fresh-x86 (heap-offset hl) off<n)
                   (sym (cong (enc-maybe hv') (fresh-abs hl req))))
