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

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.CCC.Target.X86-64.Syntax using (slot-size)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.Word using (Carrier)
open import Once.Type using (Int; Float; fits-int; fits-float)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.FlatCorrespondence
  (FS : FrameSemantics)
  -- The frame semantics' slot size IS this target's (`refl` at instantiation).
  -- Ties the abstract `slot-addr f k = frame-base f + k · frame-word` to the
  -- emitted `[rsp + slot-to-disp k]`.
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Nat using (zero; suc; _+_; _∸_; _*_; _≡ᵇ_; _≟_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; +-assoc; +-cancelˡ-≡; *-cancelʳ-≡; n∸n≡0
                                      ; m≤m+n; <-irrefl; <-trans; <-transʳ; <-transˡ
                                      ; +-monoʳ-<; *-monoˡ-<; ≤-refl; ≤-trans; m<n⇒m<1+n
                                      ; m+n≤o⇒m≤o∸n; <⇒≢)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; Dec)
open import Data.List using ([])
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

open import Once.Memory.HeapAddress
  using (HeapRef; sucHL; heap-loc; mkHeapRef; heap-ref; heap-offset; ref-id; _≟HL_)
import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; mkflags; _<ᵇ_; writeMem)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (rax; rbx; rsi; rdi; rsp; r12; r14; r15; slots)
open import Once.CCC.Target.X86-64.AbstractToX86 using (slot-to-disp)
open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeLocToStack; writeHeapMem
                       ; readLoc; writeLoc-read-same-stack; writeLoc-preserves-other)
open ExecFinal {FS} using (exec-load-via-resolved; exec-load-suc-via-resolved; exec-load-with-value
                          ; exec-store-via-resolved; exec-store-suc-via-resolved)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open FrameSemantics FS using (shift-frame)

open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below)
open AbstractExec {FS} using (exec-abstract; exec-load-from-slot-with-value; exec-restore-input-with-value)
open FrameSemantics FS using (Frame; frame-base; slot-addr; slot-addr-linear; shift-base; frame-word)

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
    -- THE STACK HIGH-WATER MARK (plan 0.54 rung D step 3): the LOWEST address
    -- `%rsp` has ever held. So the view is not only the heap injection any more —
    -- it is the whole MEMORY layout: `[hfront, lo)` is the region NO ONE has ever
    -- touched (`FlatCorr.untouched`), which is what makes an allocation's cells
    -- genuinely unwritten on the concrete side.
    --
    -- Why a high-water mark and not simply `%rsp`: DEAD MEMORY KEEPS ITS
    -- CONTENTS. A deep call that returns leaves written cells below the current
    -- `%rsp`, so "everything below `%rsp` is unmapped" is false, and the heap
    -- bumping into that region would break `heap-eq` at the fresh cells. `lo`
    -- only ever DECREASES (it is lowered by the two %rsp-lowering instructions,
    -- `descend-view`), so `untouched` only ever weakens — no write can invalidate
    -- it, which is exactly why it is an invariant and not an assumption.
    lo       : ℕ
    -- The heap has never reached the virgin region either: `hfront ≤ lo`, the
    -- layout separation, now stated INSIDE the view (with `FlatCorr.lo-le`,
    -- `lo ≤ %rsp`, it gives the old `sep` — see the derived `sep` below).
    front-lo : hfront ≤ lo
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

-- THE ENCODING IS A FUNCTION OF THE ADDRESS MAP ALONE, and it says so: the
-- matching definition takes an `AddrMap`, and the view-level name is a one-clause
-- projection wrapper. That is not cosmetic — it is what keeps the correspondence
-- STABLE under view fields the encoding does not read.
--
-- Why it matters: `enc-sv hv v` on a VARIABLE `v` is stuck, and Agda compares
-- stuck applications ARGUMENT-WISE. With the view passed whole, adding any field
-- (the step-3 high-water mark `lo`, or tomorrow's stack-memory keys) made
-- `enc-sv hv' v` and `enc-sv hv v` non-convertible even when `haddr hv' ≡ haddr hv`
-- BY DEFINITION, and every affected field of every affected `sim-*` needed a
-- transport lemma. Through the wrapper both sides unfold to
-- `enc-sv-at (haddr hv) v` — the same term — so a view change the map survives is
-- INVISIBLE, with no lemma and no per-field boilerplate.
AddrMap : Set
AddrMap = HeapLocation → ℕ

enc-sv-at : AddrMap → StoredValue FS → X.Word
enc-sv-at am (SV-Tag n)                = n
enc-sv-at am (SV-Ptr (AtDynamic hl))   = am hl
-- Plan 0.61: a stack pointer is the SLOT'S ADDRESS. This is only meaningful
-- because frames now move with %rsp (`Machine.Flat`) — with the old model the
-- callee's slot k and its caller's slot k were the same abstract cell, so no
-- address could be assigned and this was a (false) `0`.
enc-sv-at am (SV-Ptr (AtStack f k))    = slot-addr f k
-- A register-fittable INT literal encodes to its own value — exactly the immediate
-- `compile-const fits-int v = mov rax, v` loads (so load-const's rax-eq is refl and
-- literal values flow through FlatCorr instead of collapsing to 0). Float is
-- unimplemented (`compile-const fits-float` traps to ud2), so it gets no register
-- correspondence — encode 0.
-- ENUMERATED (no catch-all): a `SV-Lit _ _` catch-all does not survive the
-- case-tree translation, so `enc-sv-at am (SV-Lit fits-float v)` would not reduce
-- and the extension-stability lemma below could not be stated by `refl`.
enc-sv-at am (SV-Lit fits-int v)       = lit-word v
enc-sv-at am (SV-Lit fits-float v)     = 0
enc-sv-at am (SV-Code n)               = n

enc-maybe-at : AddrMap → Maybe (StoredValue FS) → Maybe X.Word
enc-maybe-at am (just v) = just (enc-sv-at am v)
enc-maybe-at am nothing  = nothing

-- The view-level names every proof uses: one clause each, so they UNFOLD during
-- conversion checking and the comparison lands on the address map.
enc-sv : HeapView → StoredValue FS → X.Word
enc-sv hv = enc-sv-at (haddr hv)

enc-maybe : HeapView → Maybe (StoredValue FS) → Maybe X.Word
enc-maybe hv = enc-maybe-at (haddr hv)

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
    -- THE TALLY (plan 0.54 D item 4): `%r14` IS the `Count` register. Without
    -- this field the correspondence would say NOTHING about the counter, and the
    -- choice of physical register in `compile-abstract` would not be checked by
    -- anything — the tally lowering could name any register and still typecheck.
    -- With it, every block step must re-establish it, so a wrong register in the
    -- codegen is a TYPE ERROR here.
    r14-eq  : X.readReg (X.State.regs s) r14 ≡ enc-sv hv (readReg (regs (floc fs)) Count)
    halt-eq : X.State.halted s ≡ halted (floc fs)
    -- THE STACK ANCHOR (plan 0.61): `%rsp` IS the current frame's base. Frames
    -- move with the stack pointer, so this holds at every step — and it is what
    -- gives a stack POINTER its address (`enc-sv (SV-Ptr (AtStack f k))`).
    rsp-eq  : X.readReg (X.State.regs s) rsp ≡ frame-base (current-frame (falloc fs))
    -- THE FRONTIER: `%r15` (the bump allocator's heap top) IS the view's frontier.
    -- This is what makes the next `instr-alloc-heap` provable: the fresh block's
    -- address is read off the concrete machine, not predicted from the abstract state.
    r15-eq  : X.readReg (X.State.regs s) r15 ≡ hfront hv
    -- Every mapped cell belongs to a block the ABSTRACT allocator has handed out
    -- (ref-id below the abstract counter). Together with `dom-below` this is what
    -- makes the next allocation fresh on BOTH sides.
    dom-fresh : ∀ {hl : HeapLocation} → HDom hv hl →
                ref-id (heap-ref hl) < next-heap-ref (falloc fs)
    -- THE CONVERSE COVERAGE (2026-07-30 vacuity fix): every cell the abstract
    -- machine has WRITTEN is in the view's domain. Without it the domain could be
    -- empty while the abstract heap holds data — `heap-eq` only constrains cells
    -- IN the domain — and then "the cell I am about to dereference is mapped" is
    -- simply FALSE. That was `load-indirect-live` / `-suc-live` /
    -- `store-indirect{,-suc}-live`, four postulates whose heap view was
    -- UNIVERSALLY QUANTIFIED and tied to nothing: instantiating them at a view
    -- with `HDom = λ _ → ⊥` derived `⊥` (probed 2026-07-30). They are now
    -- PROJECTIONS of this field, which every step re-establishes.
    dom-written : ∀ (hl : HeapLocation) {w : StoredValue FS}
                → heapMem (floc fs) hl ≡ just w → HDom hv hl
    -- IN-BOUNDS COVERAGE (2026-07-30 vacuity fix, the store side): every cell
    -- WITHIN an allocated block's size is mapped, whether or not it has been
    -- written yet. A store's target is exactly such a cell (the block was just
    -- allocated), so `store-indirect{,-suc}-live` reduce to a STATE-ONLY
    -- in-bounds fact — no view left to instantiate adversarially, which is what
    -- made those two postulates false for any view.
    -- Maintained by `extend-view` alone: the fresh block enters with all `n` of
    -- its cells (`ext-fresh`), and `AllocState.block-size` records the same `n`.
    dom-sized : ∀ (hl : HeapLocation)
              → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
              → HDom hv hl
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
    -- THE LAYOUT SEPARATION (plan 0.54 rung D): the heap frontier is at or below
    -- the stack pointer. The heap grows UP from its base (`add r15, n*8`) and the
    -- stack grows DOWN (`sub rsp, n*8`), so this single carried inequality is the
    -- whole of heap/stack disjointness: a live cell is BELOW the frontier
    -- (`dom-below`), hence below `%rsp`, hence below every slot address
    -- `%rsp + 8k`. No maximum stack depth and no concrete addresses are needed —
    -- only the two allocating instructions have to re-establish it, which is
    -- exactly where memory exhaustion lives.
    --
    -- Step 3 splits it in two through the high-water mark: `hfront ≤ lo` is a law
    -- of the view (`front-lo`) and `lo ≤ %rsp` is this field. The derived
    -- composite is the top-level `sep` below, so every disjointness consumer is
    -- unchanged.
    lo-le : lo hv ≤ X.readReg (X.State.regs s) rsp
    -- THE VIRGIN REGION (plan 0.54 rung D step 3): between the heap frontier and
    -- the deepest `%rsp` ever reached, the concrete memory is UNMAPPED. This is
    -- what an allocation's freshness rests on: the `n` words at the frontier are
    -- in this region (by the site's room premise), so they read as `nothing` —
    -- previously the postulate `alloc-heap-fresh-x86`, now a consequence.
    --
    -- It is preserved by every step because every WRITE lands outside the region:
    -- a heap write is at a mapped cell (`dom-below` ⇒ below `hfront`), a stack
    -- write is at `%rsp + 8k ≥ %rsp ≥ lo`, and the two instructions that lower
    -- `%rsp` lower `lo` with it (`descend-view`) BEFORE writing.
    untouched : ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
              → X.readMem (X.State.memory s) a ≡ nothing
    stack-eq : ∀ (k : Slot) → k < stackSlot (regs (floc fs)) →
              X.readMem (X.State.memory s) (X.readReg (X.State.regs s) rsp + slot-to-disp k)
              ≡ enc-maybe hv (stackMem (floc fs) (current-frame (falloc fs)) k)
open FlatCorr public

-- THE LAYOUT SEPARATION, derived: the heap frontier is at or below `%rsp`,
-- through the high-water mark (`front-lo` then `lo-le`). Every heap/stack
-- disjointness consumer uses THIS — the field it replaces had the same type.
sep : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
    → FlatCorr hv fs s → hfront hv ≤ X.readReg (X.State.regs s) rsp
sep {hv} corr = ≤-trans (front-lo hv) (lo-le corr)

-- THE VIRGIN REGION, LOWERED (plan 0.54 rung D step 3). `%rsp` descending below
-- the high-water mark moves the mark down with it; everything else about the view
-- (the address map, the domain, the frontier) is UNCHANGED, so `enc-sv` and
-- `HDom` are definitionally the same at the descended view and every other
-- `FlatCorr` field transports verbatim.
--
-- Lowering is a WEAKENING of `untouched` (a smaller region), which is why no
-- write can break it and why the descending instructions can write below the old
-- `%rsp` at all: they descend first, then write inside `[lo', %rsp)`.
descend-view : (hv : HeapView) (lo' : ℕ) → lo' ≤ lo hv → hfront hv ≤ lo' → HeapView
descend-view hv lo' _ front-lo' = record
  { haddr     = haddr hv
  ; HDom      = HDom hv
  ; hfront    = hfront hv
  ; haddr-suc = haddr-suc hv
  ; haddr-inj = haddr-inj hv
  ; dom-below = dom-below hv
  ; lo        = lo'
  ; front-lo  = front-lo'
  }

-- (No encoding-transport lemma is needed across a descent: `descend-view` copies
-- `haddr` verbatim, and the encoding is a function of the map alone — `enc-sv`
-- unfolds to `enc-sv-at (haddr hv)` on both sides. That is the whole reason the
-- wrapper above exists.)

-- `untouched` at the descended view: the region only shrank.
untouched-descend : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
                      (lo' : ℕ) (le : lo' ≤ lo hv) (fl : hfront hv ≤ lo')
                    (corr : FlatCorr hv fs s)
                  → ∀ (a : ℕ) → hfront hv ≤ a → a < lo'
                  → X.readMem (X.State.memory s) a ≡ nothing
untouched-descend lo' le fl corr a fa a<lo' = untouched corr a fa (<-transˡ a<lo' le)

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
  ; r14-eq  = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = heap-eq corr
  ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-to-input [] fs)
             (mkstate (xwriteReg (xregs s) rdi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-to-input {hv} fs s corr = record
  { rdi-eq = rax-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- mov-input2-to-output (Output := Input2) ↔ `mov rax, rsi`.
sim-mov-input2-to-output : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-input2-to-output [] fs)
             (mkstate (xwriteReg (xregs s) rax (xreadReg (xregs s) rsi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-input2-to-output {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rsi-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- mov-output-to-input2 (Input2 := Output) ↔ `mov rsi, rax`.
sim-mov-output-to-input2 : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr mov-output-to-input2 [] fs)
             (mkstate (xwriteReg (xregs s) rsi (xreadReg (xregs s) rax)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-mov-output-to-input2 {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rax-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n ⟹ rax-eq=refl.
sim-load-tag-lit : {hv : HeapView} (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-tag-lit n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-tag-lit {hv} n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`. rbx-eq=refl.
sim-reg-scratch-one : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-one) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 1) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-one {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`. rbx-eq=refl.
sim-reg-scratch-zero : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-zero) [] fs)
             (mkstate (xwriteReg (xregs s) rbx 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-zero {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = refl ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- instr-reg-op count-zero (Count := SV-Tag 0) ↔ `mov r14, 0`. r14-eq=refl.
-- Plan 0.54 D item 4: the tally register, NOT rsi — `rsi-eq` is now UNTOUCHED
-- here, which is the whole point: zeroing the counter no longer disturbs the
-- ABI's second argument register.
sim-reg-count-zero : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op count-zero) [] fs)
             (mkstate (xwriteReg (xregs s) r14 0) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-count-zero {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = refl
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- instr-reg-op scratch-load-count (Scratch := Count) ↔ `mov rbx, r14`. rbx-eq=r14-eq.
sim-reg-scratch-load-count : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-load-count) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) r14)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-reg-scratch-load-count {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = r14-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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

-- (Over the ADDRESS MAP, like the other encoding lemmas: a `{hv}` used only under
-- `enc-sv`/`haddr` cannot be inferred — see the note at `enc-sv-at`.)
enc-zero : ∀ {am : AddrMap} (v : StoredValue FS) (n : ℕ) → v ≡ SV-Tag n → (enc-sv-at am v ≡ᵇ 0) ≡ sv-is-zero v
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
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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

-- A write OUTSIDE the virgin region leaves it virgin (plan 0.54 rung D step 3).
-- The `≢` is what each writing instruction supplies: a heap write is below the
-- frontier (`dom-below`), a stack write is at or above `lo` (`lo-le`).
untouched-write : ∀ (mem : X.Memory) (waddr v' a : ℕ) → (a ≡ waddr → ⊥)
                → X.readMem mem a ≡ nothing
                → X.readMem (writeMem mem waddr v') a ≡ nothing
untouched-write mem waddr v' a ≢w pre rewrite ≢→≡ᵇfalse ≢w = pre

-- A HEAP store misses the virgin region: its target is a mapped cell, hence
-- strictly below the frontier, hence below every address the region contains.
untouched-heap-store : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
                         (hl : HeapLocation) (v' : X.Word) → HDom hv hl → FlatCorr hv fs s
                     → ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
                     → X.readMem (writeMem (memory s) (haddr hv hl) v') a ≡ nothing
untouched-heap-store {hv} {fs} {s} hl v' d corr a fa a<lo =
  untouched-write (memory s) (haddr hv hl) v' a
    (λ eq → <-irrefl refl (<-transˡ (subst (_< hfront hv) (sym eq) (dom-below hv d)) fa))
    (untouched corr a fa a<lo)

-- A STACK store misses it from the other side: its target is at or above `lo`
-- (`%rsp + 8k ≥ %rsp ≥ lo`), and the region stops strictly below `lo`.
untouched-stack-store : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
                          (waddr : ℕ) (v' : X.Word) → lo hv ≤ waddr → FlatCorr hv fs s
                      → ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
                      → X.readMem (writeMem (memory s) waddr v') a ≡ nothing
untouched-stack-store {hv} {fs} {s} waddr v' lo≤w corr a fa a<lo =
  untouched-write (memory s) waddr v' a (<⇒≢ (<-transˡ a<lo lo≤w)) (untouched corr a fa a<lo)

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

-- COVERAGE under a HEAP store (2026-07-30 vacuity fix): the written cell is in the
-- domain by the store's own liveness premise, every other cell is unchanged. Same
-- `with hl ≟HL hl'` shape as `store-heap-eq` (writeHeapMem is with-free, so the
-- decision reduces it).
store-dom-written : ∀ (hv : HeapView) (hl : HeapLocation) (v : StoredValue FS) (ls : LocState FS)
  → HDom hv hl
  → (∀ (hl' : HeapLocation) {w : StoredValue FS} → heapMem ls hl' ≡ just w → HDom hv hl')
  → ∀ (hl' : HeapLocation) {w : StoredValue FS}
  → writeHeapMem (heapMem ls) hl v hl' ≡ just w → HDom hv hl'
store-dom-written hv hl v ls live pre hl' eq with hl ≟HL hl'
... | yes refl = live
... | no ¬p    = pre hl' eq

-- STACK preservation under a HEAP store: writing the x86 memory at heap
-- address `addr` (= `haddr hv hl`) leaves every current-frame stack slot value
-- unchanged, GIVEN heap/stack disjointness (`disj`: no current-frame slot
-- aliases the heap write target). The abstract `stackMem` is untouched by a
-- heap write, so the current-frame stack correspondence is preserved — the
-- rsp-relative analogue of `store-heap-eq`'s no-alias branch. `stk` is the
-- current frame's slot→value slice (`stackMem ls (current-frame …)`).
store-stack-eq : ∀ {am : AddrMap} (addr : ℕ) (v' : X.Word) (s : X.State) (stk : Slot → Maybe (StoredValue FS)) (bound : ℕ)
  → (∀ k → k < bound → X.readMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp k) ≡ enc-maybe-at am (stk k))
  → (∀ k → (X.readReg (xregs s) rsp + slot-to-disp k ≡ addr) → ⊥)
  → ∀ k → k < bound → X.readMem (writeMem (memory s) addr v') (X.readReg (xregs s) rsp + slot-to-disp k)
          ≡ enc-maybe-at am (stk k)
store-stack-eq {am} addr v' s stk bound pre disj k k<b rewrite ≢→≡ᵇfalse (disj k) = pre k k<b

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
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; dom-written = store-dom-written hv hl v (floc fs) live-hl (dom-written corr)
      ; dom-sized = dom-sized corr
      ; heap-eq = store-heap-eq hv hl v s (floc fs) live-hl (heap-eq corr)
      ; lo-le = lo-le corr
      ; untouched = untouched-heap-store hl (enc-sv hv v) live-hl corr
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
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; dom-written = store-dom-written hv (sucHL hl) v (floc fs) live-shl (dom-written corr)
      ; dom-sized = dom-sized corr
      ; heap-eq = store-heap-eq hv (sucHL hl) v s (floc fs) live-shl (heap-eq corr)
      ; lo-le = lo-le corr
      ; untouched = untouched-heap-store (sucHL hl) (enc-sv hv v) live-shl corr
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
      { rdi-eq = refl ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
store-slot-stack-eq : ∀ {am : AddrMap} (base : ℕ) (slot : Slot) (Out : StoredValue FS) (s : X.State) (ls : LocState FS) (cf : Frame) (bound : ℕ)
  → (∀ k → k < bound → X.readMem (memory s) (base + slot-to-disp k) ≡ enc-maybe-at am (stackMem ls cf k))
  → ∀ k → k < bound → X.readMem (writeMem (memory s) (base + slot-to-disp slot) (enc-sv-at am Out)) (base + slot-to-disp k)
          ≡ enc-maybe-at am (readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k))
store-slot-stack-eq {am} base slot Out s ls cf bound old k k<b = go (k ≟ slot)
  where go : Dec (k ≡ slot)
           → X.readMem (writeMem (memory s) (base + slot-to-disp slot) (enc-sv-at am Out)) (base + slot-to-disp k)
             ≡ enc-maybe-at am (readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k))
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
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp slot) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; lo-le = lo-le corr
      ; untouched = untouched-stack-store (base + slot-to-disp slot) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp slot))) corr
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
  -- fresh (abstract): the CALLEE frame the reservation moves into is unwritten.
  -- Plan 0.61: the flat machine shifts `current-frame` here, so this is about
  -- the SHIFTED frame — a strictly weaker (and more obviously true) premise
  -- than the old one about the caller's frame.
  → (∀ k → k < n → stackMem (floc fs) (shift-frame (current-frame (falloc fs)) n) k ≡ nothing)
  → (∀ k → k < n → X.readMem (memory s) ((X.readReg (xregs s) rsp ∸ slots n) + slot-to-disp k) ≡ nothing)  -- fresh (x86)
  -- THE DESCENT (plan 0.54 rung D step 3): %rsp drops, so the high-water mark
  -- drops with it. `lo'` is chosen at the dispatch site as `lo hv ⊓ (rsp ∸ 8n)`,
  -- whose `hfront hv ≤ lo'` is where the ROOM premise (`stack-room` — STACK
  -- OVERFLOW, the honest exhaustion assumption) is spent. The mark only ever moves
  -- DOWN, so re-entering a frame that was already reached does not (falsely)
  -- re-declare its cells virgin.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) rsp ∸ slots n
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (flat-exec-instr (instr-alloc-stack n) [] fs)
             (mkstate (xwriteReg (xregs s) rsp (X.readReg (xregs s) rsp ∸ slots n))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-alloc-stack {hv} n newFlags fs s corr entry fresh-abs fresh-x86 lo' lo'≤lo front-lo' lo'≤rsp = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr
  -- the reservation moves %rsp DOWN n slots and the frame with it (`shift-base`)
  ; rsp-eq = trans (cong (_∸ slots n) (rsp-eq corr))
                   (trans (cong (λ w → frame-base (current-frame (falloc fs)) ∸ n * w) (sym word-eq))
                          (sym (shift-base (current-frame (falloc fs)) n)))
  ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = heap-eq corr
  ; lo-le = lo'≤rsp
  ; untouched = untouched-descend lo' lo'≤lo front-lo' corr
  ; stack-eq = λ k k<ns → stk k (subst (k <_) (cong (_+ n) entry) k<ns) }
  where
    stk : ∀ k → k < n → X.readMem (memory s) ((X.readReg (xregs s) rsp ∸ slots n) + slot-to-disp k)
            ≡ enc-maybe hv (stackMem (floc fs) (shift-frame (current-frame (falloc fs)) n) k)
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
  -- MATCHED PAIRING (plan 0.61): the frame this epilogue restores is the one the
  -- entry `alloc-stack n` shifted away from, so its base is where %rsp lands.
  → X.readReg (xregs s) rsp + slots n
      ≡ frame-base (current-frame (leave-frame (falloc fs)))
  → FlatCorr hv (flat-exec-instr (instr-dealloc-stack n) [] fs)
             (mkstate (xwriteReg (xregs s) rsp (X.readReg (xregs s) rsp + slots n))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-dealloc-stack {hv} n newFlags fs s corr full restores = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = restores ; r15-eq = r15-eq corr
  -- the epilogue RAISES %rsp, so the high-water mark stays below it — and the mark
  -- itself does NOT move back up: the freed cells keep their contents, which is
  -- exactly the dead memory the mark exists to remember.
  ; lo-le = ≤-trans (lo-le corr) (m≤m+n (X.readReg (xregs s) rsp) (slots n))
  ; untouched = untouched corr
  -- Plan 0.61: the epilogue RESTORES the caller's frame; the move leaves the
  -- allocation frontier alone, so `dom-fresh` only needs transporting.
  ; dom-fresh = λ {hl} d → subst (λ m → ref-id (heap-ref hl) < m)
                                 (sym (leave-frame-heap-ref (falloc fs))) (dom-fresh corr d)
  ; dom-written = dom-written corr
  ; dom-sized = λ hl lt → dom-sized corr hl
                  (subst (λ szs → heap-offset hl < szs (ref-id (heap-ref hl)))
                         (leave-frame-block-size (falloc fs)) lt)
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
  -- plan 0.54 D item 4: the prologue must not clobber the TALLY either. A real
  -- obligation on the caller, not a formality — %r14 is callee-saved precisely so
  -- a call can cross a loop body.
  → X.readReg (X.State.regs xp) r14 ≡ X.readReg (X.State.regs s) r14
  → X.State.halted xp ≡ X.State.halted s
  → X.readReg (X.State.regs xp) r15 ≡ X.readReg (X.State.regs s) r15
  -- plan 0.61: the prologue lands %rsp on the CALLEE frame's base
  → X.readReg (X.State.regs xp) rsp
      ≡ frame-base (shift-frame (current-frame (falloc fs)) (suc n))
  -- THE DESCENT (plan 0.54 rung D step 3), on the POST state like the other
  -- prologue facts: the new frame's base is the new high-water mark. ROOM (stack
  -- overflow — `frame-room`) is spent proving `hfront hv ≤ lo'`, so it is no
  -- longer a separate premise. The prologue WRITES below the old %rsp (the saved
  -- %rbp), which is legitimate precisely because the mark descends first: the
  -- write lands at or above `lo'`, outside the virgin region.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ X.readReg (X.State.regs xp) rsp
  → (∀ (a : ℕ) → hfront hv ≤ a → a < lo'
       → X.readMem (X.State.memory xp) a ≡ X.readMem (X.State.memory s) a)
  → (∀ hl → HDom hv hl → X.readMem (X.State.memory xp) (haddr hv hl)
                                  ≡ X.readMem (X.State.memory s) (haddr hv hl))
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (flat-exec-instr (instr-push-frame n) [] fs) xp
sim-push-frame {hv} n fs s xp corr rdi-p rsi-p rax-p rbx-p r14-p halt-p r15-p rsp-p
               lo' lo'≤lo front-lo' lo'≤rsp virgin-p heap-p = record
  { rdi-eq = trans rdi-p (rdi-eq corr) ; rsi-eq = trans rsi-p (rsi-eq corr)
  ; rax-eq = trans rax-p (rax-eq corr) ; rbx-eq = trans rbx-p (rbx-eq corr)
  ; r14-eq = trans r14-p (r14-eq corr)
  ; halt-eq = trans halt-p (halt-eq corr) ; rsp-eq = rsp-p
  ; r15-eq = trans r15-p (r15-eq corr) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = λ hl live → trans (heap-p hl live) (heap-eq corr hl live)
  ; lo-le = lo'≤rsp
  ; untouched = λ a fa a<lo' → trans (virgin-p a fa a<lo')
                                     (untouched corr a fa (<-transˡ a<lo' lo'≤lo))
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
  → X.readReg (X.State.regs xp) r14 ≡ X.readReg (X.State.regs s) r14
  → X.State.halted xp ≡ X.State.halted s
  → X.readReg (X.State.regs xp) r15 ≡ X.readReg (X.State.regs s) r15
  -- MATCHED PAIRING (plan 0.61): the epilogue lands %rsp on the caller frame's base
  → X.readReg (X.State.regs xp) rsp ≡ frame-base (current-frame (leave-frame (falloc fs)))
  -- the restored CALLER frame is still above the HIGH-WATER MARK (it is above the
  -- callee's base, which `lo-le` already put above the mark — but no tracked
  -- register relates the two numerically, so it is a premise on the post state).
  -- The mark does NOT rise with the epilogue: the callee's cells stay written, and
  -- remembering that is the whole point of the mark.
  → lo hv ≤ X.readReg (X.State.regs xp) rsp
  → (∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
       → X.readMem (X.State.memory xp) a ≡ X.readMem (X.State.memory s) a)
  → (∀ hl → HDom hv hl → X.readMem (X.State.memory xp) (haddr hv hl)
                                  ≡ X.readMem (X.State.memory s) (haddr hv hl))
  → FlatCorr hv (flat-exec-instr instr-pop-frame [] fs) xp
sim-pop-frame {hv} fs s xp corr ss0 rdi-p rsi-p rax-p rbx-p r14-p halt-p r15-p rsp-p room virgin-p heap-p = record
  { rdi-eq = trans rdi-p (rdi-eq corr) ; rsi-eq = trans rsi-p (rsi-eq corr)
  ; rax-eq = trans rax-p (rax-eq corr) ; rbx-eq = trans rbx-p (rbx-eq corr)
  ; r14-eq = trans r14-p (r14-eq corr)
  ; halt-eq = trans halt-p (halt-eq corr) ; rsp-eq = rsp-p
  ; r15-eq = trans r15-p (r15-eq corr)
  -- Plan 0.61: the epilogue restores the caller's frame (frontier untouched).
  ; dom-fresh = λ {hl} d → subst (λ m → ref-id (heap-ref hl) < m)
                                 (sym (leave-frame-heap-ref (falloc fs))) (dom-fresh corr d)
  ; dom-written = dom-written corr
  ; dom-sized = λ hl lt → dom-sized corr hl
                  (subst (λ szs → heap-offset hl < szs (ref-id (heap-ref hl)))
                         (leave-frame-block-size (falloc fs)) lt)
  ; heap-eq = λ hl live → trans (heap-p hl live) (heap-eq corr hl live)
  ; lo-le = room
  ; untouched = λ a fa a<lo → trans (virgin-p a fa a<lo) (untouched corr a fa a<lo)
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
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- LOAD CODE ADDR: `instr-load-code-addr n` (Output := SV-Code n) ↔ `lea rax,
-- [rip+label n]`. The x86 effective address of a label is `n` (linker-resolved,
-- abstract), and enc-sv(SV-Code n) = n, so rax := n matches — rax-eq is refl.
------------------------------------------------------------------------
sim-load-code-addr : {hv : HeapView} (n : ℕ) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-code-addr n) [] fs)
             (mkstate (xwriteReg (xregs s) rax n) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-code-addr {hv} n fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- SAVE CLOSURE REG: `instr-save-closure-reg` ↔ `mov r12, rdi`. Abstract identity;
-- x86 writes r12 (the reserved closure pointer), which FlatCorr does NOT track —
-- so the whole correspondence is unchanged. Only the fpc bumps.
------------------------------------------------------------------------
sim-save-closure-reg : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr instr-save-closure-reg [] fs)
             (mkstate (xwriteReg (xregs s) r12 (xreadReg (xregs s) rdi)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-save-closure-reg {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Arithmetic reg-ops (Plan 0.34: flag-free, so the post is parametric over
-- the x86 flags). count-inc / scratch-dec increment/decrement a TAG.
------------------------------------------------------------------------
inc-enc : ∀ {am : AddrMap} (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k
        → enc-sv-at am v + 1 ≡ enc-sv-at am (sv-succ v)
inc-enc .(SV-Tag k) k refl = +-comm k 1

dec-enc : ∀ {am : AddrMap} (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k
        → enc-sv-at am v ∸ 1 ≡ enc-sv-at am (sv-pred v)
dec-enc .(SV-Tag zero)    zero    refl = refl
dec-enc .(SV-Tag (suc m)) (suc m) refl = refl

-- Plan 0.54 D item 4: the tally increment is on `Count`/`%r14`, so it is `r14-eq`
-- that carries the `inc-enc` step and `rsi-eq` that is preserved untouched — the
-- exact mirror of the pre-split version, with the ABI register no longer involved.
sim-reg-count-inc : {hv : HeapView} (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Count ≡ SV-Tag k
  → FlatCorr hv (flat-exec-instr (instr-reg-op count-inc) [] fs)
             (mkstate (xwriteReg (xregs s) r14 (xreadReg (xregs s) r14 + 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-count-inc {hv} k newFlags fs s corr c-eq = record
  { rdi-eq = rdi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; rsi-eq = rsi-eq corr
  ; r14-eq = trans (cong (_+ 1) (r14-eq corr)) (inc-enc (readReg (regs (floc fs)) Count) k c-eq)
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

sim-reg-scratch-dec : {hv : HeapView} (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-dec) [] fs)
             (mkstate (xwriteReg (xregs s) rbx (xreadReg (xregs s) rbx ∸ 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-scratch-dec {hv} k newFlags fs s corr sc-eq = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; r14-eq = r14-eq corr
  ; rbx-eq = trans (cong (_∸ 1) (rbx-eq corr)) (dec-enc (readReg (regs (floc fs)) Scratch) k sc-eq)
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
-- `room` (plan 0.54 rung D step 3): the `n` words the bump claims are still in the
-- VIRGIN region, i.e. the heap frontier does not reach the stack high-water mark.
-- This is the HEAP EXHAUSTION premise (`heap-room`), and it is what makes the
-- extended view a legal one — and, via `FlatCorr.untouched`, what makes the fresh
-- block's cells provably unwritten on the concrete side (the postulate
-- `alloc-heap-fresh-x86` is gone).
extend-view : (hv : HeapView) (st n : ℕ)
            → (∀ {hl : HeapLocation} → HDom hv hl → ref-id (heap-ref hl) < st)
            → hfront hv + slots n ≤ lo hv
            → HeapView
extend-view hv st n fresh room = record
  { haddr     = ext-addr hv st
  ; HDom      = ExtDom hv st n
  ; hfront    = hfront hv + slots n
  ; haddr-suc = ext-suc hv st
  ; haddr-inj = inj
  ; dom-below = below
  ; lo        = lo hv
  ; front-lo  = room
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
            (rm : hfront hv + slots n ≤ lo hv)
            (v : StoredValue FS) → sv-below st v
        → enc-sv (extend-view hv st n pf rm) v ≡ enc-sv hv v
enc-ext hv st n pf rm (SV-Ptr (AtDynamic hl)) lt = ext-addr-old hv st hl lt
enc-ext hv st n pf rm (SV-Ptr (AtStack _ _))  _  = refl
enc-ext hv st n pf rm (SV-Tag _)              _  = refl
enc-ext hv st n pf rm (SV-Lit fits-int v)     _  = refl
enc-ext hv st n pf rm (SV-Lit fits-float v)   _  = refl
enc-ext hv st n pf rm (SV-Code _)             _  = refl

enc-ext-maybe : ∀ (hv : HeapView) (st n : ℕ)
                  (pf : ∀ {hl : HeapLocation} → HDom hv hl → ref-id (heap-ref hl) < st)
                  (rm : hfront hv + slots n ≤ lo hv)
                  (mv : Maybe (StoredValue FS)) → svm-below st mv
              → enc-maybe (extend-view hv st n pf rm) mv ≡ enc-maybe hv mv
enc-ext-maybe hv st n pf rm (just v) wf = cong just (enc-ext hv st n pf rm v wf)
enc-ext-maybe hv st n pf rm nothing  _  = refl


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
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Count)
  → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
  → (∀ k → k < stackSlot (regs (floc fs))
         → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) (current-frame (falloc fs)) k))
  → (∀ hl → ref-id (heap-ref hl) ≡ next-heap-ref (falloc fs) → heapMem (floc fs) hl ≡ nothing)
  -- ROOM (plan 0.54 rung D): the bump does not run the heap up into the stack —
  -- and, step 3, it is measured against the HIGH-WATER MARK, not against the
  -- current `%rsp`: a region the stack has already visited keeps its contents, so
  -- only the virgin part of the gap is available to the heap. This is HEAP
  -- EXHAUSTION, and it now also DISCHARGES the fresh block's concrete freshness
  -- (`FlatCorr.untouched`) — the postulate `alloc-heap-fresh-x86` is retired.
  → (room : hfront hv + slots n ≤ lo hv)
  → FlatCorr (extend-view hv (next-heap-ref (falloc fs)) n (dom-fresh corr) room)
             (flat-exec-instr (instr-alloc-heap n) [] fs)
             (mkstate (xwriteReg (xwriteReg (xregs s) rax (X.readReg (xregs s) r15)) r15
                                 (X.readReg (xregs s) r15 + slots n))
                      (memory s) newFlags newPc (xhalted s))
sim-alloc-heap {hv} n newFlags newPc fs s corr wf1 wf2 wfs wfc wf-heap wf-stack fresh-abs room = record
  { rdi-eq  = trans (rdi-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Input1) wf1))
  ; rsi-eq  = trans (rsi-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Input2) wf2))
  ; r14-eq  = trans (r14-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Count) wfc))
  ; rax-eq  = trans (r15-eq corr) (sym (ext-addr-base hv st))
  ; rbx-eq  = trans (rbx-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Scratch) wfs))
  ; halt-eq = halt-eq corr
  ; rsp-eq  = rsp-eq corr
  ; r15-eq  = cong (_+ slots n) (r15-eq corr)
  ; dom-fresh = df
  -- the bump writes no heap cell, so anything written was covered BEFORE and
  -- enters the extended domain as an old cell
  ; dom-written = λ hl eq → ext-old (dom-written corr hl eq)
  ; dom-sized = ds
  ; heap-eq = hp
  -- %rsp is untouched by the bump; the virgin region only SHRANK (its floor rose
  -- from `hfront` to `hfront + 8n`), so both invariants transport.
  ; lo-le = lo-le corr
  ; untouched = λ a fa a<lo → untouched corr a (≤-trans (m≤m+n (hfront hv) (slots n)) fa) a<lo
  ; stack-eq = λ k k< → trans (stack-eq corr k k<)
                              (sym (enc-ext-maybe hv st n dfr room
                                     (stackMem (floc fs) (current-frame (falloc fs)) k)
                                     (wf-stack k k<)))
  }
  where
    st  = next-heap-ref (falloc fs)
    dfr = dom-fresh corr
    -- IN-BOUNDS COVERAGE across the allocation: the fresh block's `n` cells are
    -- exactly what `block-size` now records for it (`size-with`), and they are
    -- exactly what `extend-view` put in the domain (`ext-fresh`); older blocks
    -- keep their sizes and ride `ext-old`. J-style on the ref decision so
    -- `size-with` reduces.
    ds : ∀ (hl : HeapLocation)
       → heap-offset hl < size-with n st (block-size (falloc fs)) (ref-id (heap-ref hl))
       → ExtDom hv st n hl
    ds hl lt = go (ref-id (heap-ref hl) ≟ st) lt
      where go : ∀ (d : Dec (ref-id (heap-ref hl) ≡ st))
               → heap-offset hl < size-with-aux n {ref-id (heap-ref hl)} {st}
                                    (block-size (falloc fs)) d
               → ExtDom hv st n hl
            go (yes req) o<n = ext-fresh req o<n
            go (no  _)   o<b = ext-old (dom-sized corr hl o<b)
    hv' = extend-view hv st n dfr room
    -- THE FRESH BLOCK IS UNWRITTEN, DERIVED (plan 0.54 rung D step 3): its cells
    -- sit in `[hfront, hfront + 8n) ⊆ [hfront, lo)`, the virgin region.
    fresh-x86 : ∀ i → i < n → X.readMem (memory s) (hfront hv + slot-to-disp i) ≡ nothing
    fresh-x86 i i<n = untouched corr (hfront hv + slot-to-disp i)
                        (m≤m+n (hfront hv) (slot-to-disp i))
                        (<-transˡ (+-monoʳ-< (hfront hv) (*-monoˡ-< slot-size i<n)) room)
    df : ∀ {hl : HeapLocation} → ExtDom hv st n hl → ref-id (heap-ref hl) < suc st
    df (ext-old d)       = m<n⇒m<1+n (dfr d)
    df (ext-fresh req _) = subst (_< suc st) (sym req) ≤-refl
    hp : ∀ (hl : HeapLocation) → ExtDom hv st n hl
       → X.readMem (memory s) (ext-addr hv st hl) ≡ enc-maybe hv' (heapMem (floc fs) hl)
    hp hl (ext-old d) =
      trans (cong (X.readMem (memory s)) (ext-addr-old hv st hl (dfr d)))
            (trans (heap-eq corr hl d)
                   (sym (enc-ext-maybe hv st n dfr room (heapMem (floc fs) hl) (wf-heap hl d))))
    hp hl (ext-fresh req off<n) =
      trans (cong (X.readMem (memory s)) (ext-addr-fresh hv st hl req))
            (trans (fresh-x86 (heap-offset hl) off<n)
                   (sym (cong (enc-maybe hv') (fresh-abs hl req))))

------------------------------------------------------------------------
-- STACK ADDRESS: `lea-slot slot` (Output := &stack[frame, slot]) ↔
-- `lea rax, [rsp + slot-to-disp slot]`.
--
-- THE payoff of plan 0.61. The abstract value is `SV-Ptr (AtStack cf slot)`
-- and its encoding is the slot's real address `slot-addr cf slot`
-- (= `frame-base cf + slot·word`, `slot-addr-linear`); the x86 computes
-- `rsp + slot·8`, and `rsp-eq` anchors `%rsp` to `frame-base cf`. Under the
-- old model this was unprovable in principle: the callee's slot k and its
-- caller's slot k were the same abstract cell, so no address existed.
------------------------------------------------------------------------
sim-lea-slot : {hv : HeapView} (slot : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (lea-slot slot) [] fs)
             (mkstate (xwriteReg (xregs s) rax (X.readReg (xregs s) rsp + slot-to-disp slot))
                      (memory s) (flags s) (pc s + 1) (xhalted s))
sim-lea-slot {hv} slot fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; rax-eq = addr-eq
  ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
  ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }
  where
    cf = current-frame (falloc fs)
    addr-eq : X.readReg (xregs s) rsp + slot-to-disp slot ≡ slot-addr cf slot
    addr-eq = trans (cong (_+ slot-to-disp slot) (rsp-eq corr))
                    (trans (cong (λ w → frame-base cf + slot * w) (sym word-eq))
                           (sym (slot-addr-linear cf slot)))

-- Load through a STACK pointer (plan 0.61): `Input1` holds `SV-Ptr (AtStack f k)`
-- and the slot holds `w`. Structurally identical to `sim-load-indirect`; only the
-- residence differs, and it is only expressible at all because a stack pointer
-- now denotes `slot-addr f k` instead of the old placeholder `0`.
sim-load-indirect-stack : {hv : HeapView} (f : Frame) (k : Slot) (w : StoredValue FS)
                          (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → readLoc (floc fs) (AtStack f k) ≡ just w
  → FlatCorr hv (flat-exec-instr load-indirect [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-stack {hv} f k w fs s corr i-eq st-eq =
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
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) st-eq)
    reduces : flat-exec-instr load-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- Second cell through a STACK pointer: `sucLoc (AtStack f k) = AtStack f (suc k)`,
-- so this is `sim-load-indirect-stack` one slot along.
sim-load-indirect-suc-stack : {hv : HeapView} (f : Frame) (k : Slot) (w : StoredValue FS)
                              (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → readLoc (floc fs) (AtStack f (suc k)) ≡ just w
  → FlatCorr hv (flat-exec-instr load-indirect-suc [] fs)
             (mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-suc-stack {hv} f k w fs s corr i-eq st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) rax (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-load-suc-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-suc-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) st-eq)
    reduces : flat-exec-instr load-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- STORE through a stack pointer: `writeLoc … (AtStack f k)` IS the plain stack
-- write (the cross-region guard only concerns the heap branch), so this reuses
-- the same read-back/disjointness machinery as `sim-store-at-slot` — the only
-- difference is that the address comes from `Input1` rather than the instruction.
sim-store-indirect-stack : {hv : HeapView} (k : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) rsp + slot-to-disp k ≡ haddr hv hl') → ⊥)
  → FlatCorr hv (flat-exec-instr store-indirect [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp k)
                                (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-stack {hv} k fs s corr i-eq disj =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    base = X.readReg (xregs s) rsp
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (base + slot-to-disp k) (enc-sv hv Out))
                    (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToStack (floc fs) cf k Out
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) Out (floc fs)
              ≡ writeLocToStack (floc fs) cf k Out
    floc-eq = cong (λ m → exec-store-via-resolved m Out (floc fs)) (cong sv-as-loc i-eq)
    reduces : flat-exec-instr store-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp k) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; lo-le = lo-le corr
      ; untouched = untouched-stack-store (base + slot-to-disp k) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp k))) corr
      ; stack-eq = store-slot-stack-eq base k Out s (floc fs) cf (stackSlot (regs (floc fs)))
                     (stack-eq corr) }

-- …and the SECOND cell. `sucLoc (AtStack cf k) = AtStack cf (suc k)` reduces, so
-- this is literally the same proof at slot `suc k` — `store-slot-stack-eq` is
-- generic in the written slot, and the pair's second slot belongs to the same
-- frame the prologue reserved (`stack-ptr-current-suc`).
sim-store-indirect-suc-stack : {hv : HeapView} (k : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) rsp + slot-to-disp (suc k) ≡ haddr hv hl') → ⊥)
  → FlatCorr hv (flat-exec-instr store-indirect-suc [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (X.readReg (xregs s) rsp + slot-to-disp (suc k))
                                (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-suc-stack {hv} k fs s corr i-eq disj =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    base = X.readReg (xregs s) rsp
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (base + slot-to-disp (suc k)) (enc-sv hv Out))
                    (flags s) (pc s + 1) (xhalted s)
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToStack (floc fs) cf (suc k) Out
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-suc-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) Out (floc fs)
              ≡ writeLocToStack (floc fs) cf (suc k) Out
    floc-eq = cong (λ m → exec-store-suc-via-resolved m Out (floc fs)) (cong sv-as-loc i-eq)
    reduces : flat-exec-instr store-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp (suc k)) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; lo-le = lo-le corr
      ; untouched = untouched-stack-store (base + slot-to-disp (suc k)) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp (suc k)))) corr
      ; stack-eq = store-slot-stack-eq base (suc k) Out s (floc fs) cf (stackSlot (regs (floc fs)))
                     (stack-eq corr) }
