-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Once.Semantics.FloatBits using (float-bits)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Label using (LabelId; idx)
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
                                      ; m+n≤o⇒m≤o∸n; <⇒≢; m∸n+n≡m; ≤-reflexive; m<m+n
                                      ; +-monoʳ-≤; s≤s; z≤n; +-identityʳ; m∸n≤m)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

open import Once.Memory.HeapAddress
  using (HeapRef; sucHL; heap-loc; mkHeapRef; heap-ref; heap-offset; ref-id; _≟HL_)
import Once.CCC.Target.X86-64.Semantics as X
open X using (mkstate; mkflags; _<ᵇ_; writeMem)
  renaming (readReg to xreadReg; writeReg to xwriteReg; readMem to xreadMem)
open X.State using (memory; flags; pc) renaming (regs to xregs; halted to xhalted)
open import Once.CCC.Target.X86-64.Syntax using (slots)
-- Plan 0.65 G1c: the registers by ROLE, not by name. Every projection reduces
-- to the concrete register (`out-reg` IS `rax`), so this is a rename and
-- nothing below it changed.
open import Once.Adequacy.ArchCorrectness.X86-64.RegRoles
  using (sp-reg; clos-reg; heap-reg; out-reg; in1-reg; in2-reg; scratch-reg; count-reg; reg-of)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (Role; role-sp; role-clos; role-heap; role-out; role-in1; role-in2; role-scratch; role-count)
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
    -- D096: WHERE THE CODE IS. A `SV-Code ℓ` encodes to the label's INDEX in
    -- the compiled program — a real address in this index-addressed machine —
    -- not to `idx ℓ`, which is the label's IDENTITY and no position at all.
    -- The view carries it because the encoding must be a function of the map
    -- alone (see `enc-sv-at`); `CompiledCorr.code-eq` is what ties it to the
    -- program the concrete `lea` resolves against.
    caddr     : LabelId → ℕ
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
-- `enc-sv-at (amap hv) v` — the same term — so a view change the map survives is
-- INVISIBLE, with no lemma and no per-field boilerplate.
-- D096: TWO maps, not one. A heap cell's address and a CODE address are both
-- what a `StoredValue` can encode to, and a code address is the label's INDEX
-- in the compiled program — which the old `enc-sv-at am (SV-Code n) = idx n`
-- could not express, because `idx` is the label's IDENTITY (D089) and this
-- record had nowhere to put a resolution. That was the defect the closure call
-- ran into; see D096.
--
-- A record rather than an extra parameter everywhere: every signature that
-- takes an `AddrMap` (`Window`, `StackWindows`, `RetAddrs`, every `sim-*`)
-- keeps taking exactly one, so only the APPLICATIONS moved.
record AddrMap : Set where
  constructor mkAddrMap
  field
    hmap : HeapLocation → ℕ
    cmap : LabelId → ℕ
open AddrMap public

enc-sv-at : AddrMap → StoredValue FS → X.Word
enc-sv-at am (SV-Tag n)                = n
enc-sv-at am (SV-Ptr (AtDynamic hl))   = hmap am hl
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
enc-sv-at am (SV-Lit fits-float v)     = float-bits v
-- Plan 0.63 (D089): `SV-Code` now carries the label's IDENTITY, so its
-- encoding is `idx` — numerically exactly what this yielded before, when the
-- payload was the bare counter. The same FICTION `effectiveAddr (rip+label _)`
-- records (a label number is not an instruction index): D081's open question,
-- owned by `events-running-call`. D089 neither fixes nor worsens it.
enc-sv-at am (SV-Code n)               = cmap am n

enc-maybe-at : AddrMap → Maybe (StoredValue FS) → Maybe X.Word
enc-maybe-at am (just v) = just (enc-sv-at am v)
enc-maybe-at am nothing  = nothing

-- The view-level names every proof uses: one clause each, so they UNFOLD during
-- conversion checking and the comparison lands on the address map.
-- the view's two maps, bundled — this is what every `*-at` takes
amap : HeapView → AddrMap
amap hv = mkAddrMap (haddr hv) (caddr hv)

enc-sv : HeapView → StoredValue FS → X.Word
enc-sv hv = enc-sv-at (amap hv)

enc-maybe : HeapView → Maybe (StoredValue FS) → Maybe X.Word
enc-maybe hv = enc-maybe-at (amap hv)

------------------------------------------------------------------------
-- THE LIVE FRAMES (Plan 0.63, D085).
--
-- `stack-eq` used to describe ONE frame, addressed off `%rsp`. That is
-- exactly enough for straight-line code and NOT enough for a return: the
-- epilogue restores the CALLER's frame, so the post-state has to say
-- something about a window the pre-state never mentioned — which is why
-- `sim-dealloc-stack` had to TAKE the caller's window as a premise
-- (`caller-window`, named after D084 removed the vacuity that hid it).
--
-- So the correspondence is scoped over every LIVE frame: the current one
-- (with its reservation) followed by the saved callers, each addressed by
-- ITS OWN base rather than by `%rsp`. Addressing by `frame-base` is what
-- makes a non-current frame expressible at all — `%rsp` names only one.
frames-of : AllocState {FS} → List (Frame × ℕ)
frames-of alloc = (current-frame alloc , frame-slots alloc) ∷ saved-frames alloc

-- ONE frame's window: its `b` reserved slots correspond cell by cell.
-- The abstract stack enters as `StackMem FS` — the FUNCTION, not the whole
-- `LocState` — for the reason `enc-sv` takes an `AddrMap` (see above): a record
-- update elsewhere in the state would otherwise leave the two sides
-- non-convertible at every stuck occurrence.
-- ONE DIRECTION ONLY (Plan 0.54 rung D): the concrete cell matches wherever the
-- ABSTRACT cell is WRITTEN. Nothing is claimed about a slot the abstract side
-- has not written.
--
-- WHY THE OTHER DIRECTION HAD TO GO. The equation `readMem … ≡ enc-maybe-at am
-- (stk f k)` also constrained the EMPTY case: `enc-maybe-at am nothing ≡
-- nothing`, so it demanded the concrete cell be UNMAPPED wherever the abstract
-- one was unwritten. That is FALSE the moment a closure is applied twice at one
-- depth: the second entry re-enters a frame at or ABOVE the stack high-water
-- mark (`lo` only ever descends), where the concrete cells still hold the
-- PREVIOUS incarnation's data while the abstract frame is fresh. The old
-- `Window` was therefore unprovable at frame entry, which is what blocked
-- `block-step-c-thunk` — and no amount of freshness side-conditions could fix
-- it, because the concrete cells genuinely are dirty.
--
-- With the claim restricted to written cells, frame entry is VACUOUS (a fresh
-- frame has written nothing), so `sim-grow-frame` needs no `fresh-abs`,
-- `fresh-x86` or `fits` at all, and every other producer gets easier.
Window : AddrMap → X.Memory → StackMem FS → Frame → ℕ → Set
Window am mem stk f b = ∀ (k : Slot) → k < b → ∀ (v : StoredValue FS) → stk f k ≡ just v →
  X.readMem mem (frame-base f + slot-to-disp k) ≡ just (enc-sv-at am v)

-- …and the whole live stack, THREADING A FLOOR: each frame's base is at or
-- above the floor, and the next (older) frame's floor is this frame's window
-- END. That thread is the frame SEPARATION the multi-frame statement needs and
-- the reason this is a recursive definition rather than an `All`: with only a
-- per-frame predicate, a write inside the callee's window could silently be a
-- write inside the caller's, and every stack store would be unprovable.
--
-- The initial floor is the view's high-water mark `lo`, so EVERY live stack
-- cell is above `lo` — hence above the heap (`front-lo` then `dom-below`).
-- That is the old one-frame `sep` argument, now covering every frame, and it
-- is what lets the heap stores keep their disjointness obligation as a
-- THEOREM instead of a premise.
--
-- `frames-of` is always a cons, so the head always reduces and the trivial
-- `stack-eq = stack-eq corr` copies stay trivial.
StackWindows : AddrMap → X.Memory → StackMem FS → ℕ → List (Frame × ℕ) → Set
StackWindows am mem stk fl []             = ⊤
StackWindows am mem stk fl ((f , b) ∷ fr) =
  (fl ≤ frame-base f) × Window am mem stk f b
    × StackWindows am mem stk (frame-base f + slots b) fr

------------------------------------------------------------------------
-- THE PENDING RETURN ADDRESSES (D093).
--
-- One cell per pending return, and it is NOT in any window: it is the slot the
-- CALL consumed, which sits exactly at the callee frame's window END — between
-- the callee's last slot and the caller's base (D086: the call owns the
-- return-address slot, the body's marker only deepens the frame below it).
-- That gap is the slack `StackWindows`' floor leaves, and this is what finally
-- says what lives in it.
--
-- Paired with `frames-of` — the CURRENT frame first — because the pending
-- return at the head of `fret` is the one the CURRENT frame owes, and its cell
-- is the current frame's own window end. That is also what makes a RETURN
-- carry: after `leave-frame` the new head is the old second, whose cell the
-- tail already describes, and `add rsp,8b ; ret` writes no memory at all.
--
-- `xoff` is the pc translation (`blk-off prog` at the use site) rather than the
-- program itself, so this stays a statement about the machine, not the emitter.
-- The length rows: `fret` longer than the live frames is impossible
-- (`ConcFlatSim.RetMatch` pairs them), so that row is `⊥`; the outermost frame
-- owes nothing, which is the `⊤` row.
------------------------------------------------------------------------
-- …and WHERE THE NEXT FRAME STARTS. The cell is not merely somewhere in the
-- gap: it IS the gap. A call shifts by exactly one slot and stores the return
-- address in it, so the caller's base is one slot above the callee's window
-- END — an EQUALITY, where `StackWindows` threads only `≤`. The return needs
-- exactly this (`%rsp` after `add rsp,8b ; ret` must land on the caller's
-- base), and it belongs here because it is a fact about the same slot.
GapNext : ℕ → List (Frame × ℕ) → Set
GapNext e []              = ⊤
GapNext e ((f' , b') ∷ _) = e + slot-size ≡ frame-base f'

RetAddrs : (ℕ → ℕ) → X.Memory → List (Frame × ℕ) → List ℕ → Set
RetAddrs xoff mem fr             []       = ⊤
RetAddrs xoff mem ((f , b) ∷ fr) (r ∷ rs) =
  (X.readMem mem (frame-base f + slots b) ≡ just (xoff r))
  × GapNext (frame-base f + slots b) fr
  × RetAddrs xoff mem fr rs
RetAddrs xoff mem []             (r ∷ rs) = ⊥

-- RE-ANCHORING THE HEAD (D093). The pending return at the head of `fret` is
-- addressed by the CURRENT frame's window END, and a body entry MOVES that
-- frame — down by its reservation, while setting the reservation to it. The
-- end therefore lands on the same cell (that is D086's whole point: the call's
-- slot sits just above the body's frame), and this is the transport that says
-- so. Everything below the head is untouched.
ret-head : ∀ (xoff : ℕ → ℕ) (mem : X.Memory) (f f' : Frame) (b b' : ℕ)
             (fr : List (Frame × ℕ)) (rs : List ℕ)
         → frame-base f' + slots b' ≡ frame-base f + slots b
         → RetAddrs xoff mem ((f , b) ∷ fr) rs
         → RetAddrs xoff mem ((f' , b') ∷ fr) rs
ret-head xoff mem f f' b b' fr []       eq r           = tt
ret-head xoff mem f f' b b' fr (r ∷ rs) eq (h , g , t) =
  subst (λ a → X.readMem mem a ≡ just (xoff r)) (sym eq) h
  , subst (λ e → GapNext e fr) (sym eq) g
  , t

------------------------------------------------------------------------
-- The correspondence: a FlatState and an x86 State agree on the four
-- abstract registers (under enc-sv), the pc, the zero-flag, the halt
-- flag, the heap memory (under enc-hl + enc-sv), and the LIVE STACK
-- (every frame, base-relative, under enc-sv).
--
-- `stack-eq`: see `StackWindows` above. The current frame's window is its
-- HEAD, recovered in the old `%rsp`-addressed form through `rsp-eq` by the
-- derived `stack-eq-cur` — which is what every straight-line consumer
-- (load/store-at-slot, restore-input, worklist-*) actually uses.
------------------------------------------------------------------------
record FlatCorr (hv : HeapView) (fs : FlatState) (s : X.State) : Set where
  field
    rdi-eq  : X.readReg (X.State.regs s) in1-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input1)
    rsi-eq  : X.readReg (X.State.regs s) in2-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input2)
    rax-eq  : X.readReg (X.State.regs s) out-reg ≡ enc-sv hv (readReg (regs (floc fs)) Output)
    rbx-eq  : X.readReg (X.State.regs s) scratch-reg ≡ enc-sv hv (readReg (regs (floc fs)) Scratch)
    -- THE TALLY (plan 0.54 D item 4): `%r14` IS the `Count` register. Without
    -- this field the correspondence would say NOTHING about the counter, and the
    -- choice of physical register in `compile-abstract` would not be checked by
    -- anything — the tally lowering could name any register and still typecheck.
    -- With it, every block step must re-establish it, so a wrong register in the
    -- codegen is a TYPE ERROR here.
    r14-eq  : X.readReg (X.State.regs s) count-reg ≡ enc-sv hv (readReg (regs (floc fs)) Count)
    -- THE CLOSURE REGISTER (D097). `%r12` mirrors the flat `fclosure`, which is
    -- where the abstract machine keeps the closure pointer (`exec-abstract`
    -- treats `instr-save-closure-reg` as the identity precisely because that
    -- register lives at the FLAT level). Untracked until now, because nothing
    -- READ it — the call does: `call *0x8(%r12)` dereferences it, so without
    -- this field the concrete call's target is unrelated to anything abstract.
    r12-eq  : X.readReg (X.State.regs s) clos-reg ≡ enc-sv hv (fclosure fs)
    halt-eq : X.State.halted s ≡ halted (floc fs)
    -- THE STACK ANCHOR (plan 0.61): `%rsp` IS the current frame's base. Frames
    -- move with the stack pointer, so this holds at every step — and it is what
    -- gives a stack POINTER its address (`enc-sv (SV-Ptr (AtStack f k))`).
    rsp-eq  : X.readReg (X.State.regs s) sp-reg ≡ frame-base (current-frame (falloc fs))
    -- THE FRONTIER: `%r15` (the bump allocator's heap top) IS the view's frontier.
    -- This is what makes the next `instr-alloc-heap` provable: the fresh block's
    -- address is read off the concrete machine, not predicted from the abstract state.
    r15-eq  : X.readReg (X.State.regs s) heap-reg ≡ hfront hv
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
    -- BOUNDED to the current frame's reserved slots (k < frame-slots). An
    -- UNBOUNDED ∀ k would be unsatisfiable (it would claim the CALLER's slots,
    -- above rsp, holding live data, ≡ the abstract `nothing`). The bound is the
    -- current frame's reserved slot count `frame-slots` (Plan 0.63: it lives
    -- with the frame stack, in the AllocState — there used to be a mirror of
    -- it in the register file), NOT the compile-time frontier
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
    lo-le : lo hv ≤ X.readReg (X.State.regs s) sp-reg
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
    -- EVERY LIVE FRAME (Plan 0.63, D085) — see `StackWindows`. The bound per
    -- frame is its OWN reservation (`frame-slots` for the current one, the
    -- remembered count for each saved caller): an unbounded ∀ k would be
    -- unsatisfiable (it would claim the cells beyond the outermost frame,
    -- which the loader owns, are the abstract `nothing`).
    stack-eq : StackWindows (amap hv) (X.State.memory s) (stackMem (floc fs))
                            (lo hv) (frames-of (falloc fs))
open FlatCorr public

------------------------------------------------------------------------
-- THE POST-STATE, NOT THE UPDATE (Plan 0.65 G1c step 2).
--
-- Every `sim-*` below used to STATE its conclusion over a reconstructed state:
-- `mkstate (xwriteReg (xregs s) rax v) (memory s) (flags s) (pc s + 1)
-- (xhalted s)` — 44 five-field record literals, and the reason this module
-- could not be arch-generic. riscv64's state has four fields and no flags at
-- all, so a core that BUILDS x86-64's state is x86-64's forever.
--
-- The fix is not to parameterise over the update. It is to stop performing one:
-- take the post-state as given and say what must HOLD of it. `ArithSimCore`'s
-- rule, and the reason it is the right one here is visible in what is absent —
-- FLAGS. All 44 literals either preserved `flags s` or took an opaque
-- `newFlags`; not one proof ever read them. Stated this way the core cannot
-- mention flags because it has no state constructor to put them in, and every
-- arch's extra state components (flags, CSRs, whatever) are covered for free.
--
-- The pc is absent for the same reason, and that is a finding rather than an
-- omission: `FlatCorr` has no pc field. The pc discipline lives one layer up,
-- in the block-steps, so a register write's correspondence genuinely does not
-- constrain it.
--
-- INDEXED BY `Role`, not by `Reg`: `off-role` needs "the roles I did not write
-- are unchanged", which over eight named registers is 28 inequalities and over
-- the enum is one `ρ' ≢ ρ` that every call site discharges with `λ ()`.
------------------------------------------------------------------------
record SetsRole (s s' : X.State) (ρ : Role) (v : X.Word) : Set where
  field
    at-role    : X.readReg (X.State.regs s') (reg-of ρ) ≡ v
    off-role   : ∀ ρ' → ¬ (ρ' ≡ ρ)
               → X.readReg (X.State.regs s') (reg-of ρ') ≡ X.readReg (X.State.regs s) (reg-of ρ')
    keeps-mem  : X.State.memory s' ≡ X.State.memory s
    keeps-halt : X.State.halted s' ≡ X.State.halted s
open SetsRole public

------------------------------------------------------------------------
-- Transporting the fields a role write does not touch. One helper per
-- `FlatCorr` field, so a `sim-*` record literal stays as short as it was when
-- the post-state was concrete — `rdi-eq corr` becomes `keep-in1 corr st (λ ())`
-- and the `(λ ())` IS the distinctness the concrete `writeReg` used to supply
-- by reduction.
--
-- `dom-fresh` / `dom-written` / `dom-sized` need no helper: read their
-- signatures and they never mention the machine state at all.
------------------------------------------------------------------------
module _ {hv : HeapView} {fs : FlatState} {s s' : X.State} {ρ : Role} {v : X.Word}
         (corr : FlatCorr hv fs s) (st : SetsRole s s' ρ v) where

  keep-in1 : ¬ (role-in1 ≡ ρ)
           → X.readReg (X.State.regs s') in1-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input1)
  keep-in1 ne = trans (off-role st role-in1 ne) (rdi-eq corr)

  keep-in2 : ¬ (role-in2 ≡ ρ)
           → X.readReg (X.State.regs s') in2-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input2)
  keep-in2 ne = trans (off-role st role-in2 ne) (rsi-eq corr)

  keep-out : ¬ (role-out ≡ ρ)
           → X.readReg (X.State.regs s') out-reg ≡ enc-sv hv (readReg (regs (floc fs)) Output)
  keep-out ne = trans (off-role st role-out ne) (rax-eq corr)

  keep-scratch : ¬ (role-scratch ≡ ρ)
               → X.readReg (X.State.regs s') scratch-reg ≡ enc-sv hv (readReg (regs (floc fs)) Scratch)
  keep-scratch ne = trans (off-role st role-scratch ne) (rbx-eq corr)

  keep-count : ¬ (role-count ≡ ρ)
             → X.readReg (X.State.regs s') count-reg ≡ enc-sv hv (readReg (regs (floc fs)) Count)
  keep-count ne = trans (off-role st role-count ne) (r14-eq corr)

  keep-clos : ¬ (role-clos ≡ ρ) → X.readReg (X.State.regs s') clos-reg ≡ enc-sv hv (fclosure fs)
  keep-clos ne = trans (off-role st role-clos ne) (r12-eq corr)

  keep-sp : ¬ (role-sp ≡ ρ)
          → X.readReg (X.State.regs s') sp-reg ≡ frame-base (current-frame (falloc fs))
  keep-sp ne = trans (off-role st role-sp ne) (rsp-eq corr)

  keep-heap-reg : ¬ (role-heap ≡ ρ) → X.readReg (X.State.regs s') heap-reg ≡ hfront hv
  keep-heap-reg ne = trans (off-role st role-heap ne) (r15-eq corr)

  keep-halt : X.State.halted s' ≡ halted (floc fs)
  keep-halt = trans (keeps-halt st) (halt-eq corr)

  keep-heap : ∀ (hl : HeapLocation) → HDom hv hl
            → X.readMem (X.State.memory s') (haddr hv hl) ≡ enc-maybe hv (heapMem (floc fs) hl)
  keep-heap hl d = trans (cong (λ m → X.readMem m (haddr hv hl)) (keeps-mem st)) (heap-eq corr hl d)

  keep-lo-le : ¬ (role-sp ≡ ρ) → lo hv ≤ X.readReg (X.State.regs s') sp-reg
  keep-lo-le ne = subst (lo hv ≤_) (sym (off-role st role-sp ne)) (lo-le corr)

  keep-untouched : ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
                 → X.readMem (X.State.memory s') a ≡ nothing
  keep-untouched a f<a a<lo =
    trans (cong (λ m → X.readMem m a) (keeps-mem st)) (untouched corr a f<a a<lo)

  keep-stack : StackWindows (amap hv) (X.State.memory s') (stackMem (floc fs))
                            (lo hv) (frames-of (falloc fs))
  keep-stack = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs)) (lo hv) (frames-of (falloc fs)))
                     (sym (keeps-mem st)) (stack-eq corr)

------------------------------------------------------------------------
-- The window a straight-line instruction addresses: the CURRENT frame's,
-- in the `%rsp`-relative form the emitted code uses. This is the head of
-- the frame list, re-anchored through `rsp-eq` — i.e. exactly the field
-- `stack-eq` used to BE, now derived.
------------------------------------------------------------------------
-- (`stk`/`f`/`b` are EXPLICIT: `Window` unfolds during conversion, and then
-- `stk f k` with a non-variable `f` is not a Miller pattern — an implicit
-- would just block.)
win-at : ∀ (am : AddrMap) (mem : X.Memory) (stk : StackMem FS) (f : Frame) (b : ℕ) (base : ℕ)
       → base ≡ frame-base f
       → (∀ (k : Slot) → k < b → ∀ (v : StoredValue FS) → stk f k ≡ just v
            → X.readMem mem (base + slot-to-disp k) ≡ just (enc-sv-at am v))
       → Window am mem stk f b
win-at am mem stk f b base eq w k k<b v ev rewrite sym eq = w k k<b v ev

win-off : ∀ (am : AddrMap) (mem : X.Memory) (stk : StackMem FS) (f : Frame) (b : ℕ) (base : ℕ)
        → base ≡ frame-base f → Window am mem stk f b
        → ∀ (k : Slot) → k < b → ∀ (v : StoredValue FS) → stk f k ≡ just v
        → X.readMem mem (base + slot-to-disp k) ≡ just (enc-sv-at am v)
win-off am mem stk f b base eq w k k<b v ev rewrite eq = w k k<b v ev

-- The current frame's window, as a `Window` (the head of the list).
stack-eq-win : ∀ {hv : HeapView} {fs : FlatState} {s : X.State} → FlatCorr hv fs s
             → Window (amap hv) (X.State.memory s) (stackMem (floc fs))
                      (current-frame (falloc fs)) (frame-slots (falloc fs))
stack-eq-win corr = proj₁ (proj₂ (stack-eq corr))

stack-eq-cur : ∀ {hv : HeapView} {fs : FlatState} {s : X.State} → FlatCorr hv fs s
             → ∀ (k : Slot) → k < frame-slots (falloc fs)
             → ∀ (v : StoredValue FS)
             → stackMem (floc fs) (current-frame (falloc fs)) k ≡ just v
             → X.readMem (X.State.memory s) (X.readReg (X.State.regs s) sp-reg + slot-to-disp k)
               ≡ just (enc-sv hv v)
stack-eq-cur {hv} {fs} {s} corr =
  win-off (amap hv) (X.State.memory s) (stackMem (floc fs))
          (current-frame (falloc fs)) (frame-slots (falloc fs))
          (X.readReg (X.State.regs s) sp-reg) (rsp-eq corr) (stack-eq-win corr)

-- THE LAYOUT SEPARATION, derived: the heap frontier is at or below `%rsp`,
-- through the high-water mark (`front-lo` then `lo-le`). Every heap/stack
-- disjointness consumer uses THIS — the field it replaces had the same type.
sep : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
    → FlatCorr hv fs s → hfront hv ≤ X.readReg (X.State.regs s) sp-reg
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
  ; caddr     = caddr hv
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
-- unfolds to `enc-sv-at (amap hv)` on both sides. That is the whole reason the
-- wrapper above exists.)

-- `untouched` at the descended view: the region only shrank.
untouched-descend : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
                      (lo' : ℕ) (le : lo' ≤ lo hv) (fl : hfront hv ≤ lo')
                    (corr : FlatCorr hv fs s)
                  → ∀ (a : ℕ) → hfront hv ≤ a → a < lo'
                  → X.readMem (X.State.memory s) a ≡ nothing
untouched-descend lo' le fl corr a fa a<lo' = untouched corr a fa (<-transˡ a<lo' le)

------------------------------------------------------------------------
-- x86-64 REALISES `SetsRole`: the state that writes one role's register and
-- leaves memory, the halt flag and the other seven roles alone.
--
-- THE 64 CLAUSES ARE THE POINT, not an accident. While the post-state was a
-- concrete `mkstate` literal, "writing rax leaves rdi alone" was free —
-- `readReg (writeReg rf rax v) rdi` reduces because `rax` and `rdi` are
-- distinct constructors of a record's fields. Making the post-state abstract
-- is exactly what withdraws that, so the evidence has to be produced
-- somewhere, and here is where it belongs: next to the register file, in the
-- arch layer, written once. Same shape as `FlatComposition.skip-law` — an ISA
-- fact that cannot be generalised away, only relocated out of the
-- correspondence.
------------------------------------------------------------------------
sets-role-x86 : ∀ (s : X.State) (ρ : Role) (v : X.Word) (p : ℕ)
  → SetsRole s (mkstate (xwriteReg (xregs s) (reg-of ρ) v) (memory s) (flags s) p (xhalted s)) ρ v
sets-role-x86 s ρ v p = record
  { at-role = at ρ ; off-role = off ρ ; keeps-mem = refl ; keeps-halt = refl }
  where
    at : ∀ ρ₀ → X.readReg (xwriteReg (xregs s) (reg-of ρ₀) v) (reg-of ρ₀) ≡ v
    at role-sp = refl
    at role-clos = refl
    at role-heap = refl
    at role-out = refl
    at role-in1 = refl
    at role-in2 = refl
    at role-scratch = refl
    at role-count = refl

    off : ∀ ρ₀ ρ' → ¬ (ρ' ≡ ρ₀)
        → X.readReg (xwriteReg (xregs s) (reg-of ρ₀) v) (reg-of ρ')
          ≡ X.readReg (xregs s) (reg-of ρ')
    off role-sp      role-sp      ne = ⊥-elim (ne refl)
    off role-sp      role-clos    _  = refl
    off role-sp      role-heap    _  = refl
    off role-sp      role-out     _  = refl
    off role-sp      role-in1     _  = refl
    off role-sp      role-in2     _  = refl
    off role-sp      role-scratch _  = refl
    off role-sp      role-count   _  = refl
    off role-clos    role-sp      _  = refl
    off role-clos    role-clos    ne = ⊥-elim (ne refl)
    off role-clos    role-heap    _  = refl
    off role-clos    role-out     _  = refl
    off role-clos    role-in1     _  = refl
    off role-clos    role-in2     _  = refl
    off role-clos    role-scratch _  = refl
    off role-clos    role-count   _  = refl
    off role-heap    role-sp      _  = refl
    off role-heap    role-clos    _  = refl
    off role-heap    role-heap    ne = ⊥-elim (ne refl)
    off role-heap    role-out     _  = refl
    off role-heap    role-in1     _  = refl
    off role-heap    role-in2     _  = refl
    off role-heap    role-scratch _  = refl
    off role-heap    role-count   _  = refl
    off role-out     role-sp      _  = refl
    off role-out     role-clos    _  = refl
    off role-out     role-heap    _  = refl
    off role-out     role-out     ne = ⊥-elim (ne refl)
    off role-out     role-in1     _  = refl
    off role-out     role-in2     _  = refl
    off role-out     role-scratch _  = refl
    off role-out     role-count   _  = refl
    off role-in1     role-sp      _  = refl
    off role-in1     role-clos    _  = refl
    off role-in1     role-heap    _  = refl
    off role-in1     role-out     _  = refl
    off role-in1     role-in1     ne = ⊥-elim (ne refl)
    off role-in1     role-in2     _  = refl
    off role-in1     role-scratch _  = refl
    off role-in1     role-count   _  = refl
    off role-in2     role-sp      _  = refl
    off role-in2     role-clos    _  = refl
    off role-in2     role-heap    _  = refl
    off role-in2     role-out     _  = refl
    off role-in2     role-in1     _  = refl
    off role-in2     role-in2     ne = ⊥-elim (ne refl)
    off role-in2     role-scratch _  = refl
    off role-in2     role-count   _  = refl
    off role-scratch role-sp      _  = refl
    off role-scratch role-clos    _  = refl
    off role-scratch role-heap    _  = refl
    off role-scratch role-out     _  = refl
    off role-scratch role-in1     _  = refl
    off role-scratch role-in2     _  = refl
    off role-scratch role-scratch ne = ⊥-elim (ne refl)
    off role-scratch role-count   _  = refl
    off role-count   role-sp      _  = refl
    off role-count   role-clos    _  = refl
    off role-count   role-heap    _  = refl
    off role-count   role-out     _  = refl
    off role-count   role-in1     _  = refl
    off role-count   role-in2     _  = refl
    off role-count   role-scratch _  = refl
    off role-count   role-count   ne = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- Per-instruction simulation (Plan 0.32 M3 Phase D). Each lemma: one
-- exec-flat step on `i` corresponds to running compile-abstract i on the
-- x86 state, preserving FlatCorr. Because both machines are flat, the
-- value encoding is preserved field-by-field. (1-to-1 instructions;
-- multi-x86 `alloc-heap` + the jump pc-offset are the continuation.)
--
-- Plan 0.65 G1c step 2: the REGISTER-POKE family below no longer names a
-- post-state. It takes any `s'` that `SetsRole` describes, so the statement is
-- about what holds AFTER the write rather than about how x86-64 builds a
-- state — which is what makes it instantiable at riscv64's four-field state.
--
-- First: mov-to-output (Output := Input1) ↔ `mov rax, rdi`.
-- new rax (= old rdi) corresponds to new Output (= old Input1), so
-- rax-eq is exactly the old rdi-eq.
------------------------------------------------------------------------
sim-mov-to-output : {hv : HeapView} (fs : FlatState) (s s' : X.State)
  → FlatCorr hv fs s
  → SetsRole s s' role-out (X.readReg (X.State.regs s) in1-reg)
  → FlatCorr hv (flat-exec-instr mov-to-output [] fs) s'
sim-mov-to-output {hv} fs s s' corr st = record
  { rdi-eq  = keep-in1 corr st (λ ())
  ; rax-eq  = trans (at-role st) (rdi-eq corr)
  ; rsi-eq  = keep-in2 corr st (λ ())
  ; rbx-eq  = keep-scratch corr st (λ ())
  ; r14-eq  = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = keep-heap corr st
  ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-in1 (X.readReg (X.State.regs s) out-reg)
  → FlatCorr hv (flat-exec-instr mov-to-input [] fs) s'
sim-mov-to-input {hv} fs s s' corr st = record
  { rdi-eq = trans (at-role st) (rax-eq corr) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = keep-out corr st (λ ()) ; rbx-eq = keep-scratch corr st (λ ()) ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- mov-input2-to-output (Output := Input2) ↔ `mov rax, rsi`.
sim-mov-input2-to-output : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-out (X.readReg (X.State.regs s) in2-reg)
  → FlatCorr hv (flat-exec-instr mov-input2-to-output [] fs) s'
sim-mov-input2-to-output {hv} fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = trans (at-role st) (rsi-eq corr) ; rbx-eq = keep-scratch corr st (λ ()) ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- mov-output-to-input2 (Input2 := Output) ↔ `mov rsi, rax`.
sim-mov-output-to-input2 : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-in2 (X.readReg (X.State.regs s) out-reg)
  → FlatCorr hv (flat-exec-instr mov-output-to-input2 [] fs) s'
sim-mov-output-to-input2 {hv} fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = trans (at-role st) (rax-eq corr) ; rax-eq = keep-out corr st (λ ()) ; rbx-eq = keep-scratch corr st (λ ()) ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n, so
-- the new field IS `at-role` with no transport at all.
sim-load-tag-lit : {hv : HeapView} (n : ℕ) (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-out n
  → FlatCorr hv (flat-exec-instr (instr-load-tag-lit n) [] fs) s'
sim-load-tag-lit {hv} n fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = at-role st ; rbx-eq = keep-scratch corr st (λ ()) ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`.
sim-reg-scratch-one : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-scratch 1
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-one) [] fs) s'
sim-reg-scratch-one {hv} fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = keep-out corr st (λ ()) ; rbx-eq = at-role st ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`.
sim-reg-scratch-zero : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-scratch 0
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-zero) [] fs) s'
sim-reg-scratch-zero {hv} fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = keep-out corr st (λ ()) ; rbx-eq = at-role st ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op count-zero (Count := SV-Tag 0) ↔ `mov r14, 0`.
-- Plan 0.54 D item 4: the tally register, NOT rsi — `rsi-eq` is UNTOUCHED
-- here, which is the whole point: zeroing the counter no longer disturbs the
-- ABI's second argument register. With roles that reads directly: the written
-- role is `role-count`, and `role-in2` is one of the seven `off-role` covers.
sim-reg-count-zero : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-count 0
  → FlatCorr hv (flat-exec-instr (instr-reg-op count-zero) [] fs) s'
sim-reg-count-zero {hv} fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = keep-out corr st (λ ()) ; rbx-eq = keep-scratch corr st (λ ()) ; r14-eq = at-role st
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op scratch-load-count (Scratch := Count) ↔ `mov rbx, r14`.
sim-reg-scratch-load-count : {hv : HeapView} (fs : FlatState) (s s' : X.State) → FlatCorr hv fs s
  → SetsRole s s' role-scratch (X.readReg (X.State.regs s) count-reg)
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-load-count) [] fs) s'
sim-reg-scratch-load-count {hv} fs s s' corr st = record
  { rdi-eq = keep-in1 corr st (λ ()) ; rsi-eq = keep-in2 corr st (λ ()) ; rax-eq = keep-out corr st (λ ()) ; rbx-eq = trans (at-role st) (r14-eq corr) ; r14-eq = keep-count corr st (λ ())
  ; r12-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; rsp-eq = keep-sp corr st (λ ()) ; r15-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

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
             (mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-suc {hv} hl w fs s corr i-eq h-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- Heap load (no offset): load-indirect (Output := *Input1) ↔
-- `mov rax, [rdi]`. Sibling of load-indirect-suc; reads the cell Input1
-- points to directly. Same reduce-then-correspond structure.
------------------------------------------------------------------------
sim-load-indirect : {hv : HeapView} (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) hl ≡ just w
  → FlatCorr hv (flat-exec-instr load-indirect [] fs)
             (mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect {hv} hl w fs s corr i-eq h-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
             (mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-from-slot {hv} slot w fs s corr st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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

------------------------------------------------------------------------
-- THE FRAME-LIST TRANSPORTS (Plan 0.63, D085). Every step re-establishes
-- `stack-eq` through one of these four.
------------------------------------------------------------------------

-- A write that misses `a` leaves the read at `a` alone.
-- …and the cell the write DID land on (D098: the call reads back what it just
-- pushed, one step later, on the return).
read-write-hit : ∀ (mem : X.Memory) (waddr : ℕ) (v' : X.Word)
               → X.readMem (writeMem mem waddr v') waddr ≡ just v'
read-write-hit mem waddr v' rewrite ≡ᵇ-refl waddr = refl

read-write-miss : ∀ (mem : X.Memory) (waddr : ℕ) (v' : X.Word) (a : ℕ) → (a ≡ waddr → ⊥)
                → X.readMem (writeMem mem waddr v') a ≡ X.readMem mem a
read-write-miss mem waddr v' a ne rewrite ≢→≡ᵇfalse {a} {waddr} ne = refl

-- THE FLOOR IS ONLY EVER READ AT THE HEAD, so replacing it there is the whole
-- of both frame moves: `enter-frame` conses (the tail's floor becomes the
-- caller's base), `leave-frame` drops the head (the floor drops back to `lo`).
windows-reanchor : ∀ {am : AddrMap} {mem : X.Memory} {stk : StackMem FS}
                     (fl fl' : ℕ) (f : Frame) (b : ℕ) (fr : List (Frame × ℕ))
                 → fl' ≤ frame-base f
                 → StackWindows am mem stk fl  ((f , b) ∷ fr)
                 → StackWindows am mem stk fl' ((f , b) ∷ fr)
windows-reanchor fl fl' f b fr le (_ , win , rest) = le , win , rest

-- LOWER THE FLOOR of a whole frame list. The floor is only ever a LOWER bound
-- (`fl ≤ frame-base f`), and each tail's floor is computed from its own head,
-- so dropping the initial floor weakens the head's bound and touches nothing
-- else. `c-thunk` needs it: growing a frame re-anchors the SAVED frames at the
-- grown window's end, which sits at or below where they were anchored before.
windows-lower : ∀ {am : AddrMap} {mem : X.Memory} {stk : StackMem FS}
                  (fl fl' : ℕ) (fr : List (Frame × ℕ))
              → fl' ≤ fl → StackWindows am mem stk fl fr → StackWindows am mem stk fl' fr
windows-lower fl fl' []             le w                = tt
windows-lower fl fl' ((f , b) ∷ fr) le (bd , win , rest) = ≤-trans le bd , win , rest

-- A STORE THAT ONLY FORGETS preserves every window. Direct consequence of
-- `Window` being one-directional: it constrains a cell only where the abstract
-- side holds a value, so removing values can never invalidate it. `c-thunk`'s
-- frame clear is the instance — the saved frames' windows ride across it
-- without any frame-distinctness argument.
windows-forget : ∀ {am : AddrMap} {mem : X.Memory} (stk stk' : StackMem FS)
                   (fl : ℕ) (fr : List (Frame × ℕ))
               → (∀ (f : Frame) (k : Slot) (v : StoredValue FS) → stk' f k ≡ just v → stk f k ≡ just v)
               → StackWindows am mem stk fl fr → StackWindows am mem stk' fl fr
windows-forget stk stk' fl []             kept w                 = tt
windows-forget {am} {mem} stk stk' fl ((f , b) ∷ fr) kept (bd , win , rest) =
  bd
  , (λ k k<b v ev → win k k<b v (kept f k v ev))
  , windows-forget {am} {mem} stk stk' (frame-base f + slots b) fr kept rest

-- LEAVE: the epilogue DROPS THE HEAD, so the caller's window is the TAIL of
-- the pre-state's evidence. This is the payoff of scoping `stack-eq` over the
-- whole frame stack: `sim-dealloc-stack`'s `caller-window` premise — the
-- explicit statement of the gap D084 exposed — becomes a theorem, and it is
-- the same evidence `c-ret`'s block-step will need. The floor drops back to
-- `lo` (a weakening — the caller's base is above the callee's window end).
-- J-style on the frame stack so `leave-frame-aux` reduces.
windows-leave : ∀ {am : AddrMap} {mem : X.Memory} {stk : StackMem FS}
                  (alloc : AllocState {FS}) (fl : ℕ)
              → StackWindows am mem stk fl (frames-of alloc)
              → StackWindows am mem stk fl (frames-of (leave-frame alloc))
windows-leave {am} {mem} {stk} alloc fl w = go (saved-frames alloc) refl w
  where
    go : ∀ (sf : List (Frame × ℕ)) → saved-frames alloc ≡ sf
       → StackWindows am mem stk fl ((current-frame alloc , frame-slots alloc) ∷ sf)
       → StackWindows am mem stk fl (frames-of (leave-frame-aux sf alloc))
    go []              eq w'                          rewrite eq = w'
    go ((f , b) ∷ rst) eq (bd , _ , (bd' , win' , rest')) =
      ≤-trans bd (≤-trans (m≤m+n (frame-base (current-frame alloc))
                                 (slots (frame-slots alloc))) bd')
      , win' , rest'

-- TRANSPORT: anything that leaves every cell AT OR ABOVE THE FLOOR alone —
-- concretely (the x86 memory) and abstractly (the frame's slots) — preserves
-- every window. Both the heap store (it writes strictly below `lo`) and the
-- TAIL of a stack store (it writes strictly below the caller's floor) are
-- instances; so is a view whose address map only changed off the stack.
windows-above : ∀ {am : AddrMap} (mem mem' : X.Memory) (stk stk' : StackMem FS)
                  (fl : ℕ) (fr : List (Frame × ℕ))
              → (∀ (a : ℕ) → fl ≤ a → X.readMem mem' a ≡ X.readMem mem a)
              → (∀ (f : Frame) → fl ≤ frame-base f → ∀ (k : Slot) → stk' f k ≡ stk f k)
              → StackWindows am mem stk fl fr → StackWindows am mem' stk' fl fr
windows-above mem mem' stk stk' fl []             ag ab w = tt
windows-above {am} mem mem' stk stk' fl ((f , b) ∷ fr) ag ab (bd , win , rest) =
  bd
  , (λ k k<b v ev → trans (ag (frame-base f + slot-to-disp k)
                              (≤-trans bd (m≤m+n (frame-base f) (slot-to-disp k))))
                          (win k k<b v (trans (sym (ab f bd k)) ev)))
  , windows-above {am} mem mem' stk stk' (frame-base f + slots b) fr
      (λ a le  → ag a  (≤-trans up le))
      (λ f' le → ab f' (≤-trans up le))
      rest
  where up : fl ≤ frame-base f + slots b
        up = ≤-trans bd (m≤m+n (frame-base f) (slots b))

-- A write strictly BELOW the floor is invisible to every window: the heap
-- store's case, where the floor is `lo` and the target is a mapped cell.
windows-write-below : ∀ {am : AddrMap} (mem : X.Memory) (stk : StackMem FS)
                        (waddr : ℕ) (v' : X.Word) (fl : ℕ) (fr : List (Frame × ℕ))
                    → waddr < fl
                    → StackWindows am mem stk fl fr
                    → StackWindows am (writeMem mem waddr v') stk fl fr
windows-write-below {am} mem stk waddr v' fl fr lt =
  windows-above {am} mem (writeMem mem waddr v') stk stk fl fr
    (λ a fl≤a → read-write-miss mem waddr v' a (λ eq → <⇒≢ (<-transˡ lt fl≤a) (sym eq)))
    (λ _ _ _ → refl)

-- STACK preservation under a HEAP store, derived rather than assumed: the
-- written cell is mapped, so it is below the frontier (`dom-below`), which is
-- at or below the high-water mark (`front-lo`), which is the frame list's
-- floor. This is what retires the per-site `disj` premise the heap stores used
-- to take — the same argument as the old one-frame `sep`, now for EVERY frame.
windows-heap-store : ∀ {hv : HeapView} {fs : FlatState} {s : X.State}
                       (hl : HeapLocation) (v' : X.Word) → HDom hv hl
                   → (corr : FlatCorr hv fs s)
                   → StackWindows (amap hv) (writeMem (memory s) (haddr hv hl) v')
                                  (stackMem (floc fs)) (lo hv) (frames-of (falloc fs))
windows-heap-store {hv} {fs} {s} hl v' d corr =
  windows-write-below (memory s) (stackMem (floc fs)) (haddr hv hl) v'
    (lo hv) (frames-of (falloc fs)) (<-transˡ (dom-below hv d) (front-lo hv)) (stack-eq corr)

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
  -- (Plan 0.63, D085: the heap/stack disjointness premise is GONE — it is now
  -- `windows-heap-store`, a theorem, and for every live frame rather than only
  -- the current one. Left as a premise it would have done no work.)
  → FlatCorr hv (flat-exec-instr store-indirect [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (haddr hv hl) (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect {hv} hl fs s corr i-eq live-hl guard =
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; dom-written = store-dom-written hv hl v (floc fs) live-hl (dom-written corr)
      ; dom-sized = dom-sized corr
      ; heap-eq = store-heap-eq hv hl v s (floc fs) live-hl (heap-eq corr)
      ; lo-le = lo-le corr
      ; untouched = untouched-heap-store hl (enc-sv hv v) live-hl corr
      ; stack-eq = windows-heap-store hl (enc-sv hv v) live-hl corr }

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [rdi+slot], rax`.
sim-store-indirect-suc : {hv : HeapView} (hl : HeapLocation) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the store target (second cell) is live
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  → FlatCorr hv (flat-exec-instr store-indirect-suc [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (haddr hv (sucHL hl)) (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-suc {hv} hl fs s corr i-eq live-shl guard =
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr
      ; dom-written = store-dom-written hv (sucHL hl) v (floc fs) live-shl (dom-written corr)
      ; dom-sized = dom-sized corr
      ; heap-eq = store-heap-eq hv (sucHL hl) v s (floc fs) live-shl (heap-eq corr)
      ; lo-le = lo-le corr
      ; untouched = untouched-heap-store (sucHL hl) (enc-sv hv v) live-shl corr
      ; stack-eq = windows-heap-store (sucHL hl) (enc-sv hv v) live-shl corr }

------------------------------------------------------------------------
-- STACK RESTORE: `restore-input slot` (Input1 := stack[current-frame, slot]) ↔
-- `mov rdi, [rsp + slot-to-disp slot]`. Identical to load-from-slot but the
-- destination is Input1/rdi (not Output/rax). Success case only; empty slot
-- routed as a residual.
------------------------------------------------------------------------
sim-restore-input : {hv : HeapView} (slot : Slot) (w : StoredValue FS) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → FlatCorr hv (flat-exec-instr (restore-input slot) [] fs)
             (mkstate (xwriteReg (xregs s) in1-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-restore-input {hv} slot w fs s corr st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) in1-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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

atstack-frame-inj : ∀ {f g : Frame} {a b : Slot} → AtStack {FS} f a ≡ AtStack g b → f ≡ g
atstack-frame-inj refl = refl

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
-- ONE-DIRECTION form (Plan 0.54 rung D): the hypothesis and the conclusion both
-- speak only about WRITTEN cells. The `k ≡ slot` case no longer has to say the
-- concrete cell was previously unmapped — it just reads back what was written,
-- which is why this survives frame re-entry over dirty memory.
store-slot-stack-eq : ∀ {am : AddrMap} (base : ℕ) (slot : Slot) (Out : StoredValue FS) (mem : X.Memory) (ls : LocState FS) (cf : Frame) (bound : ℕ)
  → (∀ k → k < bound → ∀ (v : StoredValue FS) → stackMem ls cf k ≡ just v
       → X.readMem mem (base + slot-to-disp k) ≡ just (enc-sv-at am v))
  → ∀ k → k < bound → ∀ (v : StoredValue FS)
  → readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k) ≡ just v
  → X.readMem (writeMem mem (base + slot-to-disp slot) (enc-sv-at am Out)) (base + slot-to-disp k)
      ≡ just (enc-sv-at am v)
store-slot-stack-eq {am} base slot Out mem ls cf bound old k k<b v ev = go (k ≟ slot) ev
  where
    just-inj : ∀ {x y : StoredValue FS} → just x ≡ just y → x ≡ y
    just-inj refl = refl
    go : Dec (k ≡ slot)
       → readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k) ≡ just v
       → X.readMem (writeMem mem (base + slot-to-disp slot) (enc-sv-at am Out)) (base + slot-to-disp k)
           ≡ just (enc-sv-at am v)
    go (yes refl) ev' rewrite ≡ᵇ-refl (base + slot-to-disp slot) =
      cong (λ w → just (enc-sv-at am w))
           (just-inj (trans (sym (writeLoc-read-same-stack ls cf slot Out)) ev'))
    go (no  p)    ev' rewrite ≢→≡ᵇfalse {base + slot-to-disp k} {base + slot-to-disp slot}
                                (λ eq → p (slot-addr-inj base k slot eq)) =
      old k k<b v (trans (sym (writeLoc-preserves-other ls (AtStack cf slot) (AtStack cf k) Out
                                 (λ eq → p (sym (atstack-slot-inj cf eq))))) ev')

-- THE WHOLE FRAME LIST under a stack store at the CURRENT frame's slot. The
-- head window is updated cell by cell (`store-slot-stack-eq`); every OLDER
-- frame is untouched — and BOTH halves of that need `slot < b`:
--   concretely, the write lands strictly below `frame-base cf + slots b`,
--   which is the caller's floor;
--   abstractly, a caller's base is then strictly above `cf`'s, so it is a
--   DIFFERENT FRAME and `writeLoc-preserves-other` applies.
-- Without the bound the claim is FALSE, not merely unprovable: a store past
-- its own reservation is a store into the caller's window. That is why
-- `sim-store-at-slot` now takes it — the emitted-code discipline
-- (`slot-read-in-frame`) supplies it at every call site.
windows-slot-store : ∀ {am : AddrMap} (mem : X.Memory) (ls : LocState FS) (cf : Frame)
                       (b : ℕ) (slot : Slot) (Out : StoredValue FS)
                       (fl : ℕ) (fr : List (Frame × ℕ))
                   → slot < b
                   → StackWindows am mem (stackMem ls) fl ((cf , b) ∷ fr)
                   → StackWindows am (writeMem mem (frame-base cf + slot-to-disp slot) (enc-sv-at am Out))
                                     (stackMem (writeLoc ls (AtStack cf slot) Out)) fl ((cf , b) ∷ fr)
windows-slot-store {am} mem ls cf b slot Out fl fr slot<b (bd , win , rest) =
  bd
  , store-slot-stack-eq {am} (frame-base cf) slot Out mem ls cf b win
  , windows-above {am} mem mem' (stackMem ls) (stackMem (writeLoc ls (AtStack cf slot) Out))
      (frame-base cf + slots b) fr
      (λ a le → read-write-miss mem waddr (enc-sv-at am Out) a
                  (λ eq → <⇒≢ (<-transˡ w<fl le) (sym eq)))
      (λ f' le k → writeLoc-preserves-other ls (AtStack cf slot) (AtStack f' k) Out
                     (λ eq → <-irrefl (cong frame-base (atstack-frame-inj eq)) (base< le)))
      rest
  where
    waddr = frame-base cf + slot-to-disp slot
    mem'  = writeMem mem waddr (enc-sv-at am Out)
    w<fl : waddr < frame-base cf + slots b
    w<fl = +-monoʳ-< (frame-base cf) (*-monoˡ-< slot-size slot<b)
    base< : ∀ {f' : Frame} → frame-base cf + slots b ≤ frame-base f' → frame-base cf < frame-base f'
    base< le = <-transˡ (m<m+n (frame-base cf) (*-monoˡ-< slot-size (<-transʳ z≤n slot<b))) le

sim-store-at-slot : {hv : HeapView} (slot : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  -- THE FRAME DISCIPLINE (Plan 0.63, D085): the written slot is inside the
  -- current frame's own reservation. See `windows-slot-store` — beyond it the
  -- store would silently land in the caller's window.
  → slot < frame-slots (falloc fs)
  -- stack/heap disjointness: the written slot address aliases no live heap cell.
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) sp-reg + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → FlatCorr hv (flat-exec-instr (store-at-slot slot) [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (X.readReg (xregs s) sp-reg + slot-to-disp slot)
                                (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-at-slot {hv} slot fs s corr slot<b disj = corr-clean
  where
    base = X.readReg (xregs s) sp-reg
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    xpost : X.State
    xpost = mkstate (xregs s) (writeMem (memory s) (base + slot-to-disp slot) (enc-sv hv Out))
                    (flags s) (pc s + 1) (xhalted s)
    corr-clean : FlatCorr hv (flat-exec-instr (store-at-slot slot) [] fs) xpost
    corr-clean = record
      { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp slot) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; lo-le = lo-le corr
      ; untouched = untouched-stack-store (base + slot-to-disp slot) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp slot))) corr
      -- the write is re-addressed off the frame BASE (`rsp-eq`), which is the
      -- form every window speaks; `windows-slot-store` does the rest.
      ; stack-eq = subst (λ a → StackWindows (amap hv)
                                             (writeMem (memory s) (a + slot-to-disp slot) (enc-sv hv Out))
                                             (stackMem (writeLoc (floc fs) (AtStack cf slot) Out))
                                             (lo hv) (frames-of (falloc fs)))
                         (sym (rsp-eq corr))
                         (windows-slot-store (memory s) (floc fs) cf (frame-slots (falloc fs))
                            slot Out (lo hv) (saved-frames (falloc fs)) slot<b (stack-eq corr)) }

------------------------------------------------------------------------
-- STACK ALLOCATION: `instr-alloc-stack n` (reserve n slots) ↔ `sub rsp, n*8`.
-- The abstract advances the slot frontier (next-slot += n) and the frame-slots
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
  -- fresh (abstract): the CALLEE frame the reservation moves into is unwritten.
  -- Plan 0.61: the flat machine shifts `current-frame` here, so this is about
  -- the SHIFTED frame — a strictly weaker (and more obviously true) premise
  -- than the old one about the caller's frame.
  → (∀ k → k < n → stackMem (floc fs) (shift-frame (current-frame (falloc fs)) n) k ≡ nothing)
  -- `fresh-x86` IS GONE (Plan 0.54 rung D). It used to demand the concrete cells
  -- below `%rsp` be UNMAPPED, which is false on frame re-entry: `lo` only
  -- descends, so a closure applied twice at one depth re-enters over its
  -- predecessor's live data. With `Window` one-directional the callee's window
  -- is discharged from `fresh-abs` ALONE — no claim is made about a cell the
  -- abstract side has not written, so the dirty concrete cells are irrelevant.
  -- THE DESCENT (plan 0.54 rung D step 3): %rsp drops, so the high-water mark
  -- drops with it. `lo'` is chosen at the dispatch site as `lo hv ⊓ (rsp ∸ 8n)`,
  -- whose `hfront hv ≤ lo'` is where the ROOM premise (`stack-room` — STACK
  -- OVERFLOW, the honest exhaustion assumption) is spent. The mark only ever moves
  -- DOWN, so re-entering a frame that was already reached does not (falsely)
  -- re-declare its cells virgin.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) sp-reg ∸ slots n
  -- THE FRAME FITS (Plan 0.63, D085): the reservation does not run `%rsp` off
  -- the bottom of the address space. Without it `frame-base (shift cf n) + 8n`
  -- is `max(frame-base cf, 8n)` (truncated ∸), so the callee's window would not
  -- be provably BELOW the caller's and the frame list would not compose. The
  -- honest sibling of `heap-room`: stack overflow, spent here.
  → slots n ≤ X.readReg (xregs s) sp-reg
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (flat-exec-instr (instr-alloc-stack n) [] fs)
             (mkstate (xwriteReg (xregs s) sp-reg (X.readReg (xregs s) sp-reg ∸ slots n))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-alloc-stack {hv} n newFlags fs s corr fresh-abs lo' lo'≤lo front-lo' lo'≤sp-reg fits = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr
  -- the reservation moves %rsp DOWN n slots and the frame with it (`shift-base`)
  ; rsp-eq = newbase
  ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = heap-eq corr
  ; lo-le = lo'≤sp-reg
  ; untouched = untouched-descend lo' lo'≤lo front-lo' corr
  -- Plan 0.63: the prologue CONSES a frame (`enter-frame n`), so the post's
  -- windows are the callee's — bounded by its own reservation `n`, and fresh on
  -- both sides — on top of the pre-state's, whose floor rises from `lo` to the
  -- callee's window END. That end IS the caller's base (`fits`), so the caller's
  -- window is carried across the call untouched rather than dropped.
  ; stack-eq = subst (lo' ≤_) newbase lo'≤sp-reg
             , win-at (amap hv) (memory s) (stackMem (floc fs)) (shift-frame cf n) n
                       (X.readReg (xregs s) sp-reg ∸ slots n) newbase stk
             , windows-reanchor (lo hv) (frame-base (shift-frame cf n) + slots n)
                 cf (frame-slots (falloc fs)) (saved-frames (falloc fs)) tail-le (stack-eq corr) }
  where
    cf = current-frame (falloc fs)
    newbase : X.readReg (xregs s) sp-reg ∸ slots n ≡ frame-base (shift-frame cf n)
    newbase = trans (cong (_∸ slots n) (rsp-eq corr))
                    (trans (cong (λ w → frame-base cf ∸ n * w) (sym word-eq))
                           (sym (shift-base cf n)))
    -- VACUOUS: the callee frame is unwritten (`fresh-abs`), and the one-directional
    -- `Window` claims nothing about unwritten cells. The hypothesis `stackMem … ≡
    -- just v` contradicts `fresh-abs` outright.
    stk : ∀ k → k < n → ∀ (v : StoredValue FS)
        → stackMem (floc fs) (shift-frame cf n) k ≡ just v
        → X.readMem (memory s) ((X.readReg (xregs s) sp-reg ∸ slots n) + slot-to-disp k)
            ≡ just (enc-sv-at (amap hv) v)
    stk k k<n v ev with trans (sym (fresh-abs k k<n)) ev
    ... | ()
    -- the callee's window ends exactly at the caller's base: `(rsp ∸ 8n) + 8n`
    -- is `rsp` because the frame FITS, and `rsp` is the caller's base.
    tail-le : frame-base (shift-frame cf n) + slots n ≤ frame-base cf
    tail-le = ≤-reflexive (trans (cong (_+ slots n) (sym newbase))
                                 (trans (m∸n+n≡m fits) (rsp-eq corr)))

------------------------------------------------------------------------
-- THE CLOSURE BODY'S RESERVATION: `c-thunk _ b` ↔ `label (thunk _) ; sub rsp, 8b`.
--
-- D086: this GROWS the frame the CALL already entered rather than pushing a new
-- one — the concrete `call` already consumed one slot for the return address,
-- and that slot is not abstractly addressable (it holds a code address, which
-- lives in the ghost `fret`). So `grow-frame` shifts the current frame and
-- resets its reservation, leaving `saved-frames` ALONE.
--
-- The window story differs from `sim-alloc-stack` accordingly: there is no new
-- saved frame, the OLD current window is simply replaced, and the saved frames
-- are re-anchored at the grown window's END — which `fits` places exactly at
-- the old base, so `windows-lower` carries them across.
--
-- Unblocked by the one-directional `Window` (Plan 0.54 rung D): this used to be
-- unprovable because the callee's window demanded UNMAPPED concrete cells, and
-- a closure applied twice at one depth re-enters over its predecessor's data.
-- The head window is now vacuous from `fresh-abs` alone.
------------------------------------------------------------------------
sim-thunk : {hv : HeapView} (b : ℕ) (newFlags : X.Flags) (newPc : ℕ)
            (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  -- NO `fresh-abs` PREMISE (Plan 0.54 rung D): `do-thunk` CLEARS the entered
  -- frame, so the callee window is vacuous by COMPUTATION rather than by
  -- assumption. Postulating freshness here would have been assuming something
  -- false — a re-entered frame keeps the previous incarnation's writes unless
  -- the machine clears them, which is why the fix belongs in `do-thunk`.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) sp-reg ∸ slots b
  → slots b ≤ X.readReg (xregs s) sp-reg
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (do-thunk b fs)
             (mkstate (xwriteReg (xregs s) sp-reg (X.readReg (xregs s) sp-reg ∸ slots b))
                      (memory s) newFlags newPc (xhalted s))
sim-thunk {hv} b newFlags newPc fs s corr lo' lo'≤lo front-lo' lo'≤sp-reg fits = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr
  ; rsp-eq = newbase
  ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr
  ; dom-sized = dom-sized corr
  ; heap-eq = heap-eq corr
  ; lo-le = lo'≤sp-reg
  ; untouched = untouched-descend lo' lo'≤lo front-lo' corr
  ; stack-eq = subst (lo' ≤_) newbase lo'≤sp-reg
             , head-window
             , windows-forget (stackMem (floc fs)) (stackMem (floc (do-thunk b fs)))
                 (frame-base (shift-frame cf b) + slots b) (saved-frames (falloc fs))
                 (λ f' k' v' → MemOps.clear-frame-just (stackMem (floc fs))
                                 (shift-frame cf b) b f' k' v')
                 (windows-lower (frame-base cf + slots (frame-slots (falloc fs)))
                    (frame-base (shift-frame cf b) + slots b)
                    (saved-frames (falloc fs))
                    (≤-trans tail-le (m≤m+n (frame-base cf) (slots (frame-slots (falloc fs)))))
                    (proj₂ (proj₂ (stack-eq corr)))) }
  where
    cf = current-frame (falloc fs)
    nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
    nothing≢just ()
    -- the entered frame reads `nothing` below its reservation, by `clear-frame`
    head-window : ∀ (k : Slot) → k < b → ∀ (v : StoredValue FS)
                → stackMem (floc (do-thunk b fs)) (shift-frame cf b) k ≡ just v
                → X.readMem (memory s) (frame-base (shift-frame cf b) + slot-to-disp k)
                    ≡ just (enc-sv-at (amap (descend-view hv lo' lo'≤lo front-lo')) v)
    head-window k k<b v ev with FrameSemantics._≟F_ FS (shift-frame cf b) (shift-frame cf b) | Data.Nat.Properties._<?_ k b
    ... | yes _ | yes _ = ⊥-elim (nothing≢just ev)
    ... | yes _ | no ¬p = ⊥-elim (¬p k<b)
    ... | no ¬q | _     = ⊥-elim (¬q refl)
    newbase : X.readReg (xregs s) sp-reg ∸ slots b ≡ frame-base (shift-frame cf b)
    newbase = trans (cong (_∸ slots b) (rsp-eq corr))
                    (trans (cong (λ w → frame-base cf ∸ b * w) (sym word-eq))
                           (sym (shift-base cf b)))
    tail-le : frame-base (shift-frame cf b) + slots b ≤ frame-base cf
    tail-le = ≤-reflexive (trans (cong (_+ slots b) (sym newbase))
                                 (trans (m∸n+n≡m fits) (rsp-eq corr)))

------------------------------------------------------------------------
-- THE CALL (D098): `instr-call-closure` ↔ `call *0x8(%r12)`.
--
-- The concrete call does three things at once — lower `%rsp` by a slot, STORE
-- the return address in it, and transfer control — and the abstract
-- `enter-call` mirrors the first (D086: a frame one slot down, reserving
-- nothing) while the ghost `fret` takes the third's residue. This lemma is the
-- data half; the pc is `CompiledCorr`'s business, so the target enters as `j`.
--
-- The written cell is BELOW every live frame's base, so nothing already
-- corresponded to it: the head window of the entered frame is vacuous (0
-- slots), and the caller's windows are untouched by a write under them. That is
-- the same separation `ret-write-in-frame` uses, read from the other side.
------------------------------------------------------------------------
-- `jₐ` is the ABSTRACT pc the call lands on and `newPc` the concrete one; they
-- are different numbers (`blk-off` apart) and `FlatCorr` constrains neither —
-- relating them is `CompiledCorr.pc-off`'s job.
sim-call : {hv : HeapView} (jₐ newPc retAddr : ℕ) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ X.readReg (xregs s) sp-reg ∸ slot-size
  -- ROOM FOR THE RETURN ADDRESS: the one slot the call spends. Same class as
  -- `StackRoom` (D087) and supplied the same way.
  → slot-size ≤ X.readReg (xregs s) sp-reg
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (record fs { falloc = enter-call (falloc fs)
                        ; fret   = suc (fpc fs) ∷ fret fs
                        ; fpc    = jₐ })
             (mkstate (xwriteReg (xregs s) sp-reg (X.readReg (xregs s) sp-reg ∸ slot-size))
                      (writeMem (memory s) (X.readReg (xregs s) sp-reg ∸ slot-size) retAddr)
                      (flags s) newPc (xhalted s))
sim-call {hv} jₐ newPc retAddr fs s corr lo' lo'≤lo front-lo' lo'≤sp-reg fits = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr
  ; r14-eq = r14-eq corr ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr
  ; rsp-eq = newbase
  ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr
  ; dom-sized = dom-sized corr
  -- the heap is under the frontier, the write is at or above the descended
  -- mark, and the mark is above the frontier — so the store misses every cell
  ; heap-eq = λ hl d → trans (read-write-miss (memory s) waddr retAddr (haddr hv hl)
                               (λ eq → <⇒≢ (<-transˡ (dom-below hv d)
                                              (≤-trans front-lo' lo'≤sp-reg)) eq))
                             (heap-eq corr hl d)
  ; lo-le = lo'≤sp-reg
  ; untouched = λ a fa a<lo' → trans (read-write-miss (memory s) waddr retAddr a
                                       (λ eq → <⇒≢ (<-transˡ a<lo' lo'≤sp-reg) eq))
                                     (untouched-descend lo' lo'≤lo front-lo' corr a fa a<lo')
  ; stack-eq = subst (lo' ≤_) newbase lo'≤sp-reg
             , (λ k ())
             , windows-reanchor (frame-base cf) (frame-base (shift-frame cf 1) + slots 0)
                 cf (frame-slots (falloc fs)) (saved-frames (falloc fs))
                 tail-floor
                 (windows-above (memory s) (writeMem (memory s) waddr retAddr)
                    (stackMem (floc fs)) (stackMem (floc fs))
                    (frame-base cf) ((cf , frame-slots (falloc fs)) ∷ saved-frames (falloc fs))
                    (λ a le → read-write-miss (memory s) waddr retAddr a
                                (λ eq → <⇒≢ (<-transˡ w<base le) (sym eq)))
                    (λ _ _ _ → refl)
                    (windows-reanchor (lo hv) (frame-base cf) cf (frame-slots (falloc fs))
                       (saved-frames (falloc fs)) ≤-refl (stack-eq corr))) }
  where
    cf    = current-frame (falloc fs)
    waddr = X.readReg (xregs s) sp-reg ∸ slot-size
    newbase : X.readReg (xregs s) sp-reg ∸ slot-size ≡ frame-base (shift-frame cf 1)
    newbase = trans (cong (_∸ slot-size) (rsp-eq corr))
                    (trans (cong (λ w → frame-base cf ∸ 1 * w) (sym word-eq))
                           (sym (shift-base cf 1)))
    -- the tail's floor is the entered frame's window END, and that frame
    -- reserves NOTHING — so the floor is its own base, one slot under the
    -- caller's, which is the gap the return address occupies (D086)
    tail-floor : frame-base (shift-frame cf 1) + slots 0 ≤ frame-base cf
    tail-floor =
      ≤-trans (≤-reflexive (trans (+-identityʳ (frame-base (shift-frame cf 1))) (sym newbase)))
              (≤-trans (m∸n≤m (X.readReg (xregs s) sp-reg) slot-size)
                       (≤-reflexive (rsp-eq corr)))
    -- the write lands strictly below the caller's base — that is the slot the
    -- call spends, and `fits` is what says it exists
    w<base : X.readReg (xregs s) sp-reg ∸ slot-size < frame-base cf
    w<base = subst (X.readReg (xregs s) sp-reg ∸ slot-size <_) (rsp-eq corr)
                   (m∸n<m′ fits)
      where m∸n<m′ : slot-size ≤ X.readReg (xregs s) sp-reg
                   → X.readReg (xregs s) sp-reg ∸ slot-size < X.readReg (xregs s) sp-reg
            m∸n<m′ le = subst (suc (X.readReg (xregs s) sp-reg ∸ slot-size) ≤_)
                              (m∸n+n≡m le)
                              (m<m+n (X.readReg (xregs s) sp-reg ∸ slot-size) (s≤s z≤n))

------------------------------------------------------------------------
-- STACK DEALLOCATION: `instr-dealloc-stack n` (free n slots) ↔ `add rsp, n*8`.
-- The epilogue restores the CALLER's frame and, with it, the caller's coverage
-- window.
--
-- PLAN 0.63 (D085) — RESOLVED. Before the `frame-slots` mirror was removed
-- (D084), the post-state's bound was `frame-slots ∸ n`, which a full-frame exit
-- made `0`, so this obligation was VACUOUS and the question never came up. With
-- the bound the restored frame's own `frame-slots`, the post genuinely has to
-- say something about the CALLER's window — which the one-frame `stack-eq`
-- could not supply, so it was an explicit `caller-window` PREMISE naming the
-- gap. Now `stack-eq` is scoped over the whole frame stack and the premise IS
-- the tail of the pre-state's evidence: `windows-leave`, a theorem. The
-- premise is deleted rather than left for call sites to supply.
--
-- The 4 tracked regs / halt / heap are untouched (dealloc changes neither
-- falloc's heap fields nor stackMem). Flag-parametric.
------------------------------------------------------------------------
sim-dealloc-stack : {hv : HeapView} (n : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  -- MATCHED PAIRING (plan 0.61): the frame this epilogue restores is the one the
  -- entry `alloc-stack n` shifted away from, so its base is where %rsp lands.
  → X.readReg (xregs s) sp-reg + slots n
      ≡ frame-base (current-frame (leave-frame (falloc fs)))
  → FlatCorr hv (flat-exec-instr (instr-dealloc-stack n) [] fs)
             (mkstate (xwriteReg (xregs s) sp-reg (X.readReg (xregs s) sp-reg + slots n))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-dealloc-stack {hv} n newFlags fs s corr restores = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = restores ; r15-eq = r15-eq corr
  -- the epilogue RAISES %rsp, so the high-water mark stays below it — and the mark
  -- itself does NOT move back up: the freed cells keep their contents, which is
  -- exactly the dead memory the mark exists to remember.
  ; lo-le = ≤-trans (lo-le corr) (m≤m+n (X.readReg (xregs s) sp-reg) (slots n))
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
  -- THE RETURN'S WINDOW, DERIVED: drop the callee's frame and the caller's
  -- window is what is left (`windows-leave`).
  ; stack-eq = windows-leave (falloc fs) (lo hv) (stack-eq corr) }

------------------------------------------------------------------------
-- THE RETURN (D095): `c-ret b` ↔ `add rsp, 8b ; ret`.
--
-- Almost exactly `sim-dealloc-stack` — both release the current frame and land
-- `%rsp` on the caller's base — with two differences that are the whole point
-- of the return: `%rsp` rises by one slot MORE (the `ret` pops the address the
-- call pushed), and the pc goes to that address rather than to the next
-- instruction. The pc is `CompiledCorr`'s business, so it enters here only as
-- the opaque `npc`.
--
-- `restores` is not a fresh assumption: it is `RetAddrs`' own `GapNext`, read
-- through `rsp-eq`. That is why the gap lives in the component — the return is
-- the one step that needs it as an EQUALITY.
------------------------------------------------------------------------
sim-ret : {hv : HeapView} (b rpc : ℕ) (rest : List ℕ) (newFlags : X.Flags) (npc : ℕ)
          (fs : FlatState) (s : X.State) → FlatCorr hv fs s
        → fret fs ≡ rpc ∷ rest
        → X.readReg (xregs s) sp-reg + slots b + slot-size
            ≡ frame-base (current-frame (leave-frame (falloc fs)))
        → FlatCorr hv (do-ret (fret fs) fs)
                   (mkstate (xwriteReg (xwriteReg (xregs s) sp-reg (X.readReg (xregs s) sp-reg + slots b))
                                       sp-reg (X.readReg (xregs s) sp-reg + slots b + slot-size))
                            (memory s) newFlags npc (xhalted s))
sim-ret {hv} b rpc rest newFlags npc fs s corr req restores rewrite req = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr
  ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = restores ; r15-eq = r15-eq corr
  -- `%rsp` only RISES, so the high-water mark stays below it and the freed
  -- cells keep their contents — the dead memory the mark exists to remember.
  ; lo-le = ≤-trans (lo-le corr)
              (≤-trans (m≤m+n (X.readReg (xregs s) sp-reg) (slots b))
                       (m≤m+n (X.readReg (xregs s) sp-reg + slots b) slot-size))
  ; untouched = untouched corr
  ; dom-fresh = λ {hl} d → subst (λ m → ref-id (heap-ref hl) < m)
                                 (sym (leave-frame-heap-ref (falloc fs))) (dom-fresh corr d)
  ; dom-written = dom-written corr
  ; dom-sized = λ hl lt → dom-sized corr hl
                  (subst (λ szs → heap-offset hl < szs (ref-id (heap-ref hl)))
                         (leave-frame-block-size (falloc fs)) lt)
  ; heap-eq = heap-eq corr
  -- drop the callee's frame and the caller's window is what is left
  ; stack-eq = windows-leave (falloc fs) (lo hv) (stack-eq corr) }

------------------------------------------------------------------------
-- FRAME PUSH / POP: the `%rbp` frame model is a FOSSIL — `sim-push-frame`
-- and `sim-pop-frame` were deleted 2026-08-04 together with their
-- block-steps. The live model is frameless and `%rsp`-relative; Plan 0.63's
-- closure frames ride on `sim-alloc-stack`/`sim-dealloc-stack` above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- LOAD CONST (int): `instr-load-const fits-int v` (Output := SV-Lit fits-int v)
-- ↔ `mov rax, imm v`. With enc-sv(SV-Lit fits-int v) = v, the loaded immediate
-- matches the encoded literal exactly, so rax-eq is refl; nothing else changes
-- (writeReg Output preserves the other regs / stack / heap / halt).
------------------------------------------------------------------------
sim-load-const : {hv : HeapView} (v : Carrier) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-const fits-int v) [] fs)
             (mkstate (xwriteReg (xregs s) out-reg (lit-word v)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-const {hv} v fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- …and the FLOAT constant (D079): identical, with the IEEE-754 pattern as
-- the immediate — `enc-sv (SV-Lit fits-float v)` IS `float-bits v`, so
-- `rax-eq` is `refl` exactly as in the int case.
sim-load-const-float : {hv : HeapView} (v : AgdaFloat) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr (instr-load-const fits-float v) [] fs)
             (mkstate (xwriteReg (xregs s) out-reg (float-bits v)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-const-float {hv} v fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = refl ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- LOAD CODE ADDR: `instr-load-code-addr n` (Output := SV-Code n) ↔ `lea rax,
-- .L_thunk_n(%rip)`.
--
-- D096: `rax-eq` used to be `refl` because BOTH sides said `idx n` — the
-- label's IDENTITY. That agreement was the defect: the concrete `lea` now
-- RESOLVES the label (as `jmp` does), so the value is the body's index, and the
-- view's code map has to be that resolution. The lemma therefore takes the
-- resolved value and the equation tying the map to it; the block-step supplies
-- both, from the program it can see and `CompiledCorr.code-eq`.
------------------------------------------------------------------------
sim-load-code-addr : {hv : HeapView} (n : LabelId) (j : ℕ) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → caddr hv n ≡ j
  → FlatCorr hv (flat-exec-instr (instr-load-code-addr n) [] fs)
             (mkstate (xwriteReg (xregs s) out-reg j) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-code-addr {hv} n j fs s corr ceq = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = sym ceq ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

------------------------------------------------------------------------
-- SAVE CLOSURE REG: `instr-save-closure-reg` ↔ `mov r12, rdi`.
--
-- This USED to be "the correspondence is unchanged" — `%r12` was untracked and
-- the abstract side was the identity. Both halves moved: D092 made the flat
-- machine write `fclosure`, and D097 made `FlatCorr` track `%r12`. So the step
-- now has real content, and it is exactly the same equation twice: what `%rdi`
-- holds is what `Input1` holds, before and after the pair of copies.
------------------------------------------------------------------------
sim-save-closure-reg : {hv : HeapView} (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → FlatCorr hv (flat-exec-instr instr-save-closure-reg [] fs)
             (mkstate (xwriteReg (xregs s) clos-reg (xreadReg (xregs s) in1-reg)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-save-closure-reg {hv} fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; r12-eq = rdi-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
             (mkstate (xwriteReg (xregs s) count-reg (xreadReg (xregs s) count-reg + 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-count-inc {hv} k newFlags fs s corr c-eq = record
  { rdi-eq = rdi-eq corr ; rax-eq = rax-eq corr ; rbx-eq = rbx-eq corr ; rsi-eq = rsi-eq corr
  ; r14-eq = trans (cong (_+ 1) (r14-eq corr)) (inc-enc (readReg (regs (floc fs)) Count) k c-eq)
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

sim-reg-scratch-dec : {hv : HeapView} (k : ℕ) (newFlags : X.Flags) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-dec) [] fs)
             (mkstate (xwriteReg (xregs s) scratch-reg (xreadReg (xregs s) scratch-reg ∸ 1))
                      (memory s) newFlags (pc s + 1) (xhalted s))
sim-reg-scratch-dec {hv} k newFlags fs s corr sc-eq = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rax-eq = rax-eq corr ; r14-eq = r14-eq corr
  ; rbx-eq = trans (cong (_∸ 1) (rbx-eq corr)) (dec-enc (readReg (regs (floc fs)) Scratch) k sc-eq)
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

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
  -- D096: an allocation extends the HEAP map; the code map is a property of
  -- the PROGRAM, so it rides through untouched.
  ; caddr     = caddr hv
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

-- …and every window survives the extension, for the same reason: the only
-- values whose encoding could move are pointers into the fresh ref, and a
-- well-formed state has none ANYWHERE — the store-WF invariant is already
-- quantified over all frames (`FlatWF.wf-stack`), so this needs no new fact.
windows-enc-ext : ∀ (hv : HeapView) (st n : ℕ)
                    (pf : ∀ {hl : HeapLocation} → HDom hv hl → ref-id (heap-ref hl) < st)
                    (rm : hfront hv + slots n ≤ lo hv)
                    (mem : X.Memory) (stk : StackMem FS) (fl : ℕ) (fr : List (Frame × ℕ))
                → (∀ (f : Frame) (k : Slot) → svm-below st (stk f k))
                → StackWindows (amap hv) mem stk fl fr
                → StackWindows (amap (extend-view hv st n pf rm)) mem stk fl fr
windows-enc-ext hv st n pf rm mem stk fl []             wf w = tt
windows-enc-ext hv st n pf rm mem stk fl ((f , b) ∷ fr) wf (bd , win , rest) =
  bd
  , (λ k k<b v ev → trans (win k k<b v ev)
                          (cong just (sym (enc-ext hv st n pf rm v
                                             (subst (svm-below st) ev (wf f k))))))
  , windows-enc-ext hv st n pf rm mem stk (frame-base f + slots b) fr wf rest


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
  -- …and the CLOSURE REGISTER (D097): it is a `FlatState` field rather than a
  -- register, so `FlatWF` does not cover it — the run invariant supplies this
  -- one, exactly as it supplies the four above.
  → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
  → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
  -- Plan 0.63 (D085): over EVERY frame, not just the current one — which is
  -- the form `FlatWF.wf-stack` already has, so the call sites got shorter.
  → (∀ (f : Frame) (k : Slot) → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) f k))
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
             (mkstate (xwriteReg (xwriteReg (xregs s) out-reg (X.readReg (xregs s) heap-reg)) heap-reg
                                 (X.readReg (xregs s) heap-reg + slots n))
                      (memory s) newFlags newPc (xhalted s))
sim-alloc-heap {hv} n newFlags newPc fs s corr wf1 wf2 wfs wfc wfcl wf-heap wf-stack fresh-abs room = record
  { rdi-eq  = trans (rdi-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Input1) wf1))
  ; rsi-eq  = trans (rsi-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Input2) wf2))
  ; r14-eq  = trans (r14-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Count) wfc))
  ; rax-eq  = trans (r15-eq corr) (sym (ext-addr-base hv st))
  ; rbx-eq  = trans (rbx-eq corr) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Scratch) wfs))
  ; r12-eq  = trans (r12-eq corr) (sym (enc-ext hv st n dfr room (fclosure fs) wfcl))
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
  ; stack-eq = windows-enc-ext hv st n dfr room (memory s) (stackMem (floc fs))
                 (lo hv) (frames-of (falloc fs)) wf-stack (stack-eq corr)
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
             (mkstate (xwriteReg (xregs s) out-reg (X.readReg (xregs s) sp-reg + slot-to-disp slot))
                      (memory s) (flags s) (pc s + 1) (xhalted s))
sim-lea-slot {hv} slot fs s corr = record
  { rdi-eq = rdi-eq corr ; rsi-eq = rsi-eq corr ; rbx-eq = rbx-eq corr ; r14-eq = r14-eq corr
  ; rax-eq = addr-eq
  ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
  ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }
  where
    cf = current-frame (falloc fs)
    addr-eq : X.readReg (xregs s) sp-reg + slot-to-disp slot ≡ slot-addr cf slot
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
             (mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-stack {hv} f k w fs s corr i-eq st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- Second cell through a STACK pointer: `sucLoc (AtStack f k) = AtStack f (suc k)`,
-- so this is `sim-load-indirect-stack` one slot along.
sim-load-indirect-suc-stack : {hv : HeapView} (f : Frame) (k : Slot) (w : StoredValue FS)
                              (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → readLoc (floc fs) (AtStack f (suc k)) ≡ just w
  → FlatCorr hv (flat-exec-instr load-indirect-suc [] fs)
             (mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s))
sim-load-indirect-suc-stack {hv} f k w fs s corr i-eq st-eq =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    xpost : X.State
    xpost = mkstate (xwriteReg (xregs s) out-reg (enc-sv hv w)) (memory s) (flags s) (pc s + 1) (xhalted s)
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = heap-eq corr ; lo-le = lo-le corr ; untouched = untouched corr ; stack-eq = stack-eq corr }

-- STORE through a stack pointer: `writeLoc … (AtStack f k)` IS the plain stack
-- write (the cross-region guard only concerns the heap branch), so this reuses
-- the same read-back/disjointness machinery as `sim-store-at-slot` — the only
-- difference is that the address comes from `Input1` rather than the instruction.
sim-store-indirect-stack : {hv : HeapView} (k : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
  -- the frame discipline, as for `sim-store-at-slot` (`stack-ptr-current`)
  → k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) sp-reg + slot-to-disp k ≡ haddr hv hl') → ⊥)
  → FlatCorr hv (flat-exec-instr store-indirect [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (X.readReg (xregs s) sp-reg + slot-to-disp k)
                                (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-stack {hv} k fs s corr i-eq k<b disj =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    base = X.readReg (xregs s) sp-reg
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp k) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; lo-le = lo-le corr
      ; untouched = untouched-stack-store (base + slot-to-disp k) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp k))) corr
      ; stack-eq = subst (λ a → StackWindows (amap hv)
                                             (writeMem (memory s) (a + slot-to-disp k) (enc-sv hv Out))
                                             (stackMem (writeLoc (floc fs) (AtStack cf k) Out))
                                             (lo hv) (frames-of (falloc fs)))
                         (sym (rsp-eq corr))
                         (windows-slot-store (memory s) (floc fs) cf (frame-slots (falloc fs))
                            k Out (lo hv) (saved-frames (falloc fs)) k<b (stack-eq corr)) }

-- …and the SECOND cell. `sucLoc (AtStack cf k) = AtStack cf (suc k)` reduces, so
-- this is literally the same proof at slot `suc k` — `store-slot-stack-eq` is
-- generic in the written slot, and the pair's second slot belongs to the same
-- frame the prologue reserved (`stack-ptr-current-suc`).
sim-store-indirect-suc-stack : {hv : HeapView} (k : Slot) (fs : FlatState) (s : X.State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
  -- the PAIR's second slot is the one reserved (`stack-ptr-current-suc`)
  → suc k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (X.readReg (xregs s) sp-reg + slot-to-disp (suc k) ≡ haddr hv hl') → ⊥)
  → FlatCorr hv (flat-exec-instr store-indirect-suc [] fs)
             (mkstate (xregs s)
                      (writeMem (memory s) (X.readReg (xregs s) sp-reg + slot-to-disp (suc k))
                                (enc-sv hv (readReg (regs (floc fs)) Output)))
                      (flags s) (pc s + 1) (xhalted s))
sim-store-indirect-suc-stack {hv} k fs s corr i-eq sk<b disj =
  subst (λ z → FlatCorr hv z xpost) (sym reduces) corr-clean
  where
    base = X.readReg (xregs s) sp-reg
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
      ; r12-eq = r12-eq corr ; halt-eq = halt-eq corr ; rsp-eq = rsp-eq corr ; r15-eq = r15-eq corr
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp (suc k)) (enc-sv hv Out) s (floc fs)
                    (heap-eq corr) disj
      ; lo-le = lo-le corr
      ; untouched = untouched-stack-store (base + slot-to-disp (suc k)) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp (suc k)))) corr
      ; stack-eq = subst (λ a → StackWindows (amap hv)
                                             (writeMem (memory s) (a + slot-to-disp (suc k)) (enc-sv hv Out))
                                             (stackMem (writeLoc (floc fs) (AtStack cf (suc k)) Out))
                                             (lo hv) (frames-of (falloc fs)))
                         (sym (rsp-eq corr))
                         (windows-slot-store (memory s) (floc fs) cf (frame-slots (falloc fs))
                            (suc k) Out (lo hv) (saved-frames (falloc fs)) sk<b (stack-eq corr)) }

-- THE PENDING RETURNS SURVIVE A WRITE THAT MISSES THEM (D093), in the two
-- shapes the emitted code produces. Both mirror `windows-above` — a return
-- cell is a frame's window END, hence at or above that frame's base, hence
-- above the floor the frame list threads.
--
-- (1) A change confined BELOW the floor — every heap store, since a live heap
-- cell is under `hfront ≤ lo ≤ %rsp`.
ret-agree-above : ∀ (xoff : ℕ → ℕ) {am : AddrMap} (mem mem' : X.Memory) (stk : StackMem FS)
                    (fl : ℕ) (fr : List (Frame × ℕ)) (rs : List ℕ)
                → (∀ (a : ℕ) → fl ≤ a → X.readMem mem' a ≡ X.readMem mem a)
                → StackWindows am mem stk fl fr
                → RetAddrs xoff mem fr rs → RetAddrs xoff mem' fr rs
ret-agree-above xoff mem mem' stk fl fr             []       ag sw r = tt
ret-agree-above xoff mem mem' stk fl []             (x ∷ rs) ag sw ()
ret-agree-above xoff mem mem' stk fl ((f , b) ∷ fr) (x ∷ rs) ag (bd , win , rest) (h , g , t) =
  trans (ag (frame-base f + slots b) (≤-trans bd (m≤m+n (frame-base f) (slots b)))) h
  , g
  , ret-agree-above xoff mem mem' stk (frame-base f + slots b) fr rs
      (λ a le → ag a (≤-trans (≤-trans bd (m≤m+n (frame-base f) (slots b))) le))
      rest t

-- (2) A write INSIDE the current frame's window — every stack store, whose
-- slot is below the reservation (`slot < b`, the emitted-code discipline). The
-- head's own cell is the window END, strictly above the write; everything
-- older is above that end by the floor thread. This is the D086 gap doing its
-- job: the return address sits in it, and nothing the frame writes can reach.
ret-write-in-frame : ∀ (xoff : ℕ → ℕ) {am : AddrMap} (mem : X.Memory) (stk : StackMem FS)
                       (a : ℕ) (v : X.Word) (fl : ℕ) (f : Frame) (b : ℕ)
                       (fr : List (Frame × ℕ)) (rs : List ℕ)
                   → a < frame-base f + slots b
                   → StackWindows am mem stk fl ((f , b) ∷ fr)
                   → RetAddrs xoff mem ((f , b) ∷ fr) rs
                   → RetAddrs xoff (writeMem mem a v) ((f , b) ∷ fr) rs
ret-write-in-frame xoff mem stk a v fl f b fr []       lt sw r = tt
ret-write-in-frame xoff {am} mem stk a v fl f b fr (x ∷ rs) lt (bd , win , rest) (h , g , t) =
  trans (read-write-miss mem a v (frame-base f + slots b) (λ eq → <⇒≢ lt (sym eq))) h
  , g
  , ret-agree-above xoff mem (writeMem mem a v) stk (frame-base f + slots b) fr rs
      (λ c le → read-write-miss mem a v c (λ eq → <⇒≢ (<-transˡ lt le) (sym eq)))
      rest t
