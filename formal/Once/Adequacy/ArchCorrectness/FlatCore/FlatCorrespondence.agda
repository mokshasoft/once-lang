-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
--
-- THE VALUE-ENCODING CORRESPONDENCE, arch-generic (plan 0.65 G1c step 4).
--
-- `FlatCorr` relates a FLAT abstract state to a machine state: the eight
-- registers by ROLE under `enc-sv`, the halt flag, the heap under the carried
-- address map, and every LIVE stack frame. Plus the 33 per-instruction
-- simulation lemmas, the four post-state records, and the window/return-address
-- machinery they run on.
--
-- WHAT THE ARCH SUPPLIES, and why it is only this. G1c steps 1–3 made this
-- module state-shape-agnostic in place: the registers became ROLES, and every
-- `sim-*` stopped BUILDING a post-state and started saying what must HOLD of
-- one. What was left mentioning the machine afterwards was a state TYPE and
-- three observations of it, so that is the whole interface:
--
--     State   rreg : State → Reg → Word    memory : State → Memory
--                                          xhalted : State → Bool
--
-- Flags never appear — not because they are abstracted, but because a
-- correspondence that does not construct states has nowhere to put them.
-- Neither does a pc: `FlatCorr` has no pc field, that discipline living one
-- layer up in the block-steps.
--
-- WORD AND MEMORY ARE NOT PARAMETERS — and the reason is weaker than it looks,
-- so it is stated honestly (2026-08-13). All three target MODELS define
-- `Word = ℕ`, a memory as `ℕ → Maybe ℕ`, and reading/writing as application
-- and update, so nothing here has to abstract over them.
--
-- That is a fact about the current models, NOT about the machines. A real
-- register is a fixed-width modular word: `add` wraps at 2^64 and `sub` of a
-- larger value gives the two's-complement result, whereas these models use
-- unbounded `_+_` and TRUNCATED `_∸_`, which clamps at zero. D054 already
-- decided that Once's own `Int` denotes a modular `Once.Word`, so the tree
-- carries both notions and they meet at `lit-word : Carrier → Word` a few
-- lines below. See the residual ledger's "THE UNBOUNDED-REGISTER MODEL" for
-- why this correspondence is nevertheless TRUE, and where the divergence
-- actually lands.
--
-- Only `writeReg` genuinely cannot cross — it is a record update on a
-- particular register file — which is why the four REALISERS stay in the arch
-- layer and are the only things there.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.Word using (Carrier)
open import Once.Type using (Int; Float; fits-int; fits-float)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Label using (LabelId; idx)
open import Data.Nat using (ℕ; _*_; NonZero; _<_; suc; zero; s≤s; z≤n)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles
  using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1; role-scratch; role-count)
open import Once.Float.Dyadic using (Dyadic)

module Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence
  (FS : FrameSemantics)
  (slot-size : ℕ)
  -- A SLOT IS NOT ZERO BYTES WIDE. With a concrete `slot-size` Agda found this
  -- instance itself; as a parameter it has to be said, and it is load-bearing
  -- rather than pedantic: `slot-addr-inj` turns distinct slots into distinct
  -- addresses by cancelling `* slot-size`, and at 0 every slot would alias.
  ⦃ slot-size-nz : NonZero slot-size ⦄
  -- The frame semantics' slot size IS this target's (`refl` at instantiation).
  (word-eq : frame-word FS ≡ slot-size)
  -- the machine, as far as a correspondence can see it
  (Reg : Set)
  (roles : RegRoles Reg)
  (State : Set)
  (rreg : State → Reg → ℕ)
  (memory : State → (ℕ → Maybe ℕ))
  (xhalted : State → Bool)
  where

open RegRoles roles using (reg-of; sp-reg; clos-reg; heap-reg; out-reg; in1-reg; scratch-reg; count-reg)

-- Both of these are `n * slot-size` at every target — the emitted displacement
-- of a slot and the byte size of a reservation. Defining them from the
-- `slot-size` parameter is what removes the last import of an x86 module.
slots : ℕ → ℕ
slots n = n * slot-size

slot-to-disp : ℕ → ℕ
slot-to-disp n = n * slot-size

-- …and the positivity that goes with it, in the form the arithmetic wants.
-- `s≤s z≤n` sufficed while `slot-size` was the literal 8.
nz⇒pos : ∀ n → ⦃ NonZero n ⦄ → 0 < n
nz⇒pos (suc _) = s≤s z≤n

slot-size>0 : 0 < slot-size
slot-size>0 = nz⇒pos slot-size

open import Data.Nat using (zero; suc; _+_; _∸_; _*_; _≡ᵇ_; _≟_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-comm; +-assoc; +-cancelˡ-≡; *-cancelʳ-≡; n∸n≡0
                                      ; m≤m+n; <-irrefl; <-trans; <-transʳ; <-transˡ
                                      ; +-monoʳ-<; *-monoˡ-<; ≤-refl; ≤-trans; m<n⇒m<1+n
                                      ; m+n≤o⇒m≤o∸n; <⇒≢; m∸n+n≡m; ≤-reflexive; m<m+n
                                      ; +-monoʳ-≤; s≤s; z≤n; +-identityʳ; m∸n≤m; *-identityˡ
                                      ; <⇒≤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; Dec; ¬_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

open import Once.Memory.HeapAddress
  using (HeapRef; sucHL; heap-loc; mkHeapRef; heap-ref; heap-offset; ref-id; _≟HL_)

-- Plan 0.65 G1c step 4: ONE accessor per observable, so the correspondence
-- reads the machine through a surface a core can take as parameters. `memory`
-- and `xhalted` are already projections; this is the register one.

-- …and the three that need no parameter at all, because they are already
-- generic: on every target a word IS a ℕ, a memory IS a partial map from
-- addresses to words, and reading one IS applying it. Naming them here is what
-- lets the core stop mentioning `X` for memory entirely.
Word : Set
Word = ℕ

Memory : Set
Memory = ℕ → Maybe Word

readMem : Memory → ℕ → Maybe Word
readMem m a = m a

-- …and writing one, the same way: `X.writeMem`'s own definition, which names
-- no register file and no state. Making it local is what lets the store
-- helpers and `read-write-{hit,miss}` cross into the core; what genuinely
-- cannot cross is `writeReg`, a record update on THIS arch's register file.
writeMem : Memory → ℕ → Word → Memory
writeMem m addr val = λ a → if a ≡ᵇ addr then just val else m a
open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeLocToStack; writeHeapMem
                       ; readLoc; writeLoc-read-same-stack; writeLoc-preserves-other)
open ExecFinal {FS} using (exec-load-via-resolved; exec-load-suc-via-resolved; exec-load-with-value
                          ; exec-store-via-resolved; exec-store-suc-via-resolved)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open FrameSemantics FS using (shift-frame)

open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below)
open AbstractExec {FS} using (exec-abstract; lit-value; exec-load-from-slot-with-value; exec-restore-input-with-value)
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
-- ⟦ Int ⟧ = Carrier = ℕ = Word; the explicit Carrier→Word target forces the
-- parameterised-module projection `⟦ Int ⟧` to reduce (it stays stuck when the
-- return type is bare `ℕ`). This is the `mov rax, imm v` immediate value.
lit-word : Carrier → Word
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

enc-sv-at : AddrMap → StoredValue FS → Word
enc-sv-at am (SV-Tag n)                = n
enc-sv-at am (SV-Ptr (AtDynamic hl))   = hmap am hl
-- Plan 0.61: a stack pointer is the SLOT'S ADDRESS. This is only meaningful
-- because frames now move with %rsp (`Machine.Flat`) — with the old model the
-- callee's slot k and its caller's slot k were the same abstract cell, so no
-- address could be assigned and this was a (false) `0`.
enc-sv-at am (SV-Ptr (AtStack f k))    = slot-addr f k
-- A register-fittable literal encodes to ITS OWN VALUE, at both numeric types.
-- That is exactly the immediate the emitter loads, so load-const's out-eq is
-- `refl` and literal values flow through FlatCorr instead of collapsing to 0.
--
-- D113 is what made the float case identical to the int one. A `StoredValue`
-- now holds the target's REPRESENTATION at both types — the machine encodes at
-- `instr-load-const`, the one instruction that materialises a literal — so
-- there is nothing left for `enc-sv` to convert. The per-arch `fenc : Dyadic →
-- ℕ` parameter this module used to take is gone with it: `FS` already carries
-- the target's format, so a second channel for the same fact was redundant.
-- ENUMERATED (no catch-all): a `SV-Lit _ _` catch-all does not survive the
-- case-tree translation, so `enc-sv-at am (SV-Lit fits-float v)` would not reduce
-- and the extension-stability lemma below could not be stated by `refl`.
enc-sv-at am (SV-Lit fits-int v)       = lit-word v
enc-sv-at am (SV-Lit fits-float v)     = lit-word v
-- Plan 0.63 (D089): `SV-Code` now carries the label's IDENTITY, so its
-- encoding is `idx` — numerically exactly what this yielded before, when the
-- payload was the bare counter. The same FICTION `effectiveAddr (rip+label _)`
-- records (a label number is not an instruction index): D081's open question,
-- owned by `events-running-call`. D089 neither fixes nor worsens it.
enc-sv-at am (SV-Code n)               = cmap am n

enc-maybe-at : AddrMap → Maybe (StoredValue FS) → Maybe Word
enc-maybe-at am (just v) = just (enc-sv-at am v)
enc-maybe-at am nothing  = nothing

-- The view-level names every proof uses: one clause each, so they UNFOLD during
-- conversion checking and the comparison lands on the address map.
-- the view's two maps, bundled — this is what every `*-at` takes
amap : HeapView → AddrMap
amap hv = mkAddrMap (haddr hv) (caddr hv)

enc-sv : HeapView → StoredValue FS → Word
enc-sv hv = enc-sv-at (amap hv)

enc-maybe : HeapView → Maybe (StoredValue FS) → Maybe Word
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
Window : AddrMap → Memory → StackMem FS → Frame → ℕ → Set
Window am mem stk f b = ∀ (k : Slot) → k < b → ∀ (v : StoredValue FS) → stk f k ≡ just v →
  readMem mem (frame-base f + slot-to-disp k) ≡ just (enc-sv-at am v)

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
StackWindows : AddrMap → Memory → StackMem FS → ℕ → List (Frame × ℕ) → Set
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

-- THE HEAD ROW IS PER-ARCH (plan 0.65 G2, 2026-08-16). Between a call and the
-- callee's body marker the head pending return has not been SPILLED yet, and
-- where it lives until then is an ABI fact: in memory on x86-64 (`call` pushed
-- it), in the link register on RISC-V (`jalr` wrote `ra` and touched nothing
-- else). `FlatState.flink` marks that one-instruction window — `just r` means
-- "unspilled" — and `LK` is what the arch claims in it.
--
--   x86-64   λ a v → readMem (memory s) a ≡ just v   -- ≡ the `nothing` row
--   riscv64  λ a v → rreg s ra ≡ v                   -- the address is ignored
--
-- The recursion passes `nothing`: only the HEAD can be unspilled, because the
-- call jumps straight to a body marker and that marker spills. Converting the
-- `just` row into the `nothing` row IS each arch's spill obligation, which is
-- why this parameter and not a 42-times-owed `CompiledCorr` field (the dead
-- route, kept in the plan file).
RetAddrs : (ℕ → ℕ) → Memory → (ℕ → ℕ → Set) → Maybe ℕ
         → List (Frame × ℕ) → List ℕ → Set
RetAddrs xoff mem LK lk       fr             []       = ⊤
RetAddrs xoff mem LK lk       []             (r ∷ rs) = ⊥
RetAddrs xoff mem LK (just _) ((f , b) ∷ fr) (r ∷ rs) =
  LK (frame-base f + slots b) (xoff r)
  × GapNext (frame-base f + slots b) fr
  × RetAddrs xoff mem LK nothing fr rs
RetAddrs xoff mem LK nothing  ((f , b) ∷ fr) (r ∷ rs) =
  (readMem mem (frame-base f + slots b) ≡ just (xoff r))
  × GapNext (frame-base f + slots b) fr
  × RetAddrs xoff mem LK nothing fr rs

-- THE SPILL, AND ITS INVERSE (plan 0.65 G2, 2026-08-16). Converting the head
-- row is the whole content of the call window, and it is exactly two lemmas:
--
--   ret-unlink  `just` → `nothing`: what the BODY MARKER does. The arch owes
--               "wherever my link claim says the return address is, the stack
--               cell now holds it" — the identity on x86-64 (`call` pushed it),
--               the `sd ra` on riscv64.
--   ret-relink  `nothing` → `just`: what the CALL does. The arch owes the
--               converse at the cell it just wrote.
--
-- Only the head row moves; everything below is already `nothing`.
-- STATED AT THE HEAD CELL, not `∀ a`. A claim may IGNORE its address argument
-- (riscv64's reads `ra` and looks at nothing else), and then the `∀ a` form is
-- simply false — it would say the link register's value sits at EVERY address.
-- The head is the only place either lemma applies, so the head is where the
-- premise belongs.
ret-unlink : ∀ (xoff : ℕ → ℕ) (mem : Memory) (LK : ℕ → ℕ → Set) (lk : Maybe ℕ)
               (f : Frame) (b : ℕ) (fr : List (Frame × ℕ)) (rs : List ℕ)
           → (∀ (v : ℕ) → LK (frame-base f + slots b) v
                        → readMem mem (frame-base f + slots b) ≡ just v)
           → RetAddrs xoff mem LK lk ((f , b) ∷ fr) rs
           → RetAddrs xoff mem LK nothing ((f , b) ∷ fr) rs
ret-unlink xoff mem LK lk       f b fr []       sp r           = tt
ret-unlink xoff mem LK (just _) f b fr (r ∷ rs) sp (h , g , t) =
  sp (xoff r) h , g , t
ret-unlink xoff mem LK nothing  f b fr (r ∷ rs) sp (h , g , t) =
  h , g , t

ret-relink : ∀ (xoff : ℕ → ℕ) (mem : Memory) (LK : ℕ → ℕ → Set) (lk : Maybe ℕ)
               (f : Frame) (b : ℕ) (fr : List (Frame × ℕ)) (rs : List ℕ)
           → (∀ (v : ℕ) → readMem mem (frame-base f + slots b) ≡ just v
                        → LK (frame-base f + slots b) v)
           → RetAddrs xoff mem LK nothing ((f , b) ∷ fr) rs
           → RetAddrs xoff mem LK lk ((f , b) ∷ fr) rs
ret-relink xoff mem LK lk       f b fr []       sp r           = tt
ret-relink xoff mem LK (just _) f b fr (r ∷ rs) sp (h , g , t) =
  sp (xoff r) h , g , t
ret-relink xoff mem LK nothing  f b fr (r ∷ rs) sp (h , g , t) =
  h , g , t

-- …and RE-STATING THE HEAD ROW AT A NEW CLAIM, which is what an arch whose
-- claim reads a REGISTER owes at every step that writes one. x86-64 never calls
-- it (its claim is about memory, and a register write leaves memory alone);
-- riscv64 calls it wherever `ra` is provably untouched.
ret-relk : ∀ (xoff : ℕ → ℕ) (mem : Memory) (LK LK' : ℕ → ℕ → Set) (lk : Maybe ℕ)
             (fr : List (Frame × ℕ)) (rs : List ℕ)
         → (∀ (a v : ℕ) → LK a v → LK' a v)
         → RetAddrs xoff mem LK lk fr rs
         → RetAddrs xoff mem LK' lk fr rs
ret-relk xoff mem LK LK' lk       fr             []       tr r           = tt
ret-relk xoff mem LK LK' lk       []             (r ∷ rs) tr ()
ret-relk xoff mem LK LK' (just _) ((f , b) ∷ fr) (r ∷ rs) tr (h , g , t) =
  tr (frame-base f + slots b) (xoff r) h , g
  , ret-relk xoff mem LK LK' nothing fr rs tr t
ret-relk xoff mem LK LK' nothing  ((f , b) ∷ fr) (r ∷ rs) tr (h , g , t) =
  h , g , ret-relk xoff mem LK LK' nothing fr rs tr t

-- RE-ANCHORING THE HEAD (D093). The pending return at the head of `fret` is
-- addressed by the CURRENT frame's window END, and a body entry MOVES that
-- frame — down by its reservation, while setting the reservation to it. The
-- end therefore lands on the same cell (that is D086's whole point: the call's
-- slot sits just above the body's frame), and this is the transport that says
-- so. Everything below the head is untouched.
ret-head : ∀ (xoff : ℕ → ℕ) (mem : Memory) (LK : ℕ → ℕ → Set) (lk : Maybe ℕ)
             (f f' : Frame) (b b' : ℕ)
             (fr : List (Frame × ℕ)) (rs : List ℕ)
         → frame-base f' + slots b' ≡ frame-base f + slots b
         → RetAddrs xoff mem LK lk ((f , b) ∷ fr) rs
         → RetAddrs xoff mem LK lk ((f' , b') ∷ fr) rs
ret-head xoff mem LK lk       f f' b b' fr []       eq r           = tt
ret-head xoff mem LK (just _) f f' b b' fr (r ∷ rs) eq (h , g , t) =
  subst (λ a → LK a (xoff r)) (sym eq) h
  , subst (λ e → GapNext e fr) (sym eq) g
  , t
ret-head xoff mem LK nothing  f f' b b' fr (r ∷ rs) eq (h , g , t) =
  subst (λ a → readMem mem a ≡ just (xoff r)) (sym eq) h
  , subst (λ e → GapNext e fr) (sym eq) g
  , t

------------------------------------------------------------------------
-- The correspondence: a FlatState and an x86 State agree on the four
-- abstract registers (under enc-sv), the pc, the zero-flag, the halt
-- flag, the heap memory (under enc-hl + enc-sv), and the LIVE STACK
-- (every frame, base-relative, under enc-sv).
--
-- `stack-eq`: see `StackWindows` above. The current frame's window is its
-- HEAD, recovered in the old `%rsp`-addressed form through `sp-eq` by the
-- derived `stack-eq-cur` — which is what every straight-line consumer
-- (load/store-at-slot, restore-input, worklist-*) actually uses.
------------------------------------------------------------------------
record FlatCorr (hv : HeapView) (fs : FlatState) (s : State) : Set where
  field
    in1-eq  : rreg s in1-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input1)
    out-eq  : rreg s out-reg ≡ enc-sv hv (readReg (regs (floc fs)) Output)
    scratch-eq  : rreg s scratch-reg ≡ enc-sv hv (readReg (regs (floc fs)) Scratch)
    -- THE TALLY (plan 0.54 D item 4): `%r14` IS the `Count` register. Without
    -- this field the correspondence would say NOTHING about the counter, and the
    -- choice of physical register in `compile-abstract` would not be checked by
    -- anything — the tally lowering could name any register and still typecheck.
    -- With it, every block step must re-establish it, so a wrong register in the
    -- codegen is a TYPE ERROR here.
    count-eq  : rreg s count-reg ≡ enc-sv hv (readReg (regs (floc fs)) Count)
    -- THE CLOSURE REGISTER (D097). `%r12` mirrors the flat `fclosure`, which is
    -- where the abstract machine keeps the closure pointer (`exec-abstract`
    -- treats `instr-save-closure-reg` as the identity precisely because that
    -- register lives at the FLAT level). Untracked until now, because nothing
    -- READ it — the call does: `call *0x8(%r12)` dereferences it, so without
    -- this field the concrete call's target is unrelated to anything abstract.
    clos-eq  : rreg s clos-reg ≡ enc-sv hv (fclosure fs)
    halt-eq : xhalted s ≡ halted (floc fs)
    -- THE STACK ANCHOR (plan 0.61): `%rsp` IS the current frame's base. Frames
    -- move with the stack pointer, so this holds at every step — and it is what
    -- gives a stack POINTER its address (`enc-sv (SV-Ptr (AtStack f k))`).
    sp-eq  : rreg s sp-reg ≡ frame-base (current-frame (falloc fs))
    -- THE FRONTIER: `%r15` (the bump allocator's heap top) IS the view's frontier.
    -- This is what makes the next `instr-alloc-heap` provable: the fresh block's
    -- address is read off the concrete machine, not predicted from the abstract state.
    frontier-eq  : rreg s heap-reg ≡ hfront hv
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
              readMem (memory s) (haddr hv hl) ≡ enc-maybe hv (heapMem (floc fs) hl)
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
    lo-le : lo hv ≤ rreg s sp-reg
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
              → readMem (memory s) a ≡ nothing
    -- EVERY LIVE FRAME (Plan 0.63, D085) — see `StackWindows`. The bound per
    -- frame is its OWN reservation (`frame-slots` for the current one, the
    -- remembered count for each saved caller): an unbounded ∀ k would be
    -- unsatisfiable (it would claim the cells beyond the outermost frame,
    -- which the loader owns, are the abstract `nothing`).
    stack-eq : StackWindows (amap hv) (memory s) (stackMem (floc fs))
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
record SetsRole (s s' : State) (ρ : Role) (v : Word) : Set where
  field
    at-role    : rreg s' (reg-of ρ) ≡ v
    off-role   : ∀ ρ' → ¬ (ρ' ≡ ρ)
               → rreg s' (reg-of ρ') ≡ rreg s (reg-of ρ')
    keeps-mem  : memory s' ≡ memory s
    keeps-halt : xhalted s' ≡ xhalted s
open SetsRole public

------------------------------------------------------------------------
-- Transporting the fields a role write does not touch. One helper per
-- `FlatCorr` field, so a `sim-*` record literal stays as short as it was when
-- the post-state was concrete — `in1-eq corr` becomes `keep-in1 corr st (λ ())`
-- and the `(λ ())` IS the distinctness the concrete `writeReg` used to supply
-- by reduction.
--
-- `dom-fresh` / `dom-written` / `dom-sized` need no helper: read their
-- signatures and they never mention the machine state at all.
------------------------------------------------------------------------
module _ {hv : HeapView} {fs : FlatState} {s s' : State} {ρ : Role} {v : Word}
         (corr : FlatCorr hv fs s) (st : SetsRole s s' ρ v) where

  keep-in1 : ¬ (role-in1 ≡ ρ)
           → rreg s' in1-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input1)
  keep-in1 ne = trans (off-role st role-in1 ne) (in1-eq corr)


  keep-out : ¬ (role-out ≡ ρ)
           → rreg s' out-reg ≡ enc-sv hv (readReg (regs (floc fs)) Output)
  keep-out ne = trans (off-role st role-out ne) (out-eq corr)

  keep-scratch : ¬ (role-scratch ≡ ρ)
               → rreg s' scratch-reg ≡ enc-sv hv (readReg (regs (floc fs)) Scratch)
  keep-scratch ne = trans (off-role st role-scratch ne) (scratch-eq corr)

  keep-count : ¬ (role-count ≡ ρ)
             → rreg s' count-reg ≡ enc-sv hv (readReg (regs (floc fs)) Count)
  keep-count ne = trans (off-role st role-count ne) (count-eq corr)

  keep-clos : ¬ (role-clos ≡ ρ) → rreg s' clos-reg ≡ enc-sv hv (fclosure fs)
  keep-clos ne = trans (off-role st role-clos ne) (clos-eq corr)

  keep-sp : ¬ (role-sp ≡ ρ)
          → rreg s' sp-reg ≡ frame-base (current-frame (falloc fs))
  keep-sp ne = trans (off-role st role-sp ne) (sp-eq corr)

  keep-heap-reg : ¬ (role-heap ≡ ρ) → rreg s' heap-reg ≡ hfront hv
  keep-heap-reg ne = trans (off-role st role-heap ne) (frontier-eq corr)

  keep-halt : xhalted s' ≡ halted (floc fs)
  keep-halt = trans (keeps-halt st) (halt-eq corr)

  keep-heap : ∀ (hl : HeapLocation) → HDom hv hl
            → readMem (memory s') (haddr hv hl) ≡ enc-maybe hv (heapMem (floc fs) hl)
  keep-heap hl d = trans (cong (λ m → readMem m (haddr hv hl)) (keeps-mem st)) (heap-eq corr hl d)

  keep-lo-le : ¬ (role-sp ≡ ρ) → lo hv ≤ rreg s' sp-reg
  keep-lo-le ne = subst (lo hv ≤_) (sym (off-role st role-sp ne)) (lo-le corr)

  keep-untouched : ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
                 → readMem (memory s') a ≡ nothing
  keep-untouched a f<a a<lo =
    trans (cong (λ m → readMem m a) (keeps-mem st)) (untouched corr a f<a a<lo)

  keep-stack : StackWindows (amap hv) (memory s') (stackMem (floc fs))
                            (lo hv) (frames-of (falloc fs))
  keep-stack = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs)) (lo hv) (frames-of (falloc fs)))
                     (sym (keeps-mem st)) (stack-eq corr)

------------------------------------------------------------------------
-- …and the same for a MEMORY write. `SetsRole`'s mirror: one cell changes,
-- every register and the halt flag do not. `off-addr` is what the concrete
-- `writeMem`'s address `≡ᵇ` test used to give by reduction, and stating it
-- makes the alias reasoning read better rather than worse — the store lemmas
-- below case-split on `hl ≟HL hl'` and then USE the law, where they used to
-- `rewrite ≡ᵇ-refl` / `≢→≡ᵇfalse` through the memory model.
--
-- Note there is no `keeps-regs ρ → ρ ≢ …` premise: a store touches no
-- register at all, so all eight roles are preserved unconditionally.
------------------------------------------------------------------------
record SetsMem (s s' : State) (a : ℕ) (v : Word) : Set where
  field
    at-addr  : readMem (memory s') a ≡ just v
    off-addr : ∀ a' → ¬ (a' ≡ a)
             → readMem (memory s') a' ≡ readMem (memory s) a'
    mem-regs : ∀ ρ → rreg s' (reg-of ρ) ≡ rreg s (reg-of ρ)
    mem-halt : xhalted s' ≡ xhalted s
open SetsMem public

module _ {hv : HeapView} {fs : FlatState} {s s' : State} {wa : ℕ} {wv : Word}
         (corr : FlatCorr hv fs s) (sm : SetsMem s s' wa wv) where

  mkeep-in1 : rreg s' in1-reg ≡ enc-sv hv (readReg (regs (floc fs)) Input1)
  mkeep-in1 = trans (mem-regs sm role-in1) (in1-eq corr)


  mkeep-out : rreg s' out-reg ≡ enc-sv hv (readReg (regs (floc fs)) Output)
  mkeep-out = trans (mem-regs sm role-out) (out-eq corr)

  mkeep-scratch : rreg s' scratch-reg ≡ enc-sv hv (readReg (regs (floc fs)) Scratch)
  mkeep-scratch = trans (mem-regs sm role-scratch) (scratch-eq corr)

  mkeep-count : rreg s' count-reg ≡ enc-sv hv (readReg (regs (floc fs)) Count)
  mkeep-count = trans (mem-regs sm role-count) (count-eq corr)

  mkeep-clos : rreg s' clos-reg ≡ enc-sv hv (fclosure fs)
  mkeep-clos = trans (mem-regs sm role-clos) (clos-eq corr)

  mkeep-sp : rreg s' sp-reg ≡ frame-base (current-frame (falloc fs))
  mkeep-sp = trans (mem-regs sm role-sp) (sp-eq corr)

  mkeep-heap-reg : rreg s' heap-reg ≡ hfront hv
  mkeep-heap-reg = trans (mem-regs sm role-heap) (frontier-eq corr)

  mkeep-halt : xhalted s' ≡ halted (floc fs)
  mkeep-halt = trans (mem-halt sm) (halt-eq corr)

  mkeep-lo-le : lo hv ≤ rreg s' sp-reg
  mkeep-lo-le = subst (lo hv ≤_) (sym (mem-regs sm role-sp)) (lo-le corr)

------------------------------------------------------------------------
-- THE TWO COMBINED SHAPES, and they exist because the ISA does — not because
-- the interface wanted generality. `call` lowers `%rsp` AND stores the return
-- address in the slot it just freed; `alloc-heap`'s two-instruction block
-- writes Output and the frontier. Neither decomposes into two `SetsRole`s,
-- because the INTERMEDIATE state is not something either lemma is given.
--
-- (A single record indexed by "which roles and which address were written"
-- would subsume all four. Worth doing when the module moves into `FlatCore`;
-- not worth doing speculatively here, where four concrete shapes cover 33
-- lemmas and each says exactly what its instruction does.)
------------------------------------------------------------------------
record SetsRoleMem (s s' : State) (ρ : Role) (v : Word) (a : ℕ) (mv : Word) : Set where
  field
    rm-at-role  : rreg s' (reg-of ρ) ≡ v
    rm-off-role : ∀ ρ' → ¬ (ρ' ≡ ρ)
                → rreg s' (reg-of ρ') ≡ rreg s (reg-of ρ')
    rm-at-addr  : readMem (memory s') a ≡ just mv
    rm-off-addr : ∀ a' → ¬ (a' ≡ a)
                → readMem (memory s') a' ≡ readMem (memory s) a'
    rm-halt     : xhalted s' ≡ xhalted s
open SetsRoleMem public

record Sets2Roles (s s' : State) (ρ₁ ρ₂ : Role) (v₁ v₂ : Word) : Set where
  field
    at-role₁  : rreg s' (reg-of ρ₁) ≡ v₁
    at-role₂  : rreg s' (reg-of ρ₂) ≡ v₂
    off-roles : ∀ ρ → ¬ (ρ ≡ ρ₁) → ¬ (ρ ≡ ρ₂)
              → rreg s' (reg-of ρ) ≡ rreg s (reg-of ρ)
    keeps-mem₂  : memory s' ≡ memory s
    keeps-halt₂ : xhalted s' ≡ xhalted s
open Sets2Roles public

------------------------------------------------------------------------
-- The window a straight-line instruction addresses: the CURRENT frame's,
-- in the `%rsp`-relative form the emitted code uses. This is the head of
-- the frame list, re-anchored through `sp-eq` — i.e. exactly the field
-- `stack-eq` used to BE, now derived.
------------------------------------------------------------------------
-- (`stk`/`f`/`b` are EXPLICIT: `Window` unfolds during conversion, and then
-- `stk f k` with a non-variable `f` is not a Miller pattern — an implicit
-- would just block.)
win-at : ∀ (am : AddrMap) (mem : Memory) (stk : StackMem FS) (f : Frame) (b : ℕ) (base : ℕ)
       → base ≡ frame-base f
       → (∀ (k : Slot) → k < b → ∀ (v : StoredValue FS) → stk f k ≡ just v
            → readMem mem (base + slot-to-disp k) ≡ just (enc-sv-at am v))
       → Window am mem stk f b
win-at am mem stk f b base eq w k k<b v ev rewrite sym eq = w k k<b v ev

win-off : ∀ (am : AddrMap) (mem : Memory) (stk : StackMem FS) (f : Frame) (b : ℕ) (base : ℕ)
        → base ≡ frame-base f → Window am mem stk f b
        → ∀ (k : Slot) → k < b → ∀ (v : StoredValue FS) → stk f k ≡ just v
        → readMem mem (base + slot-to-disp k) ≡ just (enc-sv-at am v)
win-off am mem stk f b base eq w k k<b v ev rewrite eq = w k k<b v ev

-- The current frame's window, as a `Window` (the head of the list).
stack-eq-win : ∀ {hv : HeapView} {fs : FlatState} {s : State} → FlatCorr hv fs s
             → Window (amap hv) (memory s) (stackMem (floc fs))
                      (current-frame (falloc fs)) (frame-slots (falloc fs))
stack-eq-win corr = proj₁ (proj₂ (stack-eq corr))

stack-eq-cur : ∀ {hv : HeapView} {fs : FlatState} {s : State} → FlatCorr hv fs s
             → ∀ (k : Slot) → k < frame-slots (falloc fs)
             → ∀ (v : StoredValue FS)
             → stackMem (floc fs) (current-frame (falloc fs)) k ≡ just v
             → readMem (memory s) (rreg s sp-reg + slot-to-disp k)
               ≡ just (enc-sv hv v)
stack-eq-cur {hv} {fs} {s} corr =
  win-off (amap hv) (memory s) (stackMem (floc fs))
          (current-frame (falloc fs)) (frame-slots (falloc fs))
          (rreg s sp-reg) (sp-eq corr) (stack-eq-win corr)

-- THE LAYOUT SEPARATION, derived: the heap frontier is at or below `%rsp`,
-- through the high-water mark (`front-lo` then `lo-le`). Every heap/stack
-- disjointness consumer uses THIS — the field it replaces had the same type.
sep : ∀ {hv : HeapView} {fs : FlatState} {s : State}
    → FlatCorr hv fs s → hfront hv ≤ rreg s sp-reg
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
untouched-descend : ∀ {hv : HeapView} {fs : FlatState} {s : State}
                      (lo' : ℕ) (le : lo' ≤ lo hv) (fl : hfront hv ≤ lo')
                    (corr : FlatCorr hv fs s)
                  → ∀ (a : ℕ) → hfront hv ≤ a → a < lo'
                  → readMem (memory s) a ≡ nothing
untouched-descend lo' le fl corr a fa a<lo' = untouched corr a fa (<-transˡ a<lo' le)

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
-- out-eq is exactly the old in1-eq.
------------------------------------------------------------------------
sim-mov-to-output : {hv : HeapView} (fs : FlatState) (s s' : State)
  → FlatCorr hv fs s
  → SetsRole s s' role-out (rreg s in1-reg)
  → FlatCorr hv (flat-exec-instr mov-to-output [] fs) s'
sim-mov-to-output {hv} fs s s' corr st = record
  { in1-eq  = keep-in1 corr st (λ ())
  ; out-eq  = trans (at-role st) (in1-eq corr)
  ; scratch-eq  = keep-scratch corr st (λ ())
  ; count-eq  = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = keep-heap corr st
  ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st
  }

-- mov-to-input (Input1 := Output) ↔ `mov rdi, rax`.
sim-mov-to-input : {hv : HeapView} (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-in1 (rreg s out-reg)
  → FlatCorr hv (flat-exec-instr mov-to-input [] fs) s'
sim-mov-to-input {hv} fs s s' corr st = record
  { in1-eq = trans (at-role st) (out-eq corr) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-load-tag-lit n (Output := SV-Tag n) ↔ `mov rax, n`. enc(SV-Tag n)=n, so
-- the new field IS `at-role` with no transport at all.
sim-load-tag-lit : {hv : HeapView} (n : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-out n
  → FlatCorr hv (flat-exec-instr (instr-load-tag-lit n) [] fs) s'
sim-load-tag-lit {hv} n fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op scratch-one (Scratch := SV-Tag 1) ↔ `mov rbx, 1`.
sim-reg-scratch-one : {hv : HeapView} (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-scratch 1
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-one) [] fs) s'
sim-reg-scratch-one {hv} fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = at-role st ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op scratch-zero (Scratch := SV-Tag 0) ↔ `mov rbx, 0`.
sim-reg-scratch-zero : {hv : HeapView} (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-scratch 0
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-zero) [] fs) s'
sim-reg-scratch-zero {hv} fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = at-role st ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op count-zero (Count := SV-Tag 0) ↔ `mov r14, 0`.
-- Plan 0.54 D item 4: the tally has its OWN register — zeroing the counter
-- disturbs nothing else. With roles that reads directly: the written role is
-- `role-count`, and every other role is one of the `off-role` covers.
sim-reg-count-zero : {hv : HeapView} (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-count 0
  → FlatCorr hv (flat-exec-instr (instr-reg-op count-zero) [] fs) s'
sim-reg-count-zero {hv} fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = at-role st
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- instr-reg-op scratch-load-count (Scratch := Count) ↔ `mov rbx, r14`.
sim-reg-scratch-load-count : {hv : HeapView} (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-scratch (rreg s count-reg)
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-load-count) [] fs) s'
sim-reg-scratch-load-count {hv} fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = trans (at-role st) (count-eq corr) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

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
sim-load-indirect-suc : {hv : HeapView} (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) (sucHL hl) ≡ just w
  → SetsRole s s' role-out (enc-sv hv w)
  → FlatCorr hv (flat-exec-instr load-indirect-suc [] fs) s'
sim-load-indirect-suc {hv} hl w fs s s' corr i-eq h-eq st =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
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
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
      ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

------------------------------------------------------------------------
-- Heap load (no offset): load-indirect (Output := *Input1) ↔
-- `mov rax, [rdi]`. Sibling of load-indirect-suc; reads the cell Input1
-- points to directly. Same reduce-then-correspond structure.
------------------------------------------------------------------------
sim-load-indirect : {hv : HeapView} (hl : HeapLocation) (w : StoredValue FS) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → heapMem (floc fs) hl ≡ just w
  → SetsRole s s' role-out (enc-sv hv w)
  → FlatCorr hv (flat-exec-instr load-indirect [] fs) s'
sim-load-indirect {hv} hl w fs s s' corr i-eq h-eq st =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-load-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) h-eq)
    reduces : flat-exec-instr load-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
      ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

------------------------------------------------------------------------
-- STACK LOAD: `load-from-slot slot` (Output := stack[current-frame, slot]) ↔
-- `mov rax, [rsp + slot-to-disp slot]`. The read VALUE comes from `stack-eq`
-- (memory s at rsp+disp = enc-maybe hv of the slot's abstract value); the x86 post
-- is identical in shape to `sim-load-indirect` (rax := enc-sv hv w). Only the
-- SUCCESS case (slot holds `just w`) — the empty-slot (`nothing`→halt) case is
-- routed as a WF residual, exactly like load-indirect's bad case. This is the
-- FIRST consumer of the new `stack-eq` field (via block-step-load-from-slot).
------------------------------------------------------------------------
sim-load-from-slot : {hv : HeapView} (slot : Slot) (w : StoredValue FS) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → SetsRole s s' role-out (enc-sv hv w)
  → FlatCorr hv (flat-exec-instr (load-from-slot slot) [] fs) s'
sim-load-from-slot {hv} slot w fs s s' corr st-eq st =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    ex-eq : exec-abstract (load-from-slot slot) (floc fs) (falloc fs)
            ≡ (record (floc fs) { regs = writeReg (regs (floc fs)) Output w } , falloc fs)
    ex-eq = cong (λ mv → exec-load-from-slot-with-value mv (floc fs) (falloc fs)) st-eq
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    reduces : flat-exec-instr (load-from-slot slot) [] fs ≡ cleanFlat
    reduces = cong (λ p → record fs { floc = proj₁ p ; falloc = proj₂ p ; fpc = suc (fpc fs) }) ex-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
      ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

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
untouched-write : ∀ {s s' : State} (waddr : ℕ) (v' : Word) (a : ℕ)
                → SetsMem s s' waddr v' → (a ≡ waddr → ⊥)
                → readMem (memory s) a ≡ nothing
                → readMem (memory s') a ≡ nothing
untouched-write waddr v' a sm ≢w pre = trans (off-addr sm a ≢w) pre

-- A HEAP store misses the virgin region: its target is a mapped cell, hence
-- strictly below the frontier, hence below every address the region contains.
untouched-heap-store : ∀ {hv : HeapView} {fs : FlatState} {s s' : State}
                         (hl : HeapLocation) (v' : Word) → HDom hv hl → FlatCorr hv fs s
                     → SetsMem s s' (haddr hv hl) v'
                     → ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
                     → readMem (memory s') a ≡ nothing
untouched-heap-store {hv} {fs} {s} hl v' d corr sm a fa a<lo =
  untouched-write (haddr hv hl) v' a sm
    (λ eq → <-irrefl refl (<-transˡ (subst (_< hfront hv) (sym eq) (dom-below hv d)) fa))
    (untouched corr a fa a<lo)

-- A STACK store misses it from the other side: its target is at or above `lo`
-- (`%rsp + 8k ≥ %rsp ≥ lo`), and the region stops strictly below `lo`.
untouched-stack-store : ∀ {hv : HeapView} {fs : FlatState} {s s' : State}
                          (waddr : ℕ) (v' : Word) → lo hv ≤ waddr → FlatCorr hv fs s
                      → SetsMem s s' waddr v'
                      → ∀ (a : ℕ) → hfront hv ≤ a → a < lo hv
                      → readMem (memory s') a ≡ nothing
untouched-stack-store {hv} {fs} {s} waddr v' lo≤w corr sm a fa a<lo =
  untouched-write waddr v' a sm (<⇒≢ (<-transˡ a<lo lo≤w)) (untouched corr a fa a<lo)

-- The store correspondence: writing `v` at heap cell `hl` (x86: haddr hv hl)
-- preserves the heap agreement at every other cell, and installs enc-sv v
-- at `hl`. Case-split on ≟HL; enc-hl-inj turns cell-distinctness into
-- address-distinctness so the x86 `≡ᵇ` test resolves the same way.
-- store-heap-eq now works over LIVE cells only: the write target `hl` is live,
-- and the correspondence + result quantify over live `hl'`. Distinctness for the
-- no-alias case is `enc-hl-inj-live` (the allocator's `blocks-disjoint` on live
-- blocks) — dead cells are never compared.
store-heap-eq : ∀ (hv : HeapView) (hl : HeapLocation) (v : StoredValue FS) (s s' : State) (ls : LocState FS)
  → SetsMem s s' (haddr hv hl) (enc-sv hv v)
  → HDom hv hl
  → (∀ hl' → HDom hv hl' → readMem (memory s) (haddr hv hl') ≡ enc-maybe hv (heapMem ls hl'))
  → ∀ hl' → HDom hv hl' → readMem (memory s') (haddr hv hl')
            ≡ enc-maybe hv (writeHeapMem (heapMem ls) hl v hl')
-- (writeHeapMem is with-free now, so the `with hl ≟HL hl'` below reduces
-- it directly — no read-after-write accessor lemmas needed.)
store-heap-eq hv hl v s s' ls sm live-hl pre hl' live-hl' with hl ≟HL hl'
... | yes refl = at-addr sm
... | no ¬p = trans (off-addr sm (haddr hv hl')
                      (λ q → ¬p (sym (haddr-inj hv live-hl' live-hl q))))
                    (pre hl' live-hl')

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
read-write-hit : ∀ (mem : Memory) (waddr : ℕ) (v' : Word)
               → readMem (writeMem mem waddr v') waddr ≡ just v'
read-write-hit mem waddr v' rewrite ≡ᵇ-refl waddr = refl

read-write-miss : ∀ (mem : Memory) (waddr : ℕ) (v' : Word) (a : ℕ) → (a ≡ waddr → ⊥)
                → readMem (writeMem mem waddr v') a ≡ readMem mem a
read-write-miss mem waddr v' a ne rewrite ≢→≡ᵇfalse {a} {waddr} ne = refl

-- THE FLOOR IS ONLY EVER READ AT THE HEAD, so replacing it there is the whole
-- of both frame moves: `enter-frame` conses (the tail's floor becomes the
-- caller's base), `leave-frame` drops the head (the floor drops back to `lo`).
windows-reanchor : ∀ {am : AddrMap} {mem : Memory} {stk : StackMem FS}
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
windows-lower : ∀ {am : AddrMap} {mem : Memory} {stk : StackMem FS}
                  (fl fl' : ℕ) (fr : List (Frame × ℕ))
              → fl' ≤ fl → StackWindows am mem stk fl fr → StackWindows am mem stk fl' fr
windows-lower fl fl' []             le w                = tt
windows-lower fl fl' ((f , b) ∷ fr) le (bd , win , rest) = ≤-trans le bd , win , rest

-- A STORE THAT ONLY FORGETS preserves every window. Direct consequence of
-- `Window` being one-directional: it constrains a cell only where the abstract
-- side holds a value, so removing values can never invalidate it. `c-thunk`'s
-- frame clear is the instance — the saved frames' windows ride across it
-- without any frame-distinctness argument.
windows-forget : ∀ {am : AddrMap} {mem : Memory} (stk stk' : StackMem FS)
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
windows-leave : ∀ {am : AddrMap} {mem : Memory} {stk : StackMem FS}
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
windows-above : ∀ {am : AddrMap} (mem mem' : Memory) (stk stk' : StackMem FS)
                  (fl : ℕ) (fr : List (Frame × ℕ))
              → (∀ (a : ℕ) → fl ≤ a → readMem mem' a ≡ readMem mem a)
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

-- A STORE AT THE GAP CELL PRESERVES EVERY WINDOW (plan 0.65 G2, 2026-08-16).
--
-- riscv64's body marker SPILLS — `sd ra, 8b(sp)` — and the cell it writes is
-- the current frame's window END: the slot D086 gave the CALL. The head's own
-- window stops one slot short of it, and the CALLER's base is one slot past it.
--
-- That last half is `GapNext` and nothing weaker. `StackWindows` threads its
-- floor as a `≤`, so from the windows alone the caller could start EXACTLY on
-- the cell being written, and the store would be clobbering its slot 0. So the
-- marker's store is legal precisely because the call reserved that cell — and
-- `RetAddrs`, not `StackWindows`, is where that is recorded. x86-64 never met
-- this: its marker writes no memory at all.
window-store-above : ∀ {am : AddrMap} (mem : Memory) (stk : StackMem FS)
                       (a : ℕ) (v : Word) (f : Frame) (b : ℕ)
                   → frame-base f + slots b ≤ a
                   → Window am mem stk f b
                   → Window am (writeMem mem a v) stk f b
window-store-above mem stk a v f b le win k k<b sv st =
  trans (read-write-miss mem a v (frame-base f + slot-to-disp k)
          (<⇒≢ (<-transˡ (+-monoʳ-< (frame-base f) (*-monoˡ-< slot-size k<b)) le)))
        (win k k<b sv st)

windows-store-gap : ∀ {am : AddrMap} (mem : Memory) (stk : StackMem FS) (v : Word)
                      (fl : ℕ) (f : Frame) (b : ℕ) (fr : List (Frame × ℕ))
                  → GapNext (frame-base f + slots b) fr
                  → StackWindows am mem stk fl ((f , b) ∷ fr)
                  → StackWindows am (writeMem mem (frame-base f + slots b) v) stk fl
                                  ((f , b) ∷ fr)
windows-store-gap mem stk v fl f b [] gn (bd , win , rest) =
  bd , window-store-above mem stk (frame-base f + slots b) v f b ≤-refl win , tt
windows-store-gap {am} mem stk v fl f b ((f₀ , b₀) ∷ fr) gn (bd , win , rest) =
  bd , window-store-above mem stk a v f b ≤-refl win
     , windows-lower (frame-base f₀) a ((f₀ , b₀) ∷ fr) a≤next
         (windows-above mem (writeMem mem a v) stk stk (frame-base f₀) ((f₀ , b₀) ∷ fr)
            (λ c le → read-write-miss mem a v c
                        (λ eq → <⇒≢ (<-transˡ a<next le) (sym eq)))
            (λ _ _ _ → refl)
            (windows-reanchor a (frame-base f₀) f₀ b₀ fr ≤-refl rest))
  where
    a : ℕ
    a = frame-base f + slots b
    -- the caller's base is ONE SLOT past the cell — `GapNext`, and this is the
    -- half `StackWindows` cannot supply
    a<next : a < frame-base f₀
    a<next = subst (a <_) gn (m<m+n a slot-size>0)
    a≤next : a ≤ frame-base f₀
    a≤next = <⇒≤ a<next

-- A write strictly BELOW the floor is invisible to every window: the heap
-- store's case, where the floor is `lo` and the target is a mapped cell.
windows-write-below : ∀ {am : AddrMap} {s s' : State} (stk : StackMem FS)
                        (waddr : ℕ) (v' : Word) (fl : ℕ) (fr : List (Frame × ℕ))
                    → SetsMem s s' waddr v'
                    → waddr < fl
                    → StackWindows am (memory s) stk fl fr
                    → StackWindows am (memory s') stk fl fr
windows-write-below {am} {s} {s'} stk waddr v' fl fr sm lt =
  windows-above {am} (memory s) (memory s') stk stk fl fr
    (λ a fl≤a → off-addr sm a (λ eq → <⇒≢ (<-transˡ lt fl≤a) (sym eq)))
    (λ _ _ _ → refl)

-- STACK preservation under a HEAP store, derived rather than assumed: the
-- written cell is mapped, so it is below the frontier (`dom-below`), which is
-- at or below the high-water mark (`front-lo`), which is the frame list's
-- floor. This is what retires the per-site `disj` premise the heap stores used
-- to take — the same argument as the old one-frame `sep`, now for EVERY frame.
windows-heap-store : ∀ {hv : HeapView} {fs : FlatState} {s s' : State}
                       (hl : HeapLocation) (v' : Word) → HDom hv hl
                   → (corr : FlatCorr hv fs s)
                   → SetsMem s s' (haddr hv hl) v'
                   → StackWindows (amap hv) (memory s')
                                  (stackMem (floc fs)) (lo hv) (frames-of (falloc fs))
windows-heap-store {hv} {fs} {s} hl v' d corr sm =
  windows-write-below (stackMem (floc fs)) (haddr hv hl) v'
    (lo hv) (frames-of (falloc fs)) sm (<-transˡ (dom-below hv d) (front-lo hv)) (stack-eq corr)

-- store-indirect: *Input1 := Output ↔ `mov [rdi], rax`. Hypotheses:
--   Input1 = SV-Ptr (AtDynamic hl)   (destination is a heap cell)
--   the value is heap-storable (writeLoc reduces to writeLocToHeap) — the
--   caller discharges this by `refl` for any non-stack-pointer value (all
--   cata-stored values: tags + heap pointers).
sim-store-indirect : {hv : HeapView} (hl : HeapLocation) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv hl        -- the store target is a live block (store-WF)
  → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
  -- (Plan 0.63, D085: the heap/stack disjointness premise is GONE — it is now
  -- `windows-heap-store`, a theorem, and for every live frame rather than only
  -- the current one. Left as a premise it would have done no work.)
  → SetsMem s s' (haddr hv hl) (enc-sv hv (readReg (regs (floc fs)) Output))
  → FlatCorr hv (flat-exec-instr store-indirect [] fs) s'
sim-store-indirect {hv} hl fs s s' corr i-eq live-hl guard sm =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    v = readReg (regs (floc fs)) Output
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToHeap (floc fs) hl v ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) v (floc fs)
              ≡ writeLocToHeap (floc fs) hl v
    floc-eq = trans (cong (λ m → exec-store-via-resolved m v (floc fs)) (cong sv-as-loc i-eq)) guard
    reduces : flat-exec-instr store-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = mkeep-in1 corr sm ; out-eq = mkeep-out corr sm ; scratch-eq = mkeep-scratch corr sm ; count-eq = mkeep-count corr sm
      ; clos-eq = mkeep-clos corr sm ; halt-eq = mkeep-halt corr sm ; sp-eq = mkeep-sp corr sm ; frontier-eq = mkeep-heap-reg corr sm ; dom-fresh = dom-fresh corr
      ; dom-written = store-dom-written hv hl v (floc fs) live-hl (dom-written corr)
      ; dom-sized = dom-sized corr
      ; heap-eq = store-heap-eq hv hl v s s' (floc fs) sm live-hl (heap-eq corr)
      ; lo-le = mkeep-lo-le corr sm
      ; untouched = untouched-heap-store hl (enc-sv hv v) live-hl corr sm
      ; stack-eq = windows-heap-store hl (enc-sv hv v) live-hl corr sm }

-- store-indirect-suc: *(sucLoc Input1) := Output ↔ `mov [rdi+slot], rax`.
sim-store-indirect-suc : {hv : HeapView} (hl : HeapLocation) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
  → HDom hv (sucHL hl)     -- the store target (second cell) is live
  → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
    ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
  → SetsMem s s' (haddr hv (sucHL hl)) (enc-sv hv (readReg (regs (floc fs)) Output))
  → FlatCorr hv (flat-exec-instr store-indirect-suc [] fs) s'
sim-store-indirect-suc {hv} hl fs s s' corr i-eq live-shl guard sm =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    v = readReg (regs (floc fs)) Output
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToHeap (floc fs) (sucHL hl) v ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-suc-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) v (floc fs)
              ≡ writeLocToHeap (floc fs) (sucHL hl) v
    floc-eq = trans (cong (λ m → exec-store-suc-via-resolved m v (floc fs)) (cong sv-as-loc i-eq)) guard
    reduces : flat-exec-instr store-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = mkeep-in1 corr sm ; out-eq = mkeep-out corr sm ; scratch-eq = mkeep-scratch corr sm ; count-eq = mkeep-count corr sm
      ; clos-eq = mkeep-clos corr sm ; halt-eq = mkeep-halt corr sm ; sp-eq = mkeep-sp corr sm ; frontier-eq = mkeep-heap-reg corr sm ; dom-fresh = dom-fresh corr
      ; dom-written = store-dom-written hv (sucHL hl) v (floc fs) live-shl (dom-written corr)
      ; dom-sized = dom-sized corr
      ; heap-eq = store-heap-eq hv (sucHL hl) v s s' (floc fs) sm live-shl (heap-eq corr)
      ; lo-le = mkeep-lo-le corr sm
      ; untouched = untouched-heap-store (sucHL hl) (enc-sv hv v) live-shl corr sm
      ; stack-eq = windows-heap-store (sucHL hl) (enc-sv hv v) live-shl corr sm }

------------------------------------------------------------------------
-- STACK RESTORE: `restore-input slot` (Input1 := stack[current-frame, slot]) ↔
-- `mov rdi, [rsp + slot-to-disp slot]`. Identical to load-from-slot but the
-- destination is Input1/rdi (not Output/rax). Success case only; empty slot
-- routed as a residual.
------------------------------------------------------------------------
sim-restore-input : {hv : HeapView} (slot : Slot) (w : StoredValue FS) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
  → SetsRole s s' role-in1 (enc-sv hv w)
  → FlatCorr hv (flat-exec-instr (restore-input slot) [] fs) s'
sim-restore-input {hv} slot w fs s s' corr st-eq st =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    ex-eq : exec-abstract (restore-input slot) (floc fs) (falloc fs)
            ≡ (record (floc fs) { regs = writeReg (regs (floc fs)) Input1 w } , falloc fs)
    ex-eq = cong (λ mv → exec-restore-input-with-value mv (floc fs) (falloc fs)) st-eq
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Input1 w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    reduces : flat-exec-instr (restore-input slot) [] fs ≡ cleanFlat
    reduces = cong (λ p → record fs { floc = proj₁ p ; falloc = proj₂ p ; fpc = suc (fpc fs) }) ex-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = at-role st ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
      ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

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
store-slot-heap-eq : ∀ (hv : HeapView) (waddr : ℕ) (v' : Word) (s s' : State) (ls : LocState FS)
  → SetsMem s s' waddr v'
  → (∀ hl' → HDom hv hl' → readMem (memory s) (haddr hv hl') ≡ enc-maybe hv (heapMem ls hl'))
  → (∀ hl' → HDom hv hl' → (waddr ≡ haddr hv hl') → ⊥)
  → ∀ hl' → HDom hv hl' → readMem (memory s') (haddr hv hl') ≡ enc-maybe hv (heapMem ls hl')
store-slot-heap-eq hv waddr v' s s' ls sm pre disj hl' live =
  trans (off-addr sm (haddr hv hl') (λ eq → disj hl' live (sym eq))) (pre hl' live)

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
store-slot-stack-eq : ∀ {am : AddrMap} {s s' : State} (base : ℕ) (slot : Slot) (Out : StoredValue FS) (ls : LocState FS) (cf : Frame) (bound : ℕ)
  → SetsMem s s' (base + slot-to-disp slot) (enc-sv-at am Out)
  → (∀ k → k < bound → ∀ (v : StoredValue FS) → stackMem ls cf k ≡ just v
       → readMem (memory s) (base + slot-to-disp k) ≡ just (enc-sv-at am v))
  → ∀ k → k < bound → ∀ (v : StoredValue FS)
  → readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k) ≡ just v
  → readMem (memory s') (base + slot-to-disp k) ≡ just (enc-sv-at am v)
store-slot-stack-eq {am} {s} {s'} base slot Out ls cf bound sm old k k<b v ev = go (k ≟ slot) ev
  where
    just-inj : ∀ {x y : StoredValue FS} → just x ≡ just y → x ≡ y
    just-inj refl = refl
    go : Dec (k ≡ slot)
       → readLoc (writeLoc ls (AtStack cf slot) Out) (AtStack cf k) ≡ just v
       → readMem (memory s') (base + slot-to-disp k) ≡ just (enc-sv-at am v)
    go (yes refl) ev' =
      trans (at-addr sm)
            (cong (λ w → just (enc-sv-at am w))
                  (just-inj (trans (sym (writeLoc-read-same-stack ls cf slot Out)) ev')))
    go (no  p)    ev' =
      trans (off-addr sm (base + slot-to-disp k)
              (λ eq → p (slot-addr-inj base k slot eq)))
            (old k k<b v (trans (sym (writeLoc-preserves-other ls (AtStack cf slot) (AtStack cf k) Out
                                        (λ eq → p (sym (atstack-slot-inj cf eq))))) ev'))

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
windows-slot-store : ∀ {am : AddrMap} {s s' : State} (ls : LocState FS) (cf : Frame)
                       (b : ℕ) (slot : Slot) (Out : StoredValue FS)
                       (fl : ℕ) (fr : List (Frame × ℕ))
                   → SetsMem s s' (frame-base cf + slot-to-disp slot) (enc-sv-at am Out)
                   → slot < b
                   → StackWindows am (memory s) (stackMem ls) fl ((cf , b) ∷ fr)
                   → StackWindows am (memory s')
                                     (stackMem (writeLoc ls (AtStack cf slot) Out)) fl ((cf , b) ∷ fr)
windows-slot-store {am} {s} {s'} ls cf b slot Out fl fr sm slot<b (bd , win , rest) =
  bd
  , store-slot-stack-eq {am} (frame-base cf) slot Out ls cf b sm win
  , windows-above {am} (memory s) (memory s') (stackMem ls) (stackMem (writeLoc ls (AtStack cf slot) Out))
      (frame-base cf + slots b) fr
      (λ a le → off-addr sm a (λ eq → <⇒≢ (<-transˡ w<fl le) (sym eq)))
      (λ f' le k → writeLoc-preserves-other ls (AtStack cf slot) (AtStack f' k) Out
                     (λ eq → <-irrefl (cong frame-base (atstack-frame-inj eq)) (base< le)))
      rest
  where
    waddr = frame-base cf + slot-to-disp slot
    w<fl : waddr < frame-base cf + slots b
    w<fl = +-monoʳ-< (frame-base cf) (*-monoˡ-< slot-size slot<b)
    base< : ∀ {f' : Frame} → frame-base cf + slots b ≤ frame-base f' → frame-base cf < frame-base f'
    base< le = <-transˡ (m<m+n (frame-base cf) (*-monoˡ-< slot-size (<-transʳ z≤n slot<b))) le

sim-store-at-slot : {hv : HeapView} (slot : Slot) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  -- THE FRAME DISCIPLINE (Plan 0.63, D085): the written slot is inside the
  -- current frame's own reservation. See `windows-slot-store` — beyond it the
  -- store would silently land in the caller's window.
  → slot < frame-slots (falloc fs)
  -- stack/heap disjointness: the written slot address aliases no live heap cell.
  → (∀ hl' → HDom hv hl' → (rreg s sp-reg + slot-to-disp slot ≡ haddr hv hl') → ⊥)
  → SetsMem s s' (rreg s sp-reg + slot-to-disp slot)
                 (enc-sv hv (readReg (regs (floc fs)) Output))
  → FlatCorr hv (flat-exec-instr (store-at-slot slot) [] fs) s'
sim-store-at-slot {hv} slot fs s s' corr slot<b disj sm = corr-clean
  where
    base = rreg s sp-reg
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    -- the write is re-addressed off the frame BASE (`sp-eq`), which is the
    -- form every window speaks. With the post-state abstract this is a subst on
    -- the PREMISE rather than on the goal — `memory s'` names no address at all.
    sm-base : SetsMem s s' (frame-base cf + slot-to-disp slot) (enc-sv hv Out)
    sm-base = subst (λ a → SetsMem s s' (a + slot-to-disp slot) (enc-sv hv Out)) (sp-eq corr) sm
    corr-clean : FlatCorr hv (flat-exec-instr (store-at-slot slot) [] fs) s'
    corr-clean = record
      { in1-eq = mkeep-in1 corr sm ; out-eq = mkeep-out corr sm ; scratch-eq = mkeep-scratch corr sm ; count-eq = mkeep-count corr sm
      ; clos-eq = mkeep-clos corr sm ; halt-eq = mkeep-halt corr sm ; sp-eq = mkeep-sp corr sm ; frontier-eq = mkeep-heap-reg corr sm ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp slot) (enc-sv hv Out) s s' (floc fs)
                    sm (heap-eq corr) disj
      ; lo-le = mkeep-lo-le corr sm
      ; untouched = untouched-stack-store (base + slot-to-disp slot) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp slot))) corr sm
      ; stack-eq = windows-slot-store (floc fs) cf (frame-slots (falloc fs))
                     slot Out (lo hv) (saved-frames (falloc fs)) sm-base slot<b (stack-eq corr) }

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
sim-alloc-stack : {hv : HeapView} (n : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
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
  → lo' ≤ rreg s sp-reg ∸ slots n
  -- THE FRAME FITS (Plan 0.63, D085): the reservation does not run `%rsp` off
  -- the bottom of the address space. Without it `frame-base (shift cf n) + 8n`
  -- is `max(frame-base cf, 8n)` (truncated ∸), so the callee's window would not
  -- be provably BELOW the caller's and the frame list would not compose. The
  -- honest sibling of `heap-room`: stack overflow, spent here.
  → slots n ≤ rreg s sp-reg
  → SetsRole s s' role-sp (rreg s sp-reg ∸ slots n)
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (flat-exec-instr (instr-alloc-stack n) [] fs) s'
sim-alloc-stack {hv} n fs s s' corr fresh-abs lo' lo'≤lo front-lo' lo'≤sp-reg fits st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ())
  ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st
  -- the reservation moves %rsp DOWN n slots and the frame with it (`shift-base`)
  ; sp-eq = trans (at-role st) newbase
  ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
  ; heap-eq = keep-heap corr st
  ; lo-le = subst (lo' ≤_) (sym (at-role st)) lo'≤sp-reg
  ; untouched = λ a fa a<lo → trans (cong (λ m → readMem m a) (keeps-mem st))
                                    (untouched-descend lo' lo'≤lo front-lo' corr a fa a<lo)
  -- Plan 0.63: the prologue CONSES a frame (`enter-frame n`), so the post's
  -- windows are the callee's — bounded by its own reservation `n`, and fresh on
  -- both sides — on top of the pre-state's, whose floor rises from `lo` to the
  -- callee's window END. That end IS the caller's base (`fits`), so the caller's
  -- window is carried across the call untouched rather than dropped.
  ; stack-eq = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs)) lo'
                                          (frames-of (enter-frame n (falloc fs))))
                     (sym (keeps-mem st)) windows-s }
  where
    cf = current-frame (falloc fs)
    newbase : rreg s sp-reg ∸ slots n ≡ frame-base (shift-frame cf n)
    newbase = trans (cong (_∸ slots n) (sp-eq corr))
                    (trans (cong (λ w → frame-base cf ∸ n * w) (sym word-eq))
                           (sym (shift-base cf n)))
    -- VACUOUS: the callee frame is unwritten (`fresh-abs`), and the one-directional
    -- `Window` claims nothing about unwritten cells. The hypothesis `stackMem … ≡
    -- just v` contradicts `fresh-abs` outright.
    stk : ∀ k → k < n → ∀ (v : StoredValue FS)
        → stackMem (floc fs) (shift-frame cf n) k ≡ just v
        → readMem (memory s) ((rreg s sp-reg ∸ slots n) + slot-to-disp k)
            ≡ just (enc-sv-at (amap hv) v)
    stk k k<n v ev with trans (sym (fresh-abs k k<n)) ev
    ... | ()
    -- the callee's window ends exactly at the caller's base: `(rsp ∸ 8n) + 8n`
    -- is `rsp` because the frame FITS, and `rsp` is the caller's base.
    tail-le : frame-base (shift-frame cf n) + slots n ≤ frame-base cf
    tail-le = ≤-reflexive (trans (cong (_+ slots n) (sym newbase))
                                 (trans (m∸n+n≡m fits) (sp-eq corr)))
    windows-s = subst (lo' ≤_) newbase lo'≤sp-reg
              , win-at (amap hv) (memory s) (stackMem (floc fs)) (shift-frame cf n) n
                        (rreg s sp-reg ∸ slots n) newbase stk
              , windows-reanchor (lo hv) (frame-base (shift-frame cf n) + slots n)
                  cf (frame-slots (falloc fs)) (saved-frames (falloc fs)) tail-le (stack-eq corr)

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
sim-thunk : {hv : HeapView} (b : ℕ)
            (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  -- NO `fresh-abs` PREMISE (Plan 0.54 rung D): `do-thunk` CLEARS the entered
  -- frame, so the callee window is vacuous by COMPUTATION rather than by
  -- assumption. Postulating freshness here would have been assuming something
  -- false — a re-entered frame keeps the previous incarnation's writes unless
  -- the machine clears them, which is why the fix belongs in `do-thunk`.
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ rreg s sp-reg ∸ slots b
  → slots b ≤ rreg s sp-reg
  → SetsRole s s' role-sp (rreg s sp-reg ∸ slots b)
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo') (do-thunk b fs) s'
sim-thunk {hv} b fs s s' corr lo' lo'≤lo front-lo' lo'≤sp-reg fits st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ())
  ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st
  ; sp-eq = trans (at-role st) newbase
  ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr
  ; dom-sized = dom-sized corr
  ; heap-eq = keep-heap corr st
  ; lo-le = subst (lo' ≤_) (sym (at-role st)) lo'≤sp-reg
  ; untouched = λ a fa a<lo → trans (cong (λ m → readMem m a) (keeps-mem st))
                                    (untouched-descend lo' lo'≤lo front-lo' corr a fa a<lo)
  ; stack-eq = subst (λ m → StackWindows (amap hv) m (stackMem (floc (do-thunk b fs))) lo'
                                          (frames-of (falloc (do-thunk b fs))))
                     (sym (keeps-mem st)) windows-s }
  where
    cf = current-frame (falloc fs)
    nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
    nothing≢just ()
    -- the entered frame reads `nothing` below its reservation, by `clear-frame`
    head-window : ∀ (k : Slot) → k < b → ∀ (v : StoredValue FS)
                → stackMem (floc (do-thunk b fs)) (shift-frame cf b) k ≡ just v
                → readMem (memory s) (frame-base (shift-frame cf b) + slot-to-disp k)
                    ≡ just (enc-sv-at (amap (descend-view hv lo' lo'≤lo front-lo')) v)
    head-window k k<b v ev with FrameSemantics._≟F_ FS (shift-frame cf b) (shift-frame cf b) | Data.Nat.Properties._<?_ k b
    ... | yes _ | yes _ = ⊥-elim (nothing≢just ev)
    ... | yes _ | no ¬p = ⊥-elim (¬p k<b)
    ... | no ¬q | _     = ⊥-elim (¬q refl)
    newbase : rreg s sp-reg ∸ slots b ≡ frame-base (shift-frame cf b)
    newbase = trans (cong (_∸ slots b) (sp-eq corr))
                    (trans (cong (λ w → frame-base cf ∸ b * w) (sym word-eq))
                           (sym (shift-base cf b)))
    tail-le : frame-base (shift-frame cf b) + slots b ≤ frame-base cf
    tail-le = ≤-reflexive (trans (cong (_+ slots b) (sym newbase))
                                 (trans (m∸n+n≡m fits) (sp-eq corr)))
    windows-s = subst (lo' ≤_) newbase lo'≤sp-reg
              , head-window
              , windows-forget (stackMem (floc fs)) (stackMem (floc (do-thunk b fs)))
                  (frame-base (shift-frame cf b) + slots b) (saved-frames (falloc fs))
                  (λ f' k' v' → MemOps.clear-frame-just (stackMem (floc fs))
                                  (shift-frame cf b) b f' k' v')
                  (windows-lower (frame-base cf + slots (frame-slots (falloc fs)))
                     (frame-base (shift-frame cf b) + slots b)
                     (saved-frames (falloc fs))
                     (≤-trans tail-le (m≤m+n (frame-base cf) (slots (frame-slots (falloc fs)))))
                     (proj₂ (proj₂ (stack-eq corr))))

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
-- THE CALL'S FRAME EFFECT, and ONLY that (plan 0.65 G2, 2026-08-16).
--
-- This used to be `sim-call`, which took a `SetsRoleMem` — it assumed the call
-- WRITES the return address to the reserved cell, which is x86-64's ABI and not
-- RISC-V's (`jalr` writes `ra` and touches no memory). What the two arches
-- share is the FRAME DESCENT: one slot, the entered frame reserving nothing.
--
-- The arch that also stores composes `corr-store-gap` on top — and the cell it
-- writes IS the post-state's gap cell, so the same lemma the body marker uses
-- covers it. The core cannot do that composition itself: `State` is abstract,
-- so only an arch can name the intermediate state.

------------------------------------------------------------------------
-- THE CALL'S FRAME EFFECT, and ONLY that (plan 0.65 G2, 2026-08-16).
--
-- This used to be `sim-call`, which took a `SetsRoleMem` — it assumed the call
-- WRITES the return address to the reserved cell, which is x86-64's ABI and not
-- RISC-V's (`jalr` writes `ra` and touches no memory). What the two arches
-- share is the FRAME DESCENT: one slot, the entered frame reserving nothing.
--
-- The arch that also stores composes `corr-store-gap` on top — and the cell it
-- writes IS the post-state's gap cell, so the same lemma the body marker uses
-- covers it. The core cannot do that composition itself: `State` is abstract,
-- so only an arch can name the intermediate state.
------------------------------------------------------------------------
sim-call-frame : {hv : HeapView} (jₐ : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
  → lo' ≤ rreg s sp-reg ∸ slot-size
  -- ROOM FOR THE RETURN ADDRESS: the one slot the call spends. Same class as
  -- `StackRoom` (D087) and supplied the same way.
  → slot-size ≤ rreg s sp-reg
  → SetsRole s s' role-sp (rreg s sp-reg ∸ slot-size)
  → FlatCorr (descend-view hv lo' lo'≤lo front-lo')
             (record fs { falloc = enter-call (falloc fs)
                        ; fret   = suc (fpc fs) ∷ fret fs
                        -- THE LINK: the call writes it on every arch, and it is
                        -- what `RetAddrs`' head row reads until the callee's
                        -- marker spills it.
                        ; flink  = just (suc (fpc fs))
                        ; fpc    = jₐ })
             s'
sim-call-frame {hv} jₐ fs s s' corr lo' lo'≤lo front-lo' lo'≤sp-reg fits st = record
  { in1-eq = keep-in1 corr st (λ ())
  ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ())
  ; count-eq = keep-count corr st (λ ()) ; clos-eq = keep-clos corr st (λ ())
  ; halt-eq = keep-halt corr st
  ; sp-eq = trans (at-role st) newbase
  ; frontier-eq = keep-heap-reg corr st (λ ())
  ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr
  ; dom-sized = dom-sized corr
  ; heap-eq = λ hl d → trans (cong (λ m → readMem m (haddr hv hl)) (keeps-mem st))
                             (heap-eq corr hl d)
  ; lo-le = subst (lo' ≤_) (sym (at-role st)) lo'≤sp-reg
  ; untouched = λ a fa a<lo' → trans (cong (λ m → readMem m a) (keeps-mem st))
                                     (untouched-descend lo' lo'≤lo front-lo' corr a fa a<lo')
  ; stack-eq = subst (lo' ≤_) newbase lo'≤sp-reg
             , (λ k ())
             , windows-reanchor (frame-base cf) (frame-base (shift-frame cf 1) + slots 0)
                 cf (frame-slots (falloc fs)) (saved-frames (falloc fs))
                 tail-floor
                 (windows-above (memory s) (memory s')
                    (stackMem (floc fs)) (stackMem (floc fs))
                    (frame-base cf) ((cf , frame-slots (falloc fs)) ∷ saved-frames (falloc fs))
                    (λ a le → cong (λ m → readMem m a) (keeps-mem st))
                    (λ _ _ _ → refl)
                    (windows-reanchor (lo hv) (frame-base cf) cf (frame-slots (falloc fs))
                       (saved-frames (falloc fs)) ≤-refl (stack-eq corr))) }
  where
    cf    = current-frame (falloc fs)
    newbase : rreg s sp-reg ∸ slot-size ≡ frame-base (shift-frame cf 1)
    newbase = trans (cong (_∸ slot-size) (sp-eq corr))
                    (trans (cong (frame-base cf ∸_) (sym (*-identityˡ slot-size)))
                    (trans (cong (λ w → frame-base cf ∸ 1 * w) (sym word-eq))
                           (sym (shift-base cf 1))))
    -- the tail's floor is the entered frame's window END, and that frame
    -- reserves NOTHING — so the floor is its own base, one slot under the
    -- caller's, which is the gap the return address occupies (D086)
    tail-floor : frame-base (shift-frame cf 1) + slots 0 ≤ frame-base cf
    tail-floor =
      ≤-trans (≤-reflexive (trans (+-identityʳ (frame-base (shift-frame cf 1))) (sym newbase)))
              (≤-trans (m∸n≤m (rreg s sp-reg) slot-size)
                       (≤-reflexive (sp-eq corr)))

------------------------------------------------------------------------
-- DEALLOC-STACK, and the premise D085 DELETED.
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
sim-dealloc-stack : {hv : HeapView} (n : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  -- MATCHED PAIRING (plan 0.61): the frame this epilogue restores is the one the
  -- entry `alloc-stack n` shifted away from, so its base is where %rsp lands.
  → rreg s sp-reg + slots n
      ≡ frame-base (current-frame (leave-frame (falloc fs)))
  → SetsRole s s' role-sp (rreg s sp-reg + slots n)
  → FlatCorr hv (flat-exec-instr (instr-dealloc-stack n) [] fs) s'
sim-dealloc-stack {hv} n fs s s' corr restores st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = trans (at-role st) restores ; frontier-eq = keep-heap-reg corr st (λ ())
  -- the epilogue RAISES %rsp, so the high-water mark stays below it — and the mark
  -- itself does NOT move back up: the freed cells keep their contents, which is
  -- exactly the dead memory the mark exists to remember.
  ; lo-le = subst (lo hv ≤_) (sym (at-role st))
                  (≤-trans (lo-le corr) (m≤m+n (rreg s sp-reg) (slots n)))
  ; untouched = keep-untouched corr st
  -- Plan 0.61: the epilogue RESTORES the caller's frame; the move leaves the
  -- allocation frontier alone, so `dom-fresh` only needs transporting.
  ; dom-fresh = λ {hl} d → subst (λ m → ref-id (heap-ref hl) < m)
                                 (sym (leave-frame-heap-ref (falloc fs))) (dom-fresh corr d)
  ; dom-written = dom-written corr
  ; dom-sized = λ hl lt → dom-sized corr hl
                  (subst (λ szs → heap-offset hl < szs (ref-id (heap-ref hl)))
                         (leave-frame-block-size (falloc fs)) lt)
  ; heap-eq = keep-heap corr st
  -- THE RETURN'S WINDOW, DERIVED: drop the callee's frame and the caller's
  -- window is what is left (`windows-leave`).
  ; stack-eq = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs)) (lo hv)
                                          (frames-of (leave-frame (falloc fs))))
                     (sym (keeps-mem st)) (windows-leave (falloc fs) (lo hv) (stack-eq corr)) }


-- (`sim-call` STOOD HERE and is DELETED, 2026-08-16. It took a `SetsRoleMem`,
-- i.e. it assumed the call WRITES the return address to the reserved cell —
-- x86-64's ABI, not RISC-V's. What the arches share is `sim-call-frame` above;
-- the arch that also stores composes `corr-store-gap`, and the cell it writes
-- IS the post-state's gap cell, so no new lemma was needed. x86-64's
-- `block-step-call` now does exactly that and is unchanged in strength.)

------------------------------------------------------------------------
-- Plan 0.65 G1c step 2: the post-state used to write `%rsp` TWICE, nested —
-- once for the `add` and once for the `ret`'s pop. As a claim about the state
-- AFTER the pair, that is one write of the final value, and the nesting
-- disappears with the literal.
sim-ret : {hv : HeapView} (b rpc : ℕ) (rest : List ℕ)
          (fs : FlatState) (s s' : State) → FlatCorr hv fs s
        → fret fs ≡ rpc ∷ rest
        → rreg s sp-reg + slots b + slot-size
            ≡ frame-base (current-frame (leave-frame (falloc fs)))
        → SetsRole s s' role-sp (rreg s sp-reg + slots b + slot-size)
        → FlatCorr hv (do-ret (fret fs) fs) s'
sim-ret {hv} b rpc rest fs s s' corr req restores st rewrite req = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ())
  ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = trans (at-role st) restores ; frontier-eq = keep-heap-reg corr st (λ ())
  -- `%rsp` only RISES, so the high-water mark stays below it and the freed
  -- cells keep their contents — the dead memory the mark exists to remember.
  ; lo-le = subst (lo hv ≤_) (sym (at-role st))
              (≤-trans (lo-le corr)
                (≤-trans (m≤m+n (rreg s sp-reg) (slots b))
                         (m≤m+n (rreg s sp-reg + slots b) slot-size)))
  ; untouched = keep-untouched corr st
  ; dom-fresh = λ {hl} d → subst (λ m → ref-id (heap-ref hl) < m)
                                 (sym (leave-frame-heap-ref (falloc fs))) (dom-fresh corr d)
  ; dom-written = dom-written corr
  ; dom-sized = λ hl lt → dom-sized corr hl
                  (subst (λ szs → heap-offset hl < szs (ref-id (heap-ref hl)))
                         (leave-frame-block-size (falloc fs)) lt)
  ; heap-eq = keep-heap corr st
  -- drop the callee's frame and the caller's window is what is left
  ; stack-eq = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs)) (lo hv)
                                          (frames-of (leave-frame (falloc fs))))
                     (sym (keeps-mem st)) (windows-leave (falloc fs) (lo hv) (stack-eq corr)) }

------------------------------------------------------------------------
-- FRAME PUSH / POP: the `%rbp` frame model is a FOSSIL — `sim-push-frame`
-- and `sim-pop-frame` were deleted 2026-08-04 together with their
-- block-steps. The live model is frameless and `%rsp`-relative; Plan 0.63's
-- closure frames ride on `sim-alloc-stack`/`sim-dealloc-stack` above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- LOAD CONST (int): `instr-load-const fits-int v` (Output := SV-Lit fits-int v)
-- ↔ `mov rax, imm v`. With enc-sv(SV-Lit fits-int v) = v, the loaded immediate
-- matches the encoded literal exactly, so out-eq is refl; nothing else changes
-- (writeReg Output preserves the other regs / stack / heap / halt).
------------------------------------------------------------------------
sim-load-const : {hv : HeapView} (v : Carrier) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-out (lit-word v)
  → FlatCorr hv (flat-exec-instr (instr-load-const fits-int v) [] fs) s'
sim-load-const {hv} v fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- …and the FLOAT constant (D079/D113): identical, with the IEEE-754 pattern as
-- the immediate. The payload is a `Dyadic` — source syntax — and the machine
-- MATERIALISES it (`lit-value`, i.e. `encode (float-format FS)`), so what the
-- emitter must put in the register is that same encoding. `enc-sv` is now the
-- identity here, so `out-eq` is `at-role` exactly as in the int case.
sim-load-const-float : {hv : HeapView} (v : Dyadic) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-out (lit-word (lit-value fits-float v))
  → FlatCorr hv (flat-exec-instr (instr-load-const fits-float v) [] fs) s'
sim-load-const-float {hv} v fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

------------------------------------------------------------------------
-- LOAD CODE ADDR: `instr-load-code-addr n` (Output := SV-Code n) ↔ `lea rax,
-- .L_thunk_n(%rip)`.
--
-- D096: `out-eq` used to be `refl` because BOTH sides said `idx n` — the
-- label's IDENTITY. That agreement was the defect: the concrete `lea` now
-- RESOLVES the label (as `jmp` does), so the value is the body's index, and the
-- view's code map has to be that resolution. The lemma therefore takes the
-- resolved value and the equation tying the map to it; the block-step supplies
-- both, from the program it can see and `CompiledCorr.code-eq`.
------------------------------------------------------------------------
sim-load-code-addr : {hv : HeapView} (n : LabelId) (j : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → caddr hv n ≡ j
  → SetsRole s s' role-out j
  → FlatCorr hv (flat-exec-instr (instr-load-code-addr n) [] fs) s'
sim-load-code-addr {hv} n j fs s s' corr ceq st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = trans (at-role st) (sym ceq) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

------------------------------------------------------------------------
-- SAVE CLOSURE REG: `instr-save-closure-reg` ↔ `mov r12, rdi`.
--
-- This USED to be "the correspondence is unchanged" — `%r12` was untracked and
-- the abstract side was the identity. Both halves moved: D092 made the flat
-- machine write `fclosure`, and D097 made `FlatCorr` track `%r12`. So the step
-- now has real content, and it is exactly the same equation twice: what `%rdi`
-- holds is what `Input1` holds, before and after the pair of copies.
------------------------------------------------------------------------
sim-save-closure-reg : {hv : HeapView} (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-clos (rreg s in1-reg)
  → FlatCorr hv (flat-exec-instr instr-save-closure-reg [] fs) s'
sim-save-closure-reg {hv} fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; clos-eq = trans (at-role st) (in1-eq corr) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

------------------------------------------------------------------------
-- Arithmetic reg-ops. count-inc / scratch-dec increment/decrement a TAG.
--
-- Plan 0.65 G1c step 2: these two used to carry a `newFlags : X.Flags`
-- parameter, because `add r14, 1` really does set flags and the reconstructed
-- post-state had to put SOMETHING in that field. With the post-state abstract
-- the parameter is simply GONE — there is no field to fill, and the
-- correspondence never read it. That deletion is finding 2 in one line.
------------------------------------------------------------------------
inc-enc : ∀ {am : AddrMap} (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k
        → enc-sv-at am v + 1 ≡ enc-sv-at am (sv-succ v)
inc-enc .(SV-Tag k) k refl = +-comm k 1

dec-enc : ∀ {am : AddrMap} (v : StoredValue FS) (k : ℕ) → v ≡ SV-Tag k
        → enc-sv-at am v ∸ 1 ≡ enc-sv-at am (sv-pred v)
dec-enc .(SV-Tag zero)    zero    refl = refl
dec-enc .(SV-Tag (suc m)) (suc m) refl = refl

-- Plan 0.54 D item 4: the tally increment is on `Count`/`%r14`, so it is
-- `count-eq` that carries the `inc-enc` step — the exact mirror of the
-- pre-split version, with no ABI register involved.
sim-reg-count-inc : {hv : HeapView} (k : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Count ≡ SV-Tag k
  → SetsRole s s' role-count (rreg s count-reg + 1)
  → FlatCorr hv (flat-exec-instr (instr-reg-op count-inc) [] fs) s'
sim-reg-count-inc {hv} k fs s s' corr c-eq st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ())
  ; count-eq = trans (at-role st)
                   (trans (cong (_+ 1) (count-eq corr)) (inc-enc (readReg (regs (floc fs)) Count) k c-eq))
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

sim-reg-scratch-dec : {hv : HeapView} (k : ℕ) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
  → SetsRole s s' role-scratch (rreg s scratch-reg ∸ 1)
  → FlatCorr hv (flat-exec-instr (instr-reg-op scratch-dec) [] fs) s'
sim-reg-scratch-dec {hv} k fs s s' corr sc-eq st = record
  { in1-eq = keep-in1 corr st (λ ()) ; out-eq = keep-out corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; scratch-eq = trans (at-role st)
                   (trans (cong (_∸ 1) (scratch-eq corr)) (dec-enc (readReg (regs (floc fs)) Scratch) k sc-eq))
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ()) ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

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

-- The fresh block's BASE sits exactly at the frontier — the equation `out-eq`
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
                    (mem : Memory) (stk : StackMem FS) (fl : ℕ) (fr : List (Frame × ℕ))
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
-- the old frontier — so `out-eq` is `frontier-eq` transported by `ext-addr-base`.
-- The store-WF premises are what make the extension INVISIBLE to everything else
-- (no live value referenced the not-yet-allocated ref).
sim-alloc-heap : ∀ {hv : HeapView} (n : ℕ)
                 (fs : FlatState) (s s' : State) (corr : FlatCorr hv fs s)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input1)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Scratch)
  → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Count)
  -- …and the CLOSURE REGISTER (D097): it is a `FlatState` field rather than a
  -- register, so `FlatWF` does not cover it — the run invariant supplies this
  -- one, exactly as it supplies the three above.
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
  -- the two-instruction block writes Output (the block's base) and then the
  -- frontier; `Sets2Roles` is what says the OTHER five roles survive both.
  → Sets2Roles s s' role-out role-heap
               (rreg s heap-reg)
               (rreg s heap-reg + slots n)
  → FlatCorr (extend-view hv (next-heap-ref (falloc fs)) n (dom-fresh corr) room)
             (flat-exec-instr (instr-alloc-heap n) [] fs) s'
sim-alloc-heap {hv} n fs s s' corr wf1 wfs wfc wfcl wf-heap wf-stack fresh-abs room s2 = record
  { in1-eq  = trans (trans (off-roles s2 role-in1 (λ ()) (λ ())) (in1-eq corr)) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Input1) wf1))
  ; count-eq  = trans (trans (off-roles s2 role-count (λ ()) (λ ())) (count-eq corr)) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Count) wfc))
  ; out-eq  = trans (trans (at-role₁ s2) (frontier-eq corr)) (sym (ext-addr-base hv st))
  ; scratch-eq  = trans (trans (off-roles s2 role-scratch (λ ()) (λ ())) (scratch-eq corr)) (sym (enc-ext hv st n dfr room (readReg (regs (floc fs)) Scratch) wfs))
  ; clos-eq  = trans (trans (off-roles s2 role-clos (λ ()) (λ ())) (clos-eq corr)) (sym (enc-ext hv st n dfr room (fclosure fs) wfcl))
  ; halt-eq = trans (keeps-halt₂ s2) (halt-eq corr)
  ; sp-eq  = trans (off-roles s2 role-sp (λ ()) (λ ())) (sp-eq corr)
  ; frontier-eq  = trans (at-role₂ s2) (cong (_+ slots n) (frontier-eq corr))
  ; dom-fresh = df
  -- the bump writes no heap cell, so anything written was covered BEFORE and
  -- enters the extended domain as an old cell
  ; dom-written = λ hl eq → ext-old (dom-written corr hl eq)
  ; dom-sized = ds
  ; heap-eq = hp
  -- %rsp is untouched by the bump; the virgin region only SHRANK (its floor rose
  -- from `hfront` to `hfront + 8n`), so both invariants transport.
  ; lo-le = subst (lo hv ≤_) (sym (off-roles s2 role-sp (λ ()) (λ ()))) (lo-le corr)
  ; untouched = λ a fa a<lo → trans (cong (λ m → readMem m a) (keeps-mem₂ s2))
                                    (untouched corr a (≤-trans (m≤m+n (hfront hv) (slots n)) fa) a<lo)
  ; stack-eq = subst (λ m → StackWindows (amap (extend-view hv st n dfr room)) m
                                          (stackMem (floc fs)) (lo hv) (frames-of (falloc fs)))
                     (sym (keeps-mem₂ s2))
                     (windows-enc-ext hv st n dfr room (memory s) (stackMem (floc fs))
                        (lo hv) (frames-of (falloc fs)) wf-stack (stack-eq corr))
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
    fresh-x86 : ∀ i → i < n → readMem (memory s) (hfront hv + slot-to-disp i) ≡ nothing
    fresh-x86 i i<n = untouched corr (hfront hv + slot-to-disp i)
                        (m≤m+n (hfront hv) (slot-to-disp i))
                        (<-transˡ (+-monoʳ-< (hfront hv) (*-monoˡ-< slot-size i<n)) room)
    df : ∀ {hl : HeapLocation} → ExtDom hv st n hl → ref-id (heap-ref hl) < suc st
    df (ext-old d)       = m<n⇒m<1+n (dfr d)
    df (ext-fresh req _) = subst (_< suc st) (sym req) ≤-refl
    -- the bump touches no memory, so the extended heap agreement is the old one
    -- carried across `keeps-mem₂` — one `trans` in front of each clause.
    hp : ∀ (hl : HeapLocation) → ExtDom hv st n hl
       → readMem (memory s') (ext-addr hv st hl) ≡ enc-maybe hv' (heapMem (floc fs) hl)
    hp hl (ext-old d) =
      trans (cong (λ m → readMem m (ext-addr hv st hl)) (keeps-mem₂ s2))
      (trans (cong (readMem (memory s)) (ext-addr-old hv st hl (dfr d)))
            (trans (heap-eq corr hl d)
                   (sym (enc-ext-maybe hv st n dfr room (heapMem (floc fs) hl) (wf-heap hl d)))))
    hp hl (ext-fresh req off<n) =
      trans (cong (λ m → readMem m (ext-addr hv st hl)) (keeps-mem₂ s2))
      (trans (cong (readMem (memory s)) (ext-addr-fresh hv st hl req))
            (trans (fresh-x86 (heap-offset hl) off<n)
                   (sym (cong (enc-maybe hv') (fresh-abs hl req)))))

------------------------------------------------------------------------
-- STACK ADDRESS: `lea-slot slot` (Output := &stack[frame, slot]) ↔
-- `lea rax, [rsp + slot-to-disp slot]`.
--
-- THE payoff of plan 0.61. The abstract value is `SV-Ptr (AtStack cf slot)`
-- and its encoding is the slot's real address `slot-addr cf slot`
-- (= `frame-base cf + slot·word`, `slot-addr-linear`); the x86 computes
-- `rsp + slot·8`, and `sp-eq` anchors `%rsp` to `frame-base cf`. Under the
-- old model this was unprovable in principle: the callee's slot k and its
-- caller's slot k were the same abstract cell, so no address existed.
------------------------------------------------------------------------
sim-lea-slot : {hv : HeapView} (slot : Slot) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → SetsRole s s' role-out (rreg s sp-reg + slot-to-disp slot)
  → FlatCorr hv (flat-exec-instr (lea-slot slot) [] fs) s'
sim-lea-slot {hv} slot fs s s' corr st = record
  { in1-eq = keep-in1 corr st (λ ()) ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
  ; out-eq = trans (at-role st) addr-eq
  ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ())
  ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }
  where
    cf = current-frame (falloc fs)
    addr-eq : rreg s sp-reg + slot-to-disp slot ≡ slot-addr cf slot
    addr-eq = trans (cong (_+ slot-to-disp slot) (sp-eq corr))
                    (trans (cong (λ w → frame-base cf + slot * w) (sym word-eq))
                           (sym (slot-addr-linear cf slot)))

-- Load through a STACK pointer (plan 0.61): `Input1` holds `SV-Ptr (AtStack f k)`
-- and the slot holds `w`. Structurally identical to `sim-load-indirect`; only the
-- residence differs, and it is only expressible at all because a stack pointer
-- now denotes `slot-addr f k` instead of the old placeholder `0`.
sim-load-indirect-stack : {hv : HeapView} (f : Frame) (k : Slot) (w : StoredValue FS)
                          (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → readLoc (floc fs) (AtStack f k) ≡ just w
  → SetsRole s s' role-out (enc-sv hv w)
  → FlatCorr hv (flat-exec-instr load-indirect [] fs) s'
sim-load-indirect-stack {hv} f k w fs s s' corr i-eq st-eq st =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-load-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) st-eq)
    reduces : flat-exec-instr load-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
      ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ())
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- Second cell through a STACK pointer: `sucLoc (AtStack f k) = AtStack f (suc k)`,
-- so this is `sim-load-indirect-stack` one slot along.
sim-load-indirect-suc-stack : {hv : HeapView} (f : Frame) (k : Slot) (w : StoredValue FS)
                              (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
  → readLoc (floc fs) (AtStack f (suc k)) ≡ just w
  → SetsRole s s' role-out (enc-sv hv w)
  → FlatCorr hv (flat-exec-instr load-indirect-suc [] fs) s'
sim-load-indirect-suc-stack {hv} f k w fs s s' corr i-eq st-eq st =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    cleanFlat : FlatState
    cleanFlat = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-load-suc-via-resolved Output (sv-as-loc (readReg (regs (floc fs)) Input1)) (floc fs)
              ≡ record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
    floc-eq = trans (cong (λ m → exec-load-suc-via-resolved Output m (floc fs)) (cong sv-as-loc i-eq))
                    (cong (λ mv → exec-load-with-value Output mv (floc fs)) st-eq)
    reduces : flat-exec-instr load-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = keep-in1 corr st (λ ()) ; out-eq = at-role st ; scratch-eq = keep-scratch corr st (λ ()) ; count-eq = keep-count corr st (λ ())
      ; clos-eq = keep-clos corr st (λ ()) ; halt-eq = keep-halt corr st ; sp-eq = keep-sp corr st (λ ()) ; frontier-eq = keep-heap-reg corr st (λ ())
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr ; heap-eq = keep-heap corr st ; lo-le = keep-lo-le corr st (λ ()) ; untouched = keep-untouched corr st ; stack-eq = keep-stack corr st }

-- STORE through a stack pointer: `writeLoc … (AtStack f k)` IS the plain stack
-- write (the cross-region guard only concerns the heap branch), so this reuses
-- the same read-back/disjointness machinery as `sim-store-at-slot` — the only
-- difference is that the address comes from `Input1` rather than the instruction.
sim-store-indirect-stack : {hv : HeapView} (k : Slot) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
  -- the frame discipline, as for `sim-store-at-slot` (`stack-ptr-current`)
  → k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (rreg s sp-reg + slot-to-disp k ≡ haddr hv hl') → ⊥)
  → SetsMem s s' (rreg s sp-reg + slot-to-disp k)
                 (enc-sv hv (readReg (regs (floc fs)) Output))
  → FlatCorr hv (flat-exec-instr store-indirect [] fs) s'
sim-store-indirect-stack {hv} k fs s s' corr i-eq k<b disj sm =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    base = rreg s sp-reg
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    sm-base : SetsMem s s' (frame-base cf + slot-to-disp k) (enc-sv hv Out)
    sm-base = subst (λ a → SetsMem s s' (a + slot-to-disp k) (enc-sv hv Out)) (sp-eq corr) sm
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToStack (floc fs) cf k Out
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) Out (floc fs)
              ≡ writeLocToStack (floc fs) cf k Out
    floc-eq = cong (λ m → exec-store-via-resolved m Out (floc fs)) (cong sv-as-loc i-eq)
    reduces : flat-exec-instr store-indirect [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = mkeep-in1 corr sm ; out-eq = mkeep-out corr sm ; scratch-eq = mkeep-scratch corr sm ; count-eq = mkeep-count corr sm
      ; clos-eq = mkeep-clos corr sm ; halt-eq = mkeep-halt corr sm ; sp-eq = mkeep-sp corr sm ; frontier-eq = mkeep-heap-reg corr sm
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp k) (enc-sv hv Out) s s' (floc fs)
                    sm (heap-eq corr) disj
      ; lo-le = mkeep-lo-le corr sm
      ; untouched = untouched-stack-store (base + slot-to-disp k) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp k))) corr sm
      ; stack-eq = windows-slot-store (floc fs) cf (frame-slots (falloc fs))
                     k Out (lo hv) (saved-frames (falloc fs)) sm-base k<b (stack-eq corr) }

-- …and the SECOND cell. `sucLoc (AtStack cf k) = AtStack cf (suc k)` reduces, so
-- this is literally the same proof at slot `suc k` — `store-slot-stack-eq` is
-- generic in the written slot, and the pair's second slot belongs to the same
-- frame the prologue reserved (`stack-ptr-current-suc`).
sim-store-indirect-suc-stack : {hv : HeapView} (k : Slot) (fs : FlatState) (s s' : State) → FlatCorr hv fs s
  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack (current-frame (falloc fs)) k)
  -- the PAIR's second slot is the one reserved (`stack-ptr-current-suc`)
  → suc k < frame-slots (falloc fs)
  → (∀ hl' → HDom hv hl' → (rreg s sp-reg + slot-to-disp (suc k) ≡ haddr hv hl') → ⊥)
  → SetsMem s s' (rreg s sp-reg + slot-to-disp (suc k))
                 (enc-sv hv (readReg (regs (floc fs)) Output))
  → FlatCorr hv (flat-exec-instr store-indirect-suc [] fs) s'
sim-store-indirect-suc-stack {hv} k fs s s' corr i-eq sk<b disj sm =
  subst (λ z → FlatCorr hv z s') (sym reduces) corr-clean
  where
    base = rreg s sp-reg
    Out  = readReg (regs (floc fs)) Output
    cf   = current-frame (falloc fs)
    sm-base : SetsMem s s' (frame-base cf + slot-to-disp (suc k)) (enc-sv hv Out)
    sm-base = subst (λ a → SetsMem s s' (a + slot-to-disp (suc k)) (enc-sv hv Out)) (sp-eq corr) sm
    cleanFlat : FlatState
    cleanFlat = record fs { floc = writeLocToStack (floc fs) cf (suc k) Out
                          ; falloc = falloc fs ; fpc = suc (fpc fs) }
    floc-eq : exec-store-suc-via-resolved (sv-as-loc (readReg (regs (floc fs)) Input1)) Out (floc fs)
              ≡ writeLocToStack (floc fs) cf (suc k) Out
    floc-eq = cong (λ m → exec-store-suc-via-resolved m Out (floc fs)) (cong sv-as-loc i-eq)
    reduces : flat-exec-instr store-indirect-suc [] fs ≡ cleanFlat
    reduces = cong (λ fl → record fs { floc = fl ; falloc = falloc fs ; fpc = suc (fpc fs) }) floc-eq
    corr-clean : FlatCorr hv cleanFlat s'
    corr-clean = record
      { in1-eq = mkeep-in1 corr sm ; out-eq = mkeep-out corr sm ; scratch-eq = mkeep-scratch corr sm ; count-eq = mkeep-count corr sm
      ; clos-eq = mkeep-clos corr sm ; halt-eq = mkeep-halt corr sm ; sp-eq = mkeep-sp corr sm ; frontier-eq = mkeep-heap-reg corr sm
      ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr ; dom-sized = dom-sized corr
      ; heap-eq = store-slot-heap-eq hv (base + slot-to-disp (suc k)) (enc-sv hv Out) s s' (floc fs)
                    sm (heap-eq corr) disj
      ; lo-le = mkeep-lo-le corr sm
      ; untouched = untouched-stack-store (base + slot-to-disp (suc k)) (enc-sv hv Out)
                      (≤-trans (lo-le corr) (m≤m+n base (slot-to-disp (suc k)))) corr sm
      ; stack-eq = windows-slot-store (floc fs) cf (frame-slots (falloc fs))
                     (suc k) Out (lo hv) (saved-frames (falloc fs)) sm-base sk<b (stack-eq corr) }

-- …AND THE WHOLE CORRESPONDENCE SURVIVES THAT STORE (plan 0.65 G2, 2026-08-16).
-- The record-level form of `windows-store-gap`, which is what riscv64's body
-- marker consumes: it spills `ra` onto the gap cell and changes NOTHING else,
-- so every register field rides across and the three memory fields each get the
-- same miss — the gap cell is at or above the current frame's base, hence above
-- the high-water mark, hence above the whole heap and the virgin region.
-- A WRITE THE CORRESPONDENCE CANNOT SEE (plan 0.65 G2, 2026-08-16): every ROLE
-- register keeps its value, memory and the halt flag are untouched, and the pc
-- is not a `FlatCorr` field. riscv64's return needs it — its `ld ra, 8b(sp)`
-- writes the LINK register, which is nobody's role, and x86-64 has no such
-- instruction because its `ret` pops straight into the pc.
corr-regs-agree : ∀ {hv : HeapView} (fs : FlatState) (s s' : State)
                → FlatCorr hv fs s
                → (∀ (ρ : Role) → rreg s' (reg-of ρ) ≡ rreg s (reg-of ρ))
                → memory s' ≡ memory s → xhalted s' ≡ xhalted s
                → FlatCorr hv fs s'
corr-regs-agree {hv} fs s s' corr rr mm hh = record
  { in1-eq = trans (rr role-in1) (in1-eq corr)
  ; out-eq = trans (rr role-out) (out-eq corr)
  ; scratch-eq = trans (rr role-scratch) (scratch-eq corr)
  ; count-eq = trans (rr role-count) (count-eq corr)
  ; clos-eq = trans (rr role-clos) (clos-eq corr)
  ; halt-eq = trans hh (halt-eq corr)
  ; sp-eq = trans (rr role-sp) (sp-eq corr)
  ; frontier-eq = trans (rr role-heap) (frontier-eq corr)
  ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr
  ; dom-sized = dom-sized corr
  ; heap-eq = λ hl d → trans (cong (λ m → readMem m (haddr hv hl)) mm) (heap-eq corr hl d)
  ; lo-le = subst (lo hv ≤_) (sym (rr role-sp)) (lo-le corr)
  ; untouched = λ c fc c<lo → trans (cong (λ m → readMem m c) mm) (untouched corr c fc c<lo)
  ; stack-eq = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs))
                                         (lo hv) (frames-of (falloc fs)))
                     (sym mm) (stack-eq corr) }

corr-store-gap : ∀ {hv : HeapView} (fs : FlatState) (s s' : State) (v : Word)
               → FlatCorr hv fs s
               → (∀ (r : Reg) → rreg s' r ≡ rreg s r)
               → xhalted s' ≡ xhalted s
               → memory s' ≡ writeMem (memory s)
                              (frame-base (current-frame (falloc fs))
                               + slots (frame-slots (falloc fs))) v
               → GapNext (frame-base (current-frame (falloc fs))
                          + slots (frame-slots (falloc fs))) (saved-frames (falloc fs))
               → FlatCorr hv fs s'
corr-store-gap {hv} fs s s' v corr rr hh mm gn = record
  { in1-eq = trans (rr in1-reg) (in1-eq corr)
  ; out-eq = trans (rr out-reg) (out-eq corr)
  ; scratch-eq = trans (rr scratch-reg) (scratch-eq corr)
  ; count-eq = trans (rr count-reg) (count-eq corr)
  ; clos-eq = trans (rr clos-reg) (clos-eq corr)
  ; halt-eq = trans hh (halt-eq corr)
  ; sp-eq = trans (rr sp-reg) (sp-eq corr)
  ; frontier-eq = trans (rr heap-reg) (frontier-eq corr)
  ; dom-fresh = dom-fresh corr ; dom-written = dom-written corr
  ; dom-sized = dom-sized corr
  ; heap-eq = λ hl d → trans (cong (λ m → readMem m (haddr hv hl)) mm)
                       (trans (read-write-miss (memory s) a v (haddr hv hl)
                                (<⇒≢ (<-transˡ (dom-below hv d) front≤a)))
                              (heap-eq corr hl d))
  ; lo-le = subst (lo hv ≤_) (sym (rr sp-reg)) (lo-le corr)
  ; untouched = λ c fc c<lo → trans (cong (λ m → readMem m c) mm)
                              (trans (read-write-miss (memory s) a v c
                                       (<⇒≢ (<-transˡ c<lo lo≤a)))
                                     (untouched corr c fc c<lo))
  ; stack-eq = subst (λ m → StackWindows (amap hv) m (stackMem (floc fs))
                                         (lo hv) (frames-of (falloc fs)))
                     (sym mm)
                     (windows-store-gap (memory s) (stackMem (floc fs)) v (lo hv)
                        (current-frame (falloc fs)) (frame-slots (falloc fs))
                        (saved-frames (falloc fs)) gn (stack-eq corr)) }
  where
    a : ℕ
    a = frame-base (current-frame (falloc fs)) + slots (frame-slots (falloc fs))
    -- the gap cell is at or above the current frame's base, and the base is at
    -- or above the high-water mark — which is above the heap
    lo≤a : lo hv ≤ a
    lo≤a = ≤-trans (subst (lo hv ≤_) (sp-eq corr) (lo-le corr))
                   (m≤m+n (frame-base (current-frame (falloc fs)))
                          (slots (frame-slots (falloc fs))))
    front≤a : hfront hv ≤ a
    front≤a = ≤-trans (front-lo hv) lo≤a

-- THE PENDING RETURNS SURVIVE A WRITE THAT MISSES THEM (D093), in the two
-- shapes the emitted code produces. Both mirror `windows-above` — a return
-- cell is a frame's window END, hence at or above that frame's base, hence
-- above the floor the frame list threads.
--
-- (1) A change confined BELOW the floor — every heap store, since a live heap
-- cell is under `hfront ≤ lo ≤ %rsp`.
--
-- THE HEAD ROW TRAVELS BY ITS OWN PREMISE (2026-08-16). When `lk` is `just`
-- the head claim is the ARCH's, not a memory read, so the memory agreement
-- says nothing about it and a second premise carries it — guarded by the same
-- `fl ≤ a` the memory one uses, since the head cell is at or above the floor.
-- x86-64 discharges it from `ag` itself (its `LK` IS the memory read); riscv64
-- from a register-preservation fact, ignoring the address.
ret-agree-above : ∀ (xoff : ℕ → ℕ) {am : AddrMap} (mem mem' : Memory)
                    (LK LK' : ℕ → ℕ → Set) (lk : Maybe ℕ) (stk : StackMem FS)
                    (fl : ℕ) (fr : List (Frame × ℕ)) (rs : List ℕ)
                → (∀ (a : ℕ) → fl ≤ a → readMem mem' a ≡ readMem mem a)
                → (∀ (a v : ℕ) → fl ≤ a → LK a v → LK' a v)
                → StackWindows am mem stk fl fr
                → RetAddrs xoff mem LK lk fr rs → RetAddrs xoff mem' LK' lk fr rs
ret-agree-above xoff mem mem' LK LK' lk       stk fl fr             []       ag lag sw r = tt
ret-agree-above xoff mem mem' LK LK' lk       stk fl []             (x ∷ rs) ag lag sw ()
ret-agree-above xoff mem mem' LK LK' (just _) stk fl ((f , b) ∷ fr) (x ∷ rs) ag lag (bd , win , rest) (h , g , t) =
  lag (frame-base f + slots b) (xoff x) (≤-trans bd (m≤m+n (frame-base f) (slots b))) h
  , g
  , ret-agree-above xoff mem mem' LK LK' nothing stk (frame-base f + slots b) fr rs
      (λ a le → ag a (≤-trans (≤-trans bd (m≤m+n (frame-base f) (slots b))) le))
      (λ a v le → lag a v (≤-trans (≤-trans bd (m≤m+n (frame-base f) (slots b))) le))
      rest t
ret-agree-above xoff mem mem' LK LK' nothing  stk fl ((f , b) ∷ fr) (x ∷ rs) ag lag (bd , win , rest) (h , g , t) =
  trans (ag (frame-base f + slots b) (≤-trans bd (m≤m+n (frame-base f) (slots b)))) h
  , g
  , ret-agree-above xoff mem mem' LK LK' nothing stk (frame-base f + slots b) fr rs
      (λ a le → ag a (≤-trans (≤-trans bd (m≤m+n (frame-base f) (slots b))) le))
      (λ a v le → lag a v (≤-trans (≤-trans bd (m≤m+n (frame-base f) (slots b))) le))
      rest t

-- (2) A write INSIDE the current frame's window — every stack store, whose
-- slot is below the reservation (`slot < b`, the emitted-code discipline). The
-- head's own cell is the window END, strictly above the write; everything
-- older is above that end by the floor thread. This is the D086 gap doing its
-- job: the return address sits in it, and nothing the frame writes can reach.
ret-write-in-frame : ∀ (xoff : ℕ → ℕ) {am : AddrMap} (mem : Memory)
                       (LK LK' : ℕ → ℕ → Set) (lk : Maybe ℕ) (stk : StackMem FS)
                       (a : ℕ) (v : Word) (fl : ℕ) (f : Frame) (b : ℕ)
                       (fr : List (Frame × ℕ)) (rs : List ℕ)
                   → a < frame-base f + slots b
                   → (∀ (c w : ℕ) → a < c → LK c w → LK' c w)
                   → StackWindows am mem stk fl ((f , b) ∷ fr)
                   → RetAddrs xoff mem LK lk ((f , b) ∷ fr) rs
                   → RetAddrs xoff (writeMem mem a v) LK' lk ((f , b) ∷ fr) rs
ret-write-in-frame xoff mem LK LK' lk       stk a v fl f b fr []       lt lag sw r = tt
ret-write-in-frame xoff {am} mem LK LK' (just _) stk a v fl f b fr (x ∷ rs) lt lag (bd , win , rest) (h , g , t) =
  lag (frame-base f + slots b) (xoff x) lt h
  , g
  , ret-agree-above xoff mem (writeMem mem a v) LK LK' nothing stk (frame-base f + slots b) fr rs
      (λ c le → read-write-miss mem a v c (λ eq → <⇒≢ (<-transˡ lt le) (sym eq)))
      (λ c w le → lag c w (<-transˡ lt le))
      rest t
ret-write-in-frame xoff {am} mem LK LK' nothing stk a v fl f b fr (x ∷ rs) lt lag (bd , win , rest) (h , g , t) =
  trans (read-write-miss mem a v (frame-base f + slots b) (λ eq → <⇒≢ lt (sym eq))) h
  , g
  , ret-agree-above xoff mem (writeMem mem a v) LK LK' nothing stk (frame-base f + slots b) fr rs
      (λ c le → read-write-miss mem a v c (λ eq → <⇒≢ (<-transˡ lt le) (sym eq)))
      (λ c w le → lag c w (<-transˡ lt le))
      rest t

-- A CHANGE THE OLDER ROWS DO NOT SEE, with no claim transport to supply. Once
-- the head is `nothing` the arch's claim never appears again, so demanding
-- `LK → LK'` (as `ret-agree-above` must, for its head) would be asking for a
-- witness that is not available and not needed.
ret-agree-nothing : ∀ (xoff : ℕ → ℕ) {am : AddrMap} (mem mem' : Memory)
                      (LK LK' : ℕ → ℕ → Set) (stk : StackMem FS)
                      (fl : ℕ) (fr : List (Frame × ℕ)) (rs : List ℕ)
                  → (∀ (a : ℕ) → fl ≤ a → readMem mem' a ≡ readMem mem a)
                  → StackWindows am mem stk fl fr
                  → RetAddrs xoff mem LK nothing fr rs
                  → RetAddrs xoff mem' LK' nothing fr rs
ret-agree-nothing xoff mem mem' LK LK' stk fl fr             []       ag sw rr = tt
ret-agree-nothing xoff mem mem' LK LK' stk fl []             (x ∷ rs) ag sw ()
ret-agree-nothing xoff mem mem' LK LK' stk fl ((f , b) ∷ fr) (x ∷ rs) ag (bd , win , rest) (h , g , t) =
  trans (ag (frame-base f + slots b) (≤-trans bd (m≤m+n (frame-base f) (slots b)))) h
  , g
  , ret-agree-nothing xoff mem mem' LK LK' stk (frame-base f + slots b) fr rs
      (λ a le → ag a (≤-trans (≤-trans bd (m≤m+n (frame-base f) (slots b))) le))
      rest t

-- THE SPILL AS ONE STEP, which is what an arch whose head-row conversion is a
-- STORE needs. The two halves cannot be separated: BEFORE the store the head
-- cell holds nothing usable, AFTER it the `just` row is gone — so `ret-unlink`
-- alone (which keeps the memory fixed) cannot express it.
--
-- The older rows survive by `GapNext`, which the input's own head carries: the
-- next frame's base is one slot ABOVE the cell being written, so every older
-- return cell is too. This is the `RetAddrs` twin of `windows-store-gap`, and
-- the same D086 reservation is what makes both true.
ret-nil-frames : ∀ (xoff : ℕ → ℕ) (mem mem' : Memory) (LK LK' : ℕ → ℕ → Set)
                   (rs : List ℕ)
               → RetAddrs xoff mem LK nothing [] rs
               → RetAddrs xoff mem' LK' nothing [] rs
ret-nil-frames xoff mem mem' LK LK' []       r = tt
ret-nil-frames xoff mem mem' LK LK' (x ∷ rs) ()

ret-spill : ∀ (xoff : ℕ → ℕ) {am : AddrMap} (mem : Memory) (LK LK' : ℕ → ℕ → Set)
              (stk : StackMem FS) (r : ℕ) (f : Frame) (b : ℕ) (v : Word)
              (fr : List (Frame × ℕ)) (rs : List ℕ)
          → StackWindows am mem stk (frame-base f + slots b) fr
          → (∀ (w : ℕ) → LK (frame-base f + slots b) w → v ≡ w)
          → RetAddrs xoff mem LK (just r) ((f , b) ∷ fr) rs
          → RetAddrs xoff (writeMem mem (frame-base f + slots b) v) LK' nothing
                     ((f , b) ∷ fr) rs
ret-spill xoff mem LK LK' stk r f b v fr [] sw val rr = tt
ret-spill xoff mem LK LK' stk r f b v [] (x ∷ rs) sw val (h , g , t) =
  trans (read-write-hit mem (frame-base f + slots b) v) (cong just (val (xoff x) h))
  , g
  , ret-nil-frames xoff mem (writeMem mem (frame-base f + slots b) v) LK LK' rs t
ret-spill xoff {am} mem LK LK' stk r f b v ((f₀ , b₀) ∷ fr) (x ∷ rs) sw val (h , g , t) =
  trans (read-write-hit mem (frame-base f + slots b) v) (cong just (val (xoff x) h))
  , g
  , ret-agree-nothing xoff mem (writeMem mem (frame-base f + slots b) v) LK LK' stk
      (frame-base f₀) ((f₀ , b₀) ∷ fr) rs
      (λ c le → read-write-miss mem (frame-base f + slots b) v c
                  (λ eq → <⇒≢ (<-transˡ a<next le) (sym eq)))
      (windows-reanchor (frame-base f + slots b) (frame-base f₀) f₀ b₀ fr ≤-refl sw)
      t
  where
    a<next : frame-base f + slots b < frame-base f₀
    a<next = subst (frame-base f + slots b <_) g
                   (m<m+n (frame-base f + slots b) slot-size>0)
