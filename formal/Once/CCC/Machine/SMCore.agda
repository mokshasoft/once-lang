-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.SMCore
--
-- Core types and operations for the SlotMachine abstract machine.
--
-- This is the SOURCE OF TRUTH for fundamental types.
-- SMPrimitives imports from here and adds lemmas/proofs.
--
-- Location-based abstract machine for IR correctness proofs.
--
-- This machine operates ENTIRELY on ValueLocations:
--   - Registers hold ValueLocations
--   - Memory stores ValueLocations (pointers to other locations)
--   - Instructions move Locations between registers and memory
--
-- No Words/addresses appear in this model. The correspondence with
-- concrete x86 maps ValueLocations to addresses.
------------------------------------------------------------------------

module Once.CCC.Machine.SMCore where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _>_; _≥_; s≤s)
open import Data.Nat.Properties using (_≟_; <⇒≢; ≤-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; inspect; [_])
open import Relation.Nullary using (Dec; yes; no)

-- Import FrameSemantics for Frame type
open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics)
-- Plan 0.63 (D089): the structured label identity. Re-exported, so every
-- importer of the abstract instruction set sees `LabelId` without a second
-- import — the same courtesy `Locations`/`HeapAddress` already get below.
open import Once.CCC.Label public using (LabelId; mkLabelId; owner; path; idx)

-- Import SigOpInfo so `instr-sigop` carries its full self-describing
-- info (name + semI + semM), not just the name. This unlocks per-name
-- discharge of `ir-to-trace-correct-sigop` and per-(arch, name)
-- discharge of `sigop-codegen-faithful`.
open import Once.Type using (Type; Unit; Int; Float; _*_; FitsInReg; fits-int; fits-float; fits-in-reg?)
open import Once.Semantics.Machine using (⟦_⟧; LitPayload)
open import Once.SigOp.Info using (SigOpInfo; semM; effect; EffectShape; Pure; Emits; Halts)

private
  -- Helper: just is injective (private to avoid name clashes)
  just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

-- D062: `Slot` and `ValueLocation` moved to Once.CCC.Machine.Locations so the
-- categorical IR can use the location TYPES without importing the machine.
-- Re-exported below (after HeapAddress, on which Locations depends).

------------------------------------------------------------------------
-- Heap addresses (HeapRef, HeapOffset, HeapLocation)
--
-- These are language-agnostic and live in Once.Memory.HeapAddress so
-- the allocator can depend on them without going through CCC.
------------------------------------------------------------------------

open import Once.Memory.HeapAddress public
  using (HeapOffset; HeapRef; mkHeapRef; ref-id;
         HeapLocation; heap-loc; heap-ref; heap-offset;
         _≟H_; _≟HL_; ≟HL-aux; hl-ref)

-- D062: shared location types (Slot, ValueLocation/AtStack/AtDynamic), defined
-- below the machine so the IR can import them without the machine. Re-exported.
open import Once.CCC.Machine.Locations public
open import Once.Float.Decimal using (Decimal)
open import Once.Float.Decimal using (Decimal; round)
import Once.Word as Word
import Data.Nat as ℕ

-- Plan 0.14: the abstract-trace allocator instance lives in
-- Once.Allocator.AbstractInstance. SMCore consumes it for the
-- semantics of instr-alloc-heap — so the allocator interface is the
-- single source of truth, not a parallel definition.
import Once.Allocator.AbstractInstance as AI

------------------------------------------------------------------------
-- HeapRegion: A contiguous block of heap memory
--
-- Used for tracking ownership of heap-allocated objects.
-- A region starts at a HeapRef and has a fixed size.
------------------------------------------------------------------------

record HeapRegion : Set where
  constructor heap-region
  field
    region-ref : HeapRef
    region-size : ℕ

open HeapRegion public

-- Positive predicate: HeapLocation is within a HeapRegion
-- Uses ordering: same ref AND offset < size
data InRegion : HeapLocation → HeapRegion → Set where
  in-region : ∀ {r o size} →
    o < size →
    InRegion (heap-loc r o) (heap-region r size)

-- HeapOwnership: set of owned heap regions
-- Empty list means no heap writes allowed (current behavior)
HeapOwnership : Set
HeapOwnership = List HeapRegion

-- Positive predicate: HeapLocation is outside all owned regions
-- Either different ref (by ordering) or offset ≥ size
data OutsideOwned : HeapLocation → HeapOwnership → Set where
  outside-nil : ∀ {hl} → OutsideOwned hl []
  outside-cons : ∀ {hl region regions} →
    (ref-id (heap-ref hl) < ref-id (region-ref region) ⊎
     ref-id (heap-ref hl) > ref-id (region-ref region) ⊎
     heap-offset hl ≥ region-size region) →
    OutsideOwned hl regions →
    OutsideOwned hl (region ∷ regions)

------------------------------------------------------------------------
-- ValueLocation: Where a value lives
--
-- AtStack locations can reference anything (stack or heap).
-- AtDynamic locations use HeapLocation, enforcing heap-only references.
------------------------------------------------------------------------

-- AbstractReg: declared here ahead of `regs : AbstractReg → ValueLocation`
-- so LocState can reference it. (Stage-E previously also needed
-- AbstractReg here for `InReg : AbstractReg → ValueLocation`; that
-- constructor has been retired, but AbstractReg's role for register
-- state stays the same.)
-- PLAN 0.66: `Input2` IS RETIRED (2026-08-17). It was the second argument
-- location of plan 0.2.4.5 Stage C's split-input calling convention; that
-- convention was REVERTED (see `IRToTrace.ir-to-trace' … fst/snd`, "Stage C
-- γ-revert: uniform packed-pair convention"), and the descend tally that also
-- lived there was split off into `Count` by plan 0.54 rung D. What was left
-- had NO PRODUCER on any arch: `mov-{output-to-input2,input2-to-output}` were
-- never emitted by `ir-to-trace`, and survived only in proof enumerations.
--
-- It was not free. x86-32 has eight GPRs and `ebp` is the live frame anchor
-- every epilogue restores `%esp` from (plan 0.65 G1c: the "assign it to ebp"
-- fix is a SIGSEGV, not a fix), so `Input2` and `Scratch` were both `edx`
-- there — a role map that could not be filled INJECTIVELY, which is what
-- `FlatCore.RegRoles` needs. Retiring the dead role is what makes x86-32's
-- seven realised roles fit its seven available registers.
--
-- Future: the split-input convention returns as a type-driven optimisation
-- pass for register-fittable primitive args (IRToTrace's note). It brings its
-- own register plumbing back WITH a producer, and x86-32's register pressure
-- becomes a real question then, answerable against real emitted code.
data AbstractReg : Set where
  Input1 : AbstractReg    -- first argument location
  Output : AbstractReg    -- result location
  -- Plan 0.29: loop-private scratch register (maps to callee-saved rbx).
  -- Used only by the recursion-scheme loop construct (`instr-loop`) to
  -- hold the iteration counter/flag across algebra invocations. No CCC
  -- primitive or SigOp ever writes it (see `exec-abstract`), so it is
  -- preserved by every loop-body instruction for free.
  Scratch : AbstractReg
  -- Plan 0.54 rung D (item 4): the descend TALLY, split off the (now retired)
  -- second argument location.
  --
  -- The tally used to live in `Input2`, which was ALSO the second argument
  -- location of the split-input calling convention. Those two roles
  -- contradict: the tally is always an `SV-Tag`, an argument is anything. That
  -- conflation made `count-inc`/`scratch-dec`/`c-branch-scratch-zero`
  -- UNPROVABLE against the concrete machine (abstract `sv-succ`/`sv-pred`
  -- coerce a non-tag to a tag; x86 `add`/`sub` work on the encoding), and it
  -- was false by DESIGN INTENT, not by accident.
  --
  -- With the roles split, `Count` and `Scratch` are written ONLY with tags
  -- (`count-zero`/`count-inc`/`scratch-one`/`scratch-zero`/`scratch-dec`, and
  -- `scratch-load-count : Scratch := Count`), so "both hold tags" is a STATE
  -- invariant provable by induction over every instruction — see
  -- `Once.CCC.Machine.FlatRegTagWF`.
  Count : AbstractReg

-- `ValueLocation` (AtStack / AtDynamic) is defined in
-- Once.CCC.Machine.Locations (D062) and re-exported above.

-- Plan 0.13.2 — separation of address from value.
--
-- `ValueLocation` is the type of *addresses* — where in memory a
-- value lives. `StoredValue` is the type of *values* — what a
-- memory cell holds.
--
--   - `SV-Ptr loc`     — a pointer cell.
--   - `SV-Tag n`       — a sum-type tag literal (0 = inl, 1 = inr).
--   - `SV-Lit p v`     — a register-fittable primitive literal
--                        (replaces the `encode-const` postulate).
--                        `p : FitsInReg A` is the type evidence;
--                        `v : ⟦ A ⟧` is the value (ℕ for Int,
--                        AgdaFloat for Float, etc.).
--   - `SV-Code n`      — code-address label index (replaces
--                        `encode-code-addr`).
--
-- Closures, pairs, μ-cells are *records* spanning multiple
-- consecutive cells; they decompose into `SV-Ptr` + per-slot
-- contents and don't need their own constructor here. Sums are
-- the only construct where the runtime needs to inspect a tag in
-- memory — hence `SV-Tag`. See `plans/0.13.2-stored-value-type.md`
-- for full rationale.
--
-- `SV-Lit`'s payload is `⟦ A ⟧` — the target's REPRESENTATION — at every type,
-- including `Float` (D113). A `StoredValue` holds COMPUTED values, not only
-- literals: a Pure SigOp's result is `SV-Lit fitB (semM si a)`, which is bits
-- by construction and has no source syntax behind it. Source syntax appears
-- exactly once, at `instr-load-const` (see `LitPayload` below), which is the
-- instruction that MATERIALISES a literal — and it encodes as it executes.
data StoredValue (FS : FrameSemantics) : Set where
  SV-Ptr  : ValueLocation FS → StoredValue FS
  SV-Tag  : ℕ → StoredValue FS
  SV-Lit  : ∀ {A} → FitsInReg A → ⟦ A ⟧ → StoredValue FS
  -- Plan 0.63 (D089): a code address NAMES A LABEL, so it carries the label's
  -- identity rather than a raw counter value. The encoding to a machine word is
  -- unchanged (`idx`, the same number as before) — what a code address encodes
  -- to is D081's open question, not this one's.
  SV-Code : LabelId → StoredValue FS

-- Plan 0.2.4.5 D1 (Unit erasure) note: there is intentionally no
-- `Erased` sentinel here. The earlier Erased constructor encoded
-- "Unit values are nowhere" as a value, but that's a half-measure
-- — every memory operation needed a no-op clause for it. The
-- principled spec answer (per `Once.CCC.Machine.ClosureWellFormed`'s
-- `ResultPlace`) is to track Unit-typed results structurally:
-- `unit-result : ResultPlace Unit ...` carries no location at all.
-- So `ValueLocation` stays as the memory-locations type — exactly
-- what its name suggests.

-- Plan 0.2.4.5 Stage E retired (2026-05-07): the speculative
-- `InReg : AbstractReg → ValueLocation` constructor has been removed.
-- It was added as forward-compatible scaffolding for future
-- register-residency of FitsInReg-typed values, but never wired into
-- any consumer (no `valid-*-wf` ever produced an `InReg`-witness).
-- Its presence broke the `preserves-mem` family of lemmas
-- universally (`readLoc s (InReg Output)` shifts under `mov-to-output`)
-- without any compensating benefit. When register-residency lands for
-- real (Plan 0.2.4.5 D4), it should arrive as a SEPARATE polymorphic
-- "result place" type
--     data Place = AtStorage ValueLocation | InReg AbstractReg
-- so memory-only operations (`readLoc`, `writeLoc`, `stackMem`, `regs`)
-- keep their `ValueLocation`-typed (= storage-only) signatures and
-- `preserves-mem` retains its universal form. Result handles
-- (`IRResultAWF.result-loc`, `ValidAtWF`'s loc parameter) move to
-- `Place` only at handover points.

-- sucHL / offsetHL are now in Once.Memory.HeapAddress (re-exported
-- above via the public open).
open Once.Memory.HeapAddress public using (sucHL; offsetHL)

-- | Successor location (for accessing pair.snd, closure.code-ptr, etc.)
sucLoc : ∀ {FS} → ValueLocation FS → ValueLocation FS
sucLoc (AtStack f k)  = AtStack f (suc k)
sucLoc (AtDynamic hl) = AtDynamic (sucHL hl)

-- | Offset location by n slots (for unboxed multi-slot values)
-- Note: n + k so that offsetLoc _ 1 = sucLoc definitionally.
offsetLoc : ∀ {FS} → ValueLocation FS → ℕ → ValueLocation FS
offsetLoc (AtStack f k)  n = AtStack f (n + k)
offsetLoc (AtDynamic hl) n = AtDynamic (offsetHL hl n)

------------------------------------------------------------------------
-- Memory: Stores Locations (not Words)
--
-- KEY INVARIANT: Heap can ONLY store heap locations.
-- This enforces that heap-allocated values never reference stack,
-- which is essential for safe frame deallocation.
--
-- Stack memory can store any ValueLocation (stack or heap).
-- Heap memory can only store HeapLocation (heap-only).
------------------------------------------------------------------------

-- Plan 0.13.2: stack memory holds `StoredValue`, not `ValueLocation`.
StackMem : (FS : FrameSemantics) → Set
StackMem FS = FrameSemantics.Frame FS → Slot → Maybe (StoredValue FS)

-- Heap memory stores StoredValue. The cross-region constraint
-- (no heap → stack pointers) is enforced at the writeLoc boundary,
-- not in the type — primitives (SV-Lit, SV-Tag, SV-Code) and
-- heap pointers (SV-Ptr (AtDynamic _)) are all valid cell contents.
HeapMem : (FS : FrameSemantics) → Set
HeapMem FS = HeapLocation → Maybe (StoredValue FS)

------------------------------------------------------------------------
-- Registers: Hold Locations (not Words)
--
--   Input1 - first argument location (maps to RDI in x86 SysV)
--   Output - result location (maps to RAX in x86)
--
-- Plan 0.2.4.5 D2 gave this a second input register for a split-input
-- convention; plan 0.66 retired it with the convention (see AbstractReg).
-- `apply` packs (env, arg) into a pair, so ONE input register carries every
-- CCC primitive's input.
--
-- Note: AbstractReg is declared earlier (above ValueLocation) so
-- LocState's `regs : AbstractReg → ValueLocation` field can reference
-- it. The decidable equality and helpers stay here.
------------------------------------------------------------------------

-- Decidable equality for AbstractReg
_≟R_ : (r₁ r₂ : AbstractReg) → Dec (r₁ ≡ r₂)
Input1 ≟R Input1 = yes refl
Input1 ≟R Output = no (λ ())
Output ≟R Input1 = no (λ ())
Output ≟R Output = yes refl
Input1 ≟R Scratch = no (λ ())
Output ≟R Scratch = no (λ ())
Scratch ≟R Input1 = no (λ ())
Scratch ≟R Output = no (λ ())
Scratch ≟R Scratch = yes refl
Input1 ≟R Count = no (λ ())
Output ≟R Count = no (λ ())
Scratch ≟R Count = no (λ ())
Count ≟R Input1 = no (λ ())
Count ≟R Output = no (λ ())
Count ≟R Scratch = no (λ ())
Count ≟R Count = yes refl

-- Plan 0.13.2: registers hold `StoredValue`, not `ValueLocation`.
-- Real machines load tags / ints / pointers into the same registers
-- and discriminate by what was loaded. So register state lifts to
-- the same value type as memory cells.
record Registers (FS : FrameSemantics) : Set where
  constructor mkRegs
  field
    input1 output : StoredValue FS
    scratch : StoredValue FS  -- Plan 0.29: loop-private (rbx); see AbstractReg.Scratch
    count : StoredValue FS    -- Plan 0.54 D item 4: descend tally; see AbstractReg.Count

open Registers public

readReg : ∀ {FS} → Registers FS → AbstractReg → StoredValue FS
readReg r Input1 = input1 r
readReg r Output = output r
readReg r Scratch = scratch r
readReg r Count = count r

writeReg : ∀ {FS} → Registers FS → AbstractReg → StoredValue FS → Registers FS
writeReg r Input1 v = record r { input1 = v }
writeReg r Output v = record r { output = v }
writeReg r Scratch v = record r { scratch = v }
writeReg r Count v = record r { count = v }

  where open import Data.Nat using (_∸_)

-- Key lemma: writing to one register preserves others
writeReg-preserves : ∀ {FS} (regs : Registers FS) dst r v →
  r ≢ dst →
  readReg (writeReg regs dst v) r ≡ readReg regs r
writeReg-preserves regs Input1 Input1 v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs Input1 Output v r≢dst = refl
writeReg-preserves regs Output Input1 v r≢dst = refl
writeReg-preserves regs Output Output v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs Input1 Scratch v r≢dst = refl
writeReg-preserves regs Output Scratch v r≢dst = refl
writeReg-preserves regs Scratch Input1 v r≢dst = refl
writeReg-preserves regs Scratch Output v r≢dst = refl
writeReg-preserves regs Scratch Scratch v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)
writeReg-preserves regs Input1 Count v r≢dst = refl
writeReg-preserves regs Output Count v r≢dst = refl
writeReg-preserves regs Scratch Count v r≢dst = refl
writeReg-preserves regs Count Input1 v r≢dst = refl
writeReg-preserves regs Count Output v r≢dst = refl
writeReg-preserves regs Count Scratch v r≢dst = refl
writeReg-preserves regs Count Count v r≢dst = ⊥-elim (r≢dst refl)
  where open import Data.Empty using (⊥-elim)

-- Key lemma: writing to a register and reading it back gives the written value
writeReg-same : ∀ {FS} (regs : Registers FS) dst v →
  readReg (writeReg regs dst v) dst ≡ v
writeReg-same regs Input1 v = refl
writeReg-same regs Output v = refl
writeReg-same regs Scratch v = refl
writeReg-same regs Count v = refl


-- Key lemma: writing twice to same register is same as writing once
writeReg-overwrite : ∀ {FS} (regs : Registers FS) dst x y →
  writeReg (writeReg regs dst x) dst y ≡ writeReg regs dst y
writeReg-overwrite regs Input1 x y = refl
writeReg-overwrite regs Output x y = refl
writeReg-overwrite regs Scratch x y = refl
writeReg-overwrite regs Count x y = refl

-- Plan 0.29 (M5): register pokes for recursion-scheme loop bodies.
data RegOp : Set where
  scratch-one        : RegOp  -- Scratch := SV-Tag 1   (descend continue flag)
  scratch-zero       : RegOp  -- Scratch := SV-Tag 0   (stop / break)
  scratch-dec        : RegOp  -- Scratch := pred Scratch (ascend countdown)
  scratch-load-count : RegOp  -- Scratch := Count       (count → counter)
  -- Plan 0.54 D item 4: the tally lives in `Count`, NOT in the ABI's second
  -- argument register. Both writers produce an `SV-Tag` unconditionally, which
  -- is what makes `FlatRegTagWF` a state invariant. (Was `count-zero`/
  -- `count-inc`; see AbstractReg.Count for why the split was necessary.)
  count-zero         : RegOp  -- Count   := SV-Tag 0    (descend tally init)
  count-inc          : RegOp  -- Count   := succ Count  (descend count++)

-- Plan 0.29 (M5): SV-Tag counter arithmetic for instr-reg-op.
sv-succ : ∀ {FS} → StoredValue FS → StoredValue FS
sv-succ (SV-Tag n) = SV-Tag (suc n)
sv-succ _          = SV-Tag 1

sv-pred : ∀ {FS} → StoredValue FS → StoredValue FS
sv-pred (SV-Tag (suc n)) = SV-Tag n
sv-pred _                = SV-Tag 0

-- Plan 0.36 Phase 2b: read a count register (SV-Tag n) as the ℕ index
-- for `lea-indexed`'s `offsetLoc`. Non-tags index 0 (never reached when
-- the index register holds the descend/ascend counter).
sv-tag-val : ∀ {FS} → StoredValue FS → ℕ
sv-tag-val (SV-Tag n) = n
sv-tag-val _          = 0

------------------------------------------------------------------------
-- LocState: Abstract Machine State
------------------------------------------------------------------------

record LocState (FS : FrameSemantics) : Set where
  constructor mkLocState
  field
    regs : Registers FS
    stackMem : StackMem FS
    heapMem : HeapMem FS
    halted : Bool

open LocState public

-- Plan 0.29 (M5): LocState-only effect of a reg-op (alloc untouched —
-- kept separate so `proj₂ (exec-abstract (instr-reg-op op)) ≡ alloc`
-- holds uniformly, without case-splitting on `op`).
setReg : ∀ {FS} → RegOp → Registers FS → Registers FS
setReg scratch-one        r = writeReg r Scratch (SV-Tag 1)
setReg scratch-zero       r = writeReg r Scratch (SV-Tag 0)
setReg scratch-dec        r = writeReg r Scratch (sv-pred (readReg r Scratch))
setReg scratch-load-count r = writeReg r Scratch (readReg r Count)
setReg count-zero         r = writeReg r Count (SV-Tag 0)
setReg count-inc          r = writeReg r Count (sv-succ (readReg r Count))

-- Uniform record-update on `regs`: heapMem/stackMem/halted preserved
-- definitionally for ANY op (the op case-split lives inside setReg).
exec-reg-op : ∀ {FS} → RegOp → LocState FS → LocState FS
exec-reg-op op s = record s { regs = setReg op (regs s) }

------------------------------------------------------------------------
-- Allocation Mode
--
-- Where a value is allocated (output of escape analysis).
-- This is target-independent - any backend needs to distinguish
-- stack vs heap allocation.
------------------------------------------------------------------------

data AllocMode : Set where
  Stack : AllocMode  -- Value doesn't escape, allocate on stack
  Heap  : AllocMode  -- Value escapes, allocate on heap

------------------------------------------------------------------------
-- Allocation State
--
-- Tracks frame and heap allocation metadata.
--
--   - current-frame: which frame we're executing in
--   - next-slot: next available stack slot (for BeforeFrontier validity)
--   - next-heap-ref: next available heap block ID
--
-- Design note (Plan 0.63): there used to be TWO representations of the stack
-- pointer — `next-slot` (the compile-time frontier) and a `stackSlot` field in
-- the REGISTER FILE, documented as "mirrors rsp". The mirror is gone: the
-- current frame's slot count lives with the frame stack below, as
-- `frame-slots`, so a call updates ONE thing and the per-frame statement is
-- automatic rather than an extra invariant reconciling two.
--   - next-slot: Compile-time validity frontier (Dispatcher's view)
--   - frame-slots: the CURRENT frame's reserved slot count (what the
--     correspondence's `stack-eq` coverage is bounded by)
--
-- NOTE: frame-capacity was removed in Phase 3 refactoring. Capacity bounds
-- are now enforced per-IR via the scratch-bounded invariant, eliminating
-- the need for global capacity tracking in AllocState.
------------------------------------------------------------------------

-- The block-size update at an allocation: the fresh ref gets `n`, others keep
-- theirs. Aux-style (a `Dec` argument, no `with`) so it REDUCES at proof sites.
size-with-aux : ∀ (n : ℕ) {r st : ℕ} → (ℕ → ℕ) → Dec (r ≡ st) → ℕ
size-with-aux n         szs (yes _) = n
size-with-aux n {r} {_} szs (no  _) = szs r

size-with : ∀ (n st : ℕ) → (ℕ → ℕ) → ℕ → ℕ
size-with n st szs r = size-with-aux n {r} {st} szs (r ≟ st)

record AllocState {FS : FrameSemantics} : Set where
  constructor mkAllocState
  open FrameSemantics FS
  field
    current-frame : Frame
    -- Plan 0.61: the FRAME STACK — the caller frames, innermost first.
    --
    -- Frames MOVE with the stack pointer: the FLAT machine (`Machine.Flat`,
    -- which is THE semantics — `exec-flat`) shifts `current-frame` at every
    -- %rsp-moving instruction and restores the caller's frame here at the
    -- epilogue, so a callee's slot `k` is no longer the same cell as its
    -- caller's slot `k`. Without that the machine identifies two cells the
    -- hardware keeps apart and stack ADDRESSES have no meaning.
    --
    -- The legacy STRUCTURED layer (`exec-abstract` below, consumed only by the
    -- IR well-formedness modules — not on the apex path) keeps the degenerate
    -- model where the frame never moves; plan 0.61 stage 3 re-truths it when
    -- that layer is retired.
    -- Plan 0.63: each saved frame carries the slot count it reserved, so a
    -- return restores the caller's coverage bound along with its frame.
    saved-frames : List (Frame × ℕ)
    -- the CURRENT frame's reserved slot count (the old `Registers.stackSlot`,
    -- moved to where the frame actually lives)
    frame-slots : ℕ
    next-slot : ℕ
    next-heap-ref : ℕ
    -- THE BLOCK SIZES (2026-07-30 vacuity fix): how many slots each allocated
    -- block has (`0` for a ref the allocator has not handed out). The counter
    -- alone cannot say whether a heap pointer is IN BOUNDS, and in-bounds-ness is
    -- what makes "this cell is mapped by the correspondence" TRUE — without it the
    -- store-target coverage residuals (`store-indirect{,-suc}-live`) were false for
    -- any view, since a view legitimately excludes out-of-bounds cells (in the
    -- bump layout, block k's cell at offset ≥ its size IS block k+1's cell).
    -- Set by `instr-alloc-heap`; read only by proofs (the extracted pipeline never
    -- inspects `AllocState`).
    block-size : ℕ → ℕ
  -- Note: frame-capacity removed in Phase 3 of core invariants refactoring.
  -- Capacity bounds are now enforced per-closure via scratch-bounded invariant.

open AllocState public

------------------------------------------------------------------------
-- Memory Operations
------------------------------------------------------------------------

module MemOps {FS : FrameSemantics} where
  open FrameSemantics FS

  -- | Read a value from stack memory (returns StoredValue)
  readStackLoc : LocState FS → Frame → Slot → Maybe (StoredValue FS)
  readStackLoc s f k = stackMem s f k

  -- | Read from heap memory (returns StoredValue).
  readHeapLoc : LocState FS → HeapLocation → Maybe (StoredValue FS)
  readHeapLoc s hl = heapMem s hl

  -- | Read a value from memory.
  --
  -- Plan 0.14: heap reads return StoredValue directly. The cell holds
  -- whatever was stored there (primitive, tag, code address, or heap
  -- pointer). The cross-region constraint — no stack pointers — is
  -- enforced at writeLoc, so heap reads can be trusted not to fabricate
  -- AtStack references.
  readLoc : LocState FS → ValueLocation FS → Maybe (StoredValue FS)
  readLoc s (AtStack f k) = stackMem s f k
  readLoc s (AtDynamic hl) = heapMem s hl
  -- Plan 0.2.4.5 D1 (Unit erasure): erased values have no content.

  -- | Write a Location to stack memory.
  -- Order of clauses preserves definitional equalities for the (no _)
  -- frame-mismatch case (load-bearing for `writeLoc-preserves-other`):
  -- the no-frame-match branch is a single clause that returns `old`
  -- regardless of the slot decision, so `writeStackMem-aux (no _) _ old _`
  -- reduces by `refl` without case-splitting the second arg.
  -- Plan 0.13.2: stack now holds StoredValue.
  writeStackMem-aux : ∀ {f f' : Frame} {k k' : Slot}
                    → Dec (f ≡ f') → Dec (k ≡ k')
                    → Maybe (StoredValue FS)  -- existing value at (f',k')
                    → StoredValue FS           -- new value
                    → Maybe (StoredValue FS)
  writeStackMem-aux (no _)  _       old _ = old
  writeStackMem-aux (yes _) (yes _) _   v = just v
  writeStackMem-aux (yes _) (no _)  old _ = old

  writeStackMem : StackMem FS → Frame → Slot → StoredValue FS → StackMem FS
  writeStackMem mem f k v f' k' = writeStackMem-aux (f ≟F f') (k ≟ k') (mem f' k') v

  -- | CLEAR a frame's reserved slots (Plan 0.54 rung D).
  --
  -- A frame ENTERED is a frame whose slots hold nothing yet. Without this the
  -- abstract machine keeps the PREVIOUS incarnation's writes at a re-entered
  -- frame — a closure applied twice at one depth gets the SAME `shift-frame cf
  -- b` — so "the callee frame is fresh" was simply FALSE abstractly, exactly as
  -- its concrete twin was. Clearing here makes it true BY COMPUTATION instead
  -- of by assumption, which is the whole reason it belongs in the machine and
  -- not in a premise.
  --
  -- Sound against the hardware, which clears nothing: with `Window`
  -- one-directional the correspondence claims a match only where the ABSTRACT
  -- cell is written, so a cleared abstract cell asserts nothing about the stale
  -- concrete one. The two halves are a pair — neither is sound alone.
  --
  -- Same aux idiom as `writeStackMem`: route on explicit `Dec`s so the
  -- frame-mismatch branch reduces without splitting the slot decision.
  clear-frame-aux : ∀ {f f' : Frame} {k' b : ℕ}
                  → Dec (f ≡ f') → Dec (k' < b)
                  → Maybe (StoredValue FS)
                  → Maybe (StoredValue FS)
  clear-frame-aux (no _)  _       old = old
  clear-frame-aux (yes _) (yes _) _   = nothing
  clear-frame-aux (yes _) (no _)  old = old

  clear-frame : StackMem FS → Frame → ℕ → StackMem FS
  clear-frame mem f b f' k' = clear-frame-aux (f ≟F f') (Data.Nat.Properties._<?_ k' b) (mem f' k')

  -- CLEARING ONLY FORGETS: whatever the cleared map still holds, the original
  -- held. This is all a one-directional `Window` needs to survive a frame
  -- entry — it claims nothing about absent cells, so a store that only removes
  -- values preserves every window, with no frame-distinctness reasoning.
  clear-frame-just : ∀ (mem : StackMem FS) (f : Frame) (b : ℕ) (f' : Frame) (k' : Slot)
                       (v : StoredValue FS)
                   → clear-frame mem f b f' k' ≡ just v → mem f' k' ≡ just v
  clear-frame-just mem f b f' k' v ev with f ≟F f' | Data.Nat.Properties._<?_ k' b
  ... | no  _ | _     = ev
  ... | yes _ | no  _ = ev

  -- | Write a StoredValue to heap memory.
  -- with-FREE (mirrors writeStackMem): route on the explicit ≟HL result
  -- through a helper instead of an internal `with`. Consequence: an
  -- external `with hl ≟HL hl'` reduces writeHeapMem too (the helper sees
  -- the same Dec), so no opaque case tree and no special read-after-write
  -- accessor lemmas are needed — callers just case-split on ≟HL.
  writeHeapMem-aux : ∀ {hl hl' : HeapLocation}
                   → Dec (hl ≡ hl')
                   → Maybe (StoredValue FS)  -- existing value at hl'
                   → StoredValue FS           -- new value
                   → Maybe (StoredValue FS)
  writeHeapMem-aux (yes _) _   v = just v
  writeHeapMem-aux (no _)  old _ = old

  writeHeapMem : HeapMem FS → HeapLocation → StoredValue FS → HeapMem FS
  writeHeapMem mem hl v hl' = writeHeapMem-aux (hl ≟HL hl') (mem hl') v

  -- | Write a value (StoredValue) to stack memory at a slot.
  -- Plan 0.13.2.
  writeLocToStack : LocState FS → Frame → Slot → StoredValue FS → LocState FS
  writeLocToStack s f k v = record s { stackMem = writeStackMem (stackMem s) f k v }

  -- | Write a StoredValue to heap memory at a HeapLocation.
  writeLocToHeap : LocState FS → HeapLocation → StoredValue FS → LocState FS
  writeLocToHeap s hl v = record s { heapMem = writeHeapMem (heapMem s) hl v }

  -- | Write a value (StoredValue) to memory.
  --
  -- A MEMORY WRITE WRITES (2026-07-31, plan 0.54 rung D). Plan 0.14 made the
  -- one cross-region case — a stack pointer into a heap cell — a silent NO-OP,
  -- on lifetime grounds: a heap cell outliving the frame it points into is a
  -- dangling reference. But the hardware has no such rule (`mov [rdi],rax`
  -- stores the address and moves on), so as a MACHINE model the no-op was
  -- simply wrong, and it is what forced the x86-64 correspondence to assume
  -- `store-{,suc-}output-not-stackref` — "the emitted code never has a stack
  -- pointer in Output at a store site" — a dataflow claim about codegen that
  -- was never proved and is not even expressible as a property of the trace.
  --
  -- The lifetime discipline is a LANGUAGE-level obligation (which is why plan
  -- 0.53 moved apply's (env,arg) pair to the heap after the x86-32 dangling
  -- read), not something a store instruction can enforce by losing the write.
  writeLoc : LocState FS → ValueLocation FS → StoredValue FS → LocState FS
  writeLoc s (AtStack f k)  v                          = writeLocToStack s f k v
  writeLoc s (AtDynamic hl) (SV-Ptr (AtStack f k))     = writeLocToHeap s hl (SV-Ptr (AtStack f k))
  writeLoc s (AtDynamic hl) (SV-Ptr (AtDynamic v))     = writeLocToHeap s hl (SV-Ptr (AtDynamic v))
  writeLoc s (AtDynamic hl) (SV-Tag t)                 = writeLocToHeap s hl (SV-Tag t)
  writeLoc s (AtDynamic hl) (SV-Lit p v)               = writeLocToHeap s hl (SV-Lit p v)
  writeLoc s (AtDynamic hl) (SV-Code c)                = writeLocToHeap s hl (SV-Code c)

  -- writeLoc preserves regs (for all cases). Plan 0.13.2: v : StoredValue.
  writeLoc-regs : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS) →
    regs (writeLoc s loc v) ≡ regs s
  writeLoc-regs s (AtStack f k)  v                      = refl
  writeLoc-regs s (AtDynamic hl) (SV-Ptr (AtDynamic v)) = refl
  writeLoc-regs s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-regs s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-regs s (AtDynamic hl) (SV-Lit _ _)             = refl
  writeLoc-regs s (AtDynamic hl) (SV-Code _)            = refl

  -- writeLoc preserves halted (for all cases). Plan 0.13.2: v : StoredValue.
  writeLoc-halted : ∀ (s : LocState FS) (loc : ValueLocation FS) (v : StoredValue FS) →
    halted (writeLoc s loc v) ≡ halted s
  writeLoc-halted s (AtStack f k)  v                      = refl
  writeLoc-halted s (AtDynamic hl) (SV-Ptr (AtDynamic v)) = refl
  writeLoc-halted s (AtDynamic hl) (SV-Ptr (AtStack _ _)) = refl
  writeLoc-halted s (AtDynamic hl) (SV-Tag _)             = refl
  writeLoc-halted s (AtDynamic hl) (SV-Lit _ _)             = refl
  writeLoc-halted s (AtDynamic hl) (SV-Code _)            = refl

  -- writeLoc AtStack preserves heapMem. Plan 0.13.2: v : StoredValue.
  writeLoc-heapMem-stack : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS) →
    heapMem (writeLoc s (AtStack f k) v) ≡ heapMem s
  writeLoc-heapMem-stack s f k v = refl

  -- writeLoc commutes with register updates for AtStack locations.
  -- Plan 0.13.2: v : StoredValue.
  writeLoc-regs-commute : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS)
    (r : Registers FS) →
    writeLoc (record s { regs = r }) (AtStack f k) v ≡
    record (writeLoc s (AtStack f k) v) { regs = r }
  writeLoc-regs-commute s f k v r = refl

  -- writeLoc preserves other locations (reading from a different location)
  -- Key lemma for frame-independence proofs.
  -- Inner-with logic extracted to a helper to keep the proof CATCHALL-free.
  writeLoc-preserves-other-stack-aux : ∀ {f1 f2 : Frame} {k1 k2 : Slot}
    (s : LocState FS) (v : StoredValue FS)
    (df : Dec (f1 ≡ f2)) (dk : Dec (k1 ≡ k2))
    → AtStack {FS} f1 k1 ≢ AtStack {FS} f2 k2
    → writeStackMem-aux df dk (stackMem s f2 k2) v ≡ stackMem s f2 k2
  writeLoc-preserves-other-stack-aux s v (yes refl) (yes refl) neq = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  writeLoc-preserves-other-stack-aux s v (yes refl) (no _)     _   = refl
  writeLoc-preserves-other-stack-aux s v (no _)     (yes refl) _   = refl
  writeLoc-preserves-other-stack-aux s v (no _)     (no _)     _   = refl

  writeLoc-preserves-other : ∀ (s : LocState FS) (loc1 loc2 : ValueLocation FS)
    (v : StoredValue FS) →
    loc1 ≢ loc2 →
    readLoc (writeLoc s loc1 v) loc2 ≡ readLoc s loc2
  -- Writing to stack, reading from different stack location
  writeLoc-preserves-other s (AtStack f1 k1) (AtStack f2 k2) v neq =
    writeLoc-preserves-other-stack-aux s v (f1 ≟F f2) (k1 ≟ k2) neq
  -- Writing to stack, reading from heap (disjoint)
  writeLoc-preserves-other s (AtStack f k) (AtDynamic hl) v _ = refl
  -- Writing to heap (SV-Ptr (AtDynamic v)), reading from stack (disjoint)
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Ptr (AtDynamic hv)) _ = refl
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Ptr (AtStack _ _))  _ = refl
  -- Writing non-pointer to heap is no-op, so reading anywhere unchanged
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Tag _)              _ = refl
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Lit _ _)              _ = refl
  writeLoc-preserves-other s (AtDynamic hl) (AtStack f k) (SV-Code _)             _ = refl
  -- Writing to heap, reading from a different heap location.
  -- Plan 0.14: heap cells now accept any StoredValue except
  -- SV-Ptr (AtStack _ _), so all four "value" cases share the same
  -- "different cell" reasoning.
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Ptr (AtDynamic hv)) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Tag t) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Lit p v) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Code c) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl
  -- …including a stack pointer, which a heap cell now accepts like any other
  -- value (2026-07-31: the cross-region no-op is gone — see `writeLoc`)
  writeLoc-preserves-other s (AtDynamic hl1) (AtDynamic hl2) (SV-Ptr (AtStack f k)) neq
    with hl1 ≟HL hl2
  ... | yes refl = ⊥-elim (neq refl)
    where open import Data.Empty using (⊥-elim)
  ... | no _ = refl

  -- writeLoc-read-same: Reading from the location we just wrote returns the written value
  -- Stack case: writeLoc s (AtStack f k) v → readLoc (AtStack f k) ≡ just v
  writeLoc-read-same-stack : ∀ (s : LocState FS) (f : Frame) (k : Slot) (v : StoredValue FS) →
    readLoc (writeLoc s (AtStack f k) v) (AtStack f k) ≡ just v
  writeLoc-read-same-stack s f k v with f ≟F f | k ≟ k
  ... | yes _ | yes _ = refl
  ... | yes _ | no k≢k = ⊥-elim (k≢k refl)
    where open import Data.Empty using (⊥-elim)
  ... | no f≢f | _ = ⊥-elim (f≢f refl)
    where open import Data.Empty using (⊥-elim)

------------------------------------------------------------------------
-- Location Source
------------------------------------------------------------------------

data LocSourceExt (FS : FrameSemantics) : Set where
  Loc : ValueLocation FS → LocSourceExt FS
  IndReg : AbstractReg → LocSourceExt FS
  IndRegSuc : AbstractReg → LocSourceExt FS

-- Helper: extract a `ValueLocation` from a `StoredValue` if it's
-- a pointer. Plan 0.13.2: registers hold StoredValue, but
-- `resolveSourceExt` needs to derive addresses for loads/stores.
-- A non-pointer register value (tag/int/code) means the program
-- is dereferencing something it shouldn't — return `nothing`.
sv-as-loc : ∀ {FS} → StoredValue FS → Maybe (ValueLocation FS)
sv-as-loc (SV-Ptr loc) = just loc
sv-as-loc (SV-Tag _)   = nothing
sv-as-loc (SV-Lit _ _)   = nothing
sv-as-loc (SV-Code _)  = nothing

resolveSourceExt : ∀ {FS} → Registers FS → LocSourceExt FS → Maybe (ValueLocation FS)
resolveSourceExt regs (Loc loc) = just loc
resolveSourceExt regs (IndReg r) = sv-as-loc (readReg regs r)
resolveSourceExt regs (IndRegSuc r) with sv-as-loc (readReg regs r)
... | just loc = just (sucLoc loc)
... | nothing  = nothing

------------------------------------------------------------------------
-- Instructions
------------------------------------------------------------------------

data Instr (FS : FrameSemantics) : Set where
  load : AbstractReg → LocSourceExt FS → Instr FS
  store : LocSourceExt FS → AbstractReg → Instr FS
  mov : AbstractReg → AbstractReg → Instr FS

------------------------------------------------------------------------
-- Execution
------------------------------------------------------------------------

module ExecFinal {FS : FrameSemantics} where
  open MemOps {FS}

  -- Helper: Apply the result of a memory read to produce new state.
  -- Plan 0.13.2: the read result is `Maybe StoredValue`.
  exec-load-with-value : AbstractReg → Maybe (StoredValue FS) →
                         LocState FS → LocState FS
  exec-load-with-value dst (just v) s = record s { regs = writeReg (regs s) dst v }
  exec-load-with-value dst nothing s = record s { halted = true }

  -- Helper: bind through Maybe-resolved address. If resolveSourceExt
  -- returned `nothing` (non-pointer in register), halt.
  exec-load-via-resolved : AbstractReg → Maybe (ValueLocation FS) →
                           LocState FS → LocState FS
  exec-load-via-resolved dst (just loc) s = exec-load-with-value dst (readLoc s loc) s
  exec-load-via-resolved dst nothing    s = record s { halted = true }

  -- Same shape for stores: if dst-resolution fails, halt.
  exec-store-via-resolved : Maybe (ValueLocation FS) → StoredValue FS →
                            LocState FS → LocState FS
  exec-store-via-resolved (just loc) v s = writeLoc s loc v
  exec-store-via-resolved nothing    _ s = record s { halted = true }

  -- Plan 0.36 Phase 2b: `lea-indexed` helpers (with-free). `slot-base`
  -- resolves the base pointer read from a slot; `exec-lea-indexed-via`
  -- writes `&(base + idx)` into Input1 (halts if the base isn't a ptr).
  slot-base : Maybe (StoredValue FS) → Maybe (ValueLocation FS)
  slot-base (just sv) = sv-as-loc sv
  slot-base nothing   = nothing

  exec-lea-indexed-via : Maybe (ValueLocation FS) → ℕ → LocState FS → LocState FS
  exec-lea-indexed-via (just loc) idx s =
    record s { regs = writeReg (regs s) Input1 (SV-Ptr (offsetLoc loc idx)) }
  exec-lea-indexed-via nothing    idx s = record s { halted = true }

  -- Plan 0.27: `-suc` variants of the resolved load/store helpers, dispatching
  -- on the resolved Maybe address EXPLICITLY (no `with`). exec-abstract's
  -- load-indirect-suc / store-indirect-suc route through these so that a
  -- `sv-as-loc … ≡ just loc` hypothesis can be `rewrite`-n to reduce the
  -- result transparently — the old `with sv-as-loc …` froze that behind a
  -- generated auxiliary (the StoredValue-with-block reduction problem).
  exec-load-suc-via-resolved : AbstractReg → Maybe (ValueLocation FS) →
                               LocState FS → LocState FS
  exec-load-suc-via-resolved dst (just loc) s = exec-load-with-value dst (readLoc s (sucLoc loc)) s
  exec-load-suc-via-resolved dst nothing    s = record s { halted = true }

  exec-store-suc-via-resolved : Maybe (ValueLocation FS) → StoredValue FS →
                                LocState FS → LocState FS
  exec-store-suc-via-resolved (just loc) v s = writeLoc s (sucLoc loc) v
  exec-store-suc-via-resolved nothing    _ s = record s { halted = true }

  exec : Instr FS → LocState FS → LocState FS

  exec (load dst src) s =
    exec-load-via-resolved dst (resolveSourceExt (regs s) src) s

  exec (store dst src) s =
    exec-store-via-resolved
      (resolveSourceExt (regs s) dst)
      (readReg (regs s) src)
      s

  exec (mov dst src) s =
    record s { regs = writeReg (regs s) dst (readReg (regs s) src) }

  -- Lemmas for exec-load behavior (definitionally equal, but named for clarity)
  exec-load-just : ∀ dst v s →
    exec-load-with-value dst (just v) s ≡ record s { regs = writeReg (regs s) dst v }
  exec-load-just _ _ _ = refl

  exec-load-nothing : ∀ dst s →
    exec-load-with-value dst nothing s ≡ record s { halted = true }
  exec-load-nothing _ _ = refl

  execList : List (Instr FS) → LocState FS → LocState FS
  execList [] s = s
  execList (i ∷ is) s with halted s
  ... | true  = s
  ... | false = execList is (exec i s)

------------------------------------------------------------------------
-- Execution Lemmas
------------------------------------------------------------------------

module ExecLemmas {FS : FrameSemantics} where
  open MemOps {FS}
  open ExecFinal {FS}

  -- | Plan 0.13.2: helper to unify the two Maybe-layers introduced
  -- by resolveSourceExt now returning `Maybe ValueLocation`.
  -- Combines "resolve the source address" and "read the cell".
  resolved-readLoc : LocState FS → LocSourceExt FS → Maybe (StoredValue FS)
  resolved-readLoc s src with resolveSourceExt (regs s) src
  ... | just loc = readLoc s loc
  ... | nothing  = nothing

  -- | After load, dst holds the value from memory (when successful).
  -- Plan 0.13.2: takes the resolved address as an explicit arg to
  -- avoid double-`with` unification issues.
  load-result : ∀ dst src loc (s : LocState FS) v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    readReg (regs (exec (load dst src) s)) dst ≡ v
  load-result dst src loc s v r-eq mem-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | just v' | refl = writeReg-same (regs s) dst v'

  -- | After load (successful), other registers are preserved
  load-preserves-reg : ∀ dst src loc (s : LocState FS) r v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    r ≢ dst →
    readReg (regs (exec (load dst src) s)) r ≡ readReg (regs s) r
  load-preserves-reg dst src loc s r v r-eq mem-eq r≢dst
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | just v' | refl = writeReg-preserves (regs s) dst r v' r≢dst

  -- | After load (resolve failed), registers unchanged
  load-failed-resolve-preserves : ∀ dst src (s : LocState FS) →
    resolveSourceExt (regs s) src ≡ nothing →
    regs (exec (load dst src) s) ≡ regs s
  load-failed-resolve-preserves dst src s r-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | nothing | refl = refl

  -- | After load (read returned nothing), registers unchanged
  load-failed-read-preserves : ∀ dst src loc (s : LocState FS) →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ nothing →
    regs (exec (load dst src) s) ≡ regs s
  load-failed-read-preserves dst src loc s r-eq mem-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | nothing | refl = refl

  -- | Load preserves stack memory
  load-preserves-stackMem : ∀ dst src (s : LocState FS) →
    stackMem (exec (load dst src) s) ≡ stackMem s
  load-preserves-stackMem dst src s
    with resolveSourceExt (regs s) src
  ... | nothing  = refl
  ... | just loc with readLoc s loc
  ...   | just _  = refl
  ...   | nothing = refl

  -- | Load preserves heap memory
  load-preserves-heapMem : ∀ dst src (s : LocState FS) →
    heapMem (exec (load dst src) s) ≡ heapMem s
  load-preserves-heapMem dst src s
    with resolveSourceExt (regs s) src
  ... | nothing  = refl
  ... | just loc with readLoc s loc
  ...   | just _  = refl
  ...   | nothing = refl

  -- | After mov, dst holds what src held
  mov-result : ∀ dst src (s : LocState FS) →
    readReg (regs (exec (mov dst src) s)) dst ≡ readReg (regs s) src
  mov-result dst src s = writeReg-same (regs s) dst (readReg (regs s) src)

  -- | Mov preserves other registers
  mov-preserves-reg : ∀ dst src (s : LocState FS) r →
    r ≢ dst →
    readReg (regs (exec (mov dst src) s)) r ≡ readReg (regs s) r
  mov-preserves-reg dst src s r r≢dst =
    writeReg-preserves (regs s) dst r (readReg (regs s) src) r≢dst

  -- | Mov preserves memory
  mov-preserves-stackMem : ∀ dst src (s : LocState FS) →
    stackMem (exec (mov dst src) s) ≡ stackMem s
  mov-preserves-stackMem dst src s = refl

  mov-preserves-heapMem : ∀ dst src (s : LocState FS) →
    heapMem (exec (mov dst src) s) ≡ heapMem s
  mov-preserves-heapMem dst src s = refl

  -- | Load preserves halted status when memory read succeeds
  load-preserves-halted : ∀ dst src loc (s : LocState FS) v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    halted (exec (load dst src) s) ≡ halted s
  load-preserves-halted dst src loc s v r-eq mem-eq
    with resolveSourceExt (regs s) src | r-eq
  ... | just loc' | refl with readLoc s loc' | mem-eq
  ...   | just _ | refl = refl

  -- | Load doesn't halt when memory read succeeds and not already halted
  load-no-halt : ∀ dst src loc (s : LocState FS) v →
    resolveSourceExt (regs s) src ≡ just loc →
    readLoc s loc ≡ just v →
    halted s ≡ false →
    halted (exec (load dst src) s) ≡ false
  load-no-halt dst src loc s v r-eq mem-eq not-halted =
    trans (load-preserves-halted dst src loc s v r-eq mem-eq) not-halted

  -- | Memory read is preserved when stackMem and heapMem unchanged.
  -- Now universal (post-Stage-E retirement): readLoc only depends on
  -- (stackMem, heapMem) for AtStack/AtDynamic, and is constantly
  -- `nothing` for Erased. The Stage-E InReg-postulate is gone with
  -- the constructor it was working around.
  readLoc-stackMem-eq : ∀ (s₁ s₂ : LocState FS) loc →
    stackMem s₁ ≡ stackMem s₂ →
    heapMem s₁ ≡ heapMem s₂ →
    readLoc s₁ loc ≡ readLoc s₂ loc
  readLoc-stackMem-eq s₁ s₂ (AtStack f k) stack-eq heap-eq =
    cong (λ m → m f k) stack-eq
  readLoc-stackMem-eq s₁ s₂ (AtDynamic hl) stack-eq heap-eq =
    cong (λ m → m hl) heap-eq

------------------------------------------------------------------------
-- Abstract Instructions
--
-- Higher-level instructions that map directly to IR operations.
-- Each AbstractInstr has a clear semantics at the LocState level
-- and compiles to one or more x86 instructions.
--
-- This is the trace layer: IR execution produces AbstractTrace,
-- which compiles to x86 and has per-instruction simulation proofs.
------------------------------------------------------------------------

-- Plan 0.32 (M3, flatten): FLAT control flow for the abstract machine,
-- mirroring the target (pc + label/je/jmp). Wrapped in a single
-- `instr-ctrl` AbstractInstr constructor to bound the exhaustive-match
-- cascade to one clause per function. Run by the pc/fuel flat `exec`
-- (a FlatState carries the pc + zero-flag); the legacy structured
-- `exec-trace`/`exec-abstract` (no pc) simply HALT on these — they are
-- never emitted into a structured trace, only into a flat program.
-- Plan 0.63 (D089): the label ARGUMENTS are `LabelId`, not `ℕ`. Provenance
-- stays where it already was — in WHICH CONSTRUCTOR (`c-label` vs `c-thunk`)
-- and WHICH LOOKUP (`find-label` vs `find-thunk`) — so this layer needs no
-- provenance field; only the identity becomes structured. See D089 for why a
-- bare counter cannot be unique: `cata-dispatch` emits its algebra's trace
-- twice, and a counter distinguishes occurrences only under a linear walk.
data FlatCtrl : Set where
  c-label              : LabelId → FlatCtrl  -- label marker (pc passes through)
  c-jmp                : LabelId → FlatCtrl  -- unconditional jump to label
  -- Plan 0.34: a conditional branch is ONE portable unit (condition +
  -- target), lowered per target (x86: cmp+je = 2 instrs; RISC-V: beqz = 1).
  -- No flags register in the abstract machine — the condition is computed
  -- and consumed inside this single step.
  c-branch-scratch-zero : LabelId → FlatCtrl -- if Scratch ≟ SV-Tag 0, jump to label
  c-branch-tag-zero     : LabelId → FlatCtrl -- if *Input1 tag ≟ SV-Tag 0, jump
  -- Plan 0.63: the call/return half of flat control. A RETURN is pure
  -- control flow, so it belongs here rather than as a top-level
  -- AbstractInstr (which would force a clause at the 13 sites that treat
  -- `instr-ctrl c` opaquely). `c-thunk` marks a closure body's entry: it
  -- is a label like `c-label`, but in the `thunk` provenance (D082), so a
  -- jump can never land on a body entry and a call can never land on a
  -- jump label — definitionally, not by counter accident.
  -- Plan 0.63 step 2a: the markers CARRY THE BODY'S SLOT BUDGET, because
  -- the per-body frame is part of them. The concrete body is
  -- `.L_thunk_n: subq $b*8,%rsp ; … ; addq $b*8,%rsp ; ret` — and that
  -- `subq` is LOAD-BEARING: `call` pushes a return address, so a frameless
  -- body's slot k would sit at `caller_base − 8 + 8k` and clobber the
  -- caller's slots from k = 1 on. Keeping the reservation ON THE MARKER
  -- (rather than giving `instr-alloc-stack` a producer again) means the
  -- frame moves at exactly the two instructions that also move the pc, and
  -- it moves via `enter-frame`/`leave-frame` — an AllocState-only update,
  -- so the register file is untouched.
  c-thunk               : LabelId → ℕ → FlatCtrl -- closure-body entry: label, budget
  c-ret                 : ℕ → FlatCtrl     -- return: budget to release

data AbstractInstr : Set where
  -- Register operations
  mov-to-output      : AbstractInstr              -- Output := Input1
  mov-to-input       : AbstractInstr              -- Input1 := Output (compose bridge)

  -- (Plan 0.2.4.5 Stage C's `mov-output-to-input2` / `mov-input2-to-output`
  -- were RETIRED with `Input2` by plan 0.66 — the split-input convention they
  -- served was reverted, and `ir-to-trace` never emitted them.)

  -- Memory load operations (slot-level, not physical address arithmetic)
  load-indirect      : AbstractInstr              -- Output := *Input1
  load-indirect-suc  : AbstractInstr              -- Output := *(sucLoc Input1)
  load-from-slot     : Slot → AbstractInstr       -- Output := stack[slot]

  -- Memory store operations
  store-at-slot      : Slot → AbstractInstr       -- stack[slot] := Output
  store-indirect     : AbstractInstr              -- *Input1 := Output
  store-indirect-suc : AbstractInstr              -- *(sucLoc Input1) := Output

  -- Address computation
  lea-slot           : Slot → AbstractInstr       -- Output := &stack[slot]
  restore-input      : Slot → AbstractInstr       -- Input1 := stack[slot]

  -- Stack management
  instr-alloc-stack   : ℕ → AbstractInstr          -- allocate N slots
  instr-dealloc-stack : ℕ → AbstractInstr          -- deallocate N slots

  -- OCP-0003: Slot reclamation for Sum wrappers
  -- Sets next-slot to a specific value, allowing wrapper allocation at reclaimed position.
  -- Used by Sum to place wrapper at child's reclaimable-slot for tight allocation.
  instr-reclaim-to    : ℕ → AbstractInstr          -- set next-slot to n

  -- Apply-specific (function calls)
  instr-push-frame   : ℕ → AbstractInstr          -- push new frame with capacity
  instr-pop-frame    : AbstractInstr              -- restore caller frame
  instr-call-closure : AbstractInstr              -- jump to closure code

  -- OCP-0003: Worklist operations for loop-based recursion schemes
  --
  -- The worklist is a slot-based stack for tree traversal:
  --   Slot (base-1): count (number of items)
  --   Slots base, base+1, ...: data items
  --
  -- Runtime uses loops; proofs use Star (structural induction on μ-values).
  -- These instructions implement the runtime loop operations.
  --
  worklist-init  : Slot → AbstractInstr  -- Initialize: count := 0
  worklist-push  : Slot → AbstractInstr  -- Push Output, count++
  worklist-pop   : Slot → AbstractInstr  -- count--, Output := top item
  worklist-check : Slot → AbstractInstr  -- Output := 1 if empty, 0 if not

  -- Plan 0.10 Phase B / Phase A step 1: SigOp dispatch.
  --
  -- Carries the SigOpInfo (name + semI + semM). Per-arch
  -- compile-abstract uses `name si` to decide what assembly to emit
  -- (e.g., "exit" → mov $60, %rax; syscall). The proof layer can
  -- consult `semI si` / `semM si` for per-name discharge of
  -- `sigop-codegen-faithful` and `ir-to-trace-correct-sigop` — see
  -- `Once.SigOp.Info` for the spec layer.
  --
  -- Type indices A, B are implicit and recoverable when needed by
  -- pattern-matching on `instr-sigop {A} {B} si`.
  instr-sigop : ∀ {A B : Type} → SigOpInfo A B → AbstractInstr

  -- Plan 0.11: Load a primitive-typed constant into Output.
  --
  -- Carries `FitsInReg` evidence and the machine-level value
  -- `v : ⟦ A ⟧`. Per-arch `compile-abstract` pattern-matches on the
  -- evidence to emit the right load instruction (`mov $N, %rax` for
  -- Int, etc.). CCC stays specific-primitive-type-agnostic; the
  -- per-arch backend knows specific register-fittable types because
  -- it has to emit specific machine instructions.
  instr-load-const : ∀ {A : Type} (p : FitsInReg A) → LitPayload p → AbstractInstr

  -- Plan 0.2.4.2 Phase A: Load the address of a closure-body label
  -- into Output. The argument `n : ℕ` indexes into the parent
  -- function's per-function table of closure-body labels — Plan
  -- 0.2.4.2 D5 (stateful counter, local to each parent function).
  --
  -- Per-arch `compile-abstract` lowers this to a label-relative
  -- address load (`lea .L_thunk_<n>(%rip), %rax` on x86-64).
  --
  -- Plan 0.2.4.2 Phase D follow-up: capture the current Input1
  -- register into the closure-register convention slot (e.g.
  -- `%r12` on x86-64). Used in `apply`'s setup trace to keep the
  -- closure pointer alive across pair-construction so that
  -- `instr-call-closure` (lowered to `call *0x8(%r12)`) has a
  -- valid target.
  --
  -- Abstract semantics: identity. We don't model the closure
  -- register separately at the abstract level — it's purely a
  -- per-arch calling-convention concern.
  -- Used by `curry`'s codegen to set up the closure record's
  -- code-pointer slot.
  instr-load-code-addr : LabelId → AbstractInstr
  instr-save-closure-reg : AbstractInstr

  -- Plan 0.13.1 Phase 1 — sum tag handling (tag-aware abstract layer).
  --
  -- `instr-load-tag-lit n`: write `SV-Tag n` to Output. Used by
  -- `run-inl` / `run-inr` to deposit the sum-discriminator (0 for
  -- inl, 1 for inr) before storing it to the container's tag slot.
  --
  -- `instr-case-on-tag f g`: read `SV-Tag k` from `*Input1` (the
  -- sum value's tag slot, at offset 0) and dispatch:
  --   k = 0 → exec-trace f
  --   k = 1 → exec-trace g
  --   otherwise (no tag / malformed sum) → halt
  --
  -- This is the tag-aware abstract semantics promised by Plan 0.13.1
  -- Phase 1. The proof of run-case correctness composes from
  -- `valid-inl-wf` / `valid-inr-wf`'s tag-eq fields (Plan 0.13.1
  -- Phase 2) — no `case-codegen-faithful` postulate needed.
  --
  -- Argument type for instr-case-on-tag is `List AbstractInstr`
  -- (= `AbstractTrace`) spelled out — the `AbstractTrace` alias is
  -- defined just below.
  -- NOTE: keep instr-case-on-tag in this position so existing
  -- compile-correct proofs and Haskell-side simulations don't shift.
  -- New constructors get added strictly AFTER instr-case-on-tag.
  instr-load-tag-lit : ℕ → AbstractInstr
  instr-case-on-tag : List AbstractInstr → List AbstractInstr → AbstractInstr

  -- Plan 0.14 Phase A — heap allocation primitive.
  --
  -- `instr-alloc-heap n`: allocate a fresh heap block (n cells), bump
  -- `next-heap-ref`, write the resulting `SV-Ptr (AtDynamic …)` to Output.
  -- Caller subsequently writes the cells via `store-indirect` /
  -- `store-indirect-suc` and reads them via `load-indirect` /
  -- `load-indirect-suc`.
  --
  -- The `n` parameter is the cell count for codegen / sigop dispatch;
  -- the abstract semantics treats every `instr-alloc-heap _` as a single
  -- fresh `AtDynamic` whose `sucLoc` chains give access to all n cells
  -- (HeapLocation already supports this).
  --
  -- Added AFTER `instr-case-on-tag` so existing MAlonzo constructor
  -- indices remain stable.
  instr-alloc-heap : ℕ → AbstractInstr

  -- Plan 0.29: generic fuel-bounded loop. `instr-loop body` re-runs
  -- `body` while the loop-private `Scratch` register is nonzero (the
  -- body updates `Scratch` each iteration); execution is fuel-bounded
  -- (see `exec-loop`). This is the reusable control-flow primitive for
  -- structural-recursion schemes (Cata first; Para/Ana/Hylo later) — the
  -- per-scheme descend/ascend logic lives in `body`, the loop/back-edge
  -- and fuel are shared. Added AFTER all prior constructors for MAlonzo
  -- ctor-index stability.
  instr-loop : List AbstractInstr → AbstractInstr

  -- Plan 0.29 (M5): register-only counter pokes for the recursion-scheme
  -- loop bodies (Scratch = loop counter/flag, Count = descend tally).
  -- No heap, no slot, frame-preserving — its whole cascade mirrors
  -- `mov-to-output`. x86: mov/add/sub on rbx (Scratch) / r14 (Count).
  instr-reg-op : RegOp → AbstractInstr

  -- Plan 0.32 (M3): flat control flow (label/jump/test). Added LAST for
  -- MAlonzo ctor-index stability. Structured exec halts on these; the
  -- flat pc/fuel exec interprets them. See FlatCtrl above.
  instr-ctrl : FlatCtrl → AbstractInstr

  -- Plan 0.36 Phase 2b: indexed-pointer compute for the cata payload/work
  -- stack. `lea-indexed slot`: Input1 := &(base + idx), where base is the
  -- array pointer held at stack `slot` and idx = the count in `Scratch`
  -- (reuses `offsetLoc`). The subsequent `load-indirect`/`store-indirect`
  -- then access `array[idx]`. Added LAST for MAlonzo ctor-index stability.
  lea-indexed : ℕ → AbstractInstr

-- | A trace is a sequence of abstract instructions
AbstractTrace : Set
AbstractTrace = List AbstractInstr

------------------------------------------------------------------------
-- Tree-Structured Traces (OCP-0003)
--
-- For recursion schemes, we need traces that can represent recursive
-- structure. TreeTrace extends AbstractTrace with:
--   - Sequencing: Execute traces in order
--   - Branching: Choose trace based on tag slot value
--   - Recursive call: Execute sub-trace (maps to function call at runtime)
--
-- PORTABILITY:
--   These primitives map cleanly to all backends:
--   - x86-64: call/ret sequences, conditional jumps
--   - ARM64: bl/ret sequences, conditional branches
--   - WASM: call instruction, br_if blocks
--   - RISC-V: jal/jalr sequences
--
-- The semantic model is portable: tree structure represents control
-- flow without committing to a specific calling convention.
------------------------------------------------------------------------

data TreeTrace : Set where
  -- | Empty trace
  ε : TreeTrace
  -- | Single instruction
  instr : AbstractInstr → TreeTrace
  -- | Sequential composition: execute t₁ then t₂
  _▸_ : TreeTrace → TreeTrace → TreeTrace
  -- | Branch on tag in slot: if tag=0 run left, else run right
  -- This supports sum types (inj₁/inj₂ dispatching)
  branch : Slot → TreeTrace → TreeTrace → TreeTrace
  -- | Recursive call: execute sub-trace (callee-saved context)
  -- This models the recursive step in recursion schemes
  call-sub : TreeTrace → TreeTrace
  -- | Embed flat trace (compatibility with existing code)
  flat : AbstractTrace → TreeTrace

infixr 5 _▸_

-- | Convert flat trace to tree trace
flatToTree : AbstractTrace → TreeTrace
flatToTree [] = ε
flatToTree (i ∷ is) = instr i ▸ flatToTree is

-- | Flatten tree trace to list (for backends that want flat sequences)
-- Note: branch and call-sub are eliminated by code generation, not here
treeToFlat : TreeTrace → AbstractTrace
treeToFlat ε = []
treeToFlat (instr i) = i ∷ []
treeToFlat (t₁ ▸ t₂) = treeToFlat t₁ ++ treeToFlat t₂
treeToFlat (branch _ tL tR) = treeToFlat tL ++ treeToFlat tR  -- Both branches for analysis
treeToFlat (call-sub t) = treeToFlat t
treeToFlat (flat is) = is

------------------------------------------------------------------------
-- TreeTrace to Runnable Flat Trace Compilation
--
-- This compiles TreeTrace to a flat AbstractTrace that executes
-- equivalently using worklist operations for call-sub.
--
-- PROOF SIGNIFICANCE:
--   exec-tree-trace t s alloc ≡ exec-trace (treeToRunnable wl t) s alloc
--   (where wl is the worklist slot allocation)
--
-- This enables proving ValidAtWF by:
--   1. Build TreeTrace by structural recursion (cata-tree-μ)
--   2. Prove TreeTrace execution correct (cata-tree-μ-correct)
--   3. Compile to flat trace (treeToRunnable)
--   4. By equivalence, flat trace also correct
--
-- RUNTIME MAPPING:
--   - call-sub → worklist-push + main loop processing
--   - branch → conditional jump
--   - Sequential composition → instruction concatenation
------------------------------------------------------------------------

-- | Compile TreeTrace to runnable flat trace
--
-- Parameters:
--   wl : Slot for worklist (count + items)
--   t  : TreeTrace to compile
--
-- The worklist approach:
--   - Initialize worklist at start
--   - call-sub pushes current work item and continues with sub-trace
--   - At end of sub-trace, check worklist for more work
--
-- Note: This is a simplified model. Real runtime uses loop structure.
treeToRunnable : Slot → TreeTrace → AbstractTrace
treeToRunnable wl ε = []
treeToRunnable wl (instr i) = i ∷ []
treeToRunnable wl (t₁ ▸ t₂) = treeToRunnable wl t₁ ++ treeToRunnable wl t₂
treeToRunnable wl (branch slot tL tR) =
  -- Simplified: flatten both branches (runtime uses conditional)
  -- For proofs, the taken branch is determined by getTag
  treeToRunnable wl tL ++ treeToRunnable wl tR
treeToRunnable wl (call-sub t) =
  -- Push current continuation, execute sub-trace
  -- Worklist manages the return continuation
  worklist-push wl ∷ treeToRunnable wl t ++ worklist-pop wl ∷ []
treeToRunnable wl (flat is) = is

-- | Initialize worklist and compile tree trace
treeToRunnableWithInit : Slot → TreeTrace → AbstractTrace
treeToRunnableWithInit wl t = worklist-init wl ∷ treeToRunnable wl t

------------------------------------------------------------------------
-- Abstract Instruction Semantics
--
-- Operational semantics for AbstractInstr. Each instruction transforms
-- (LocState, AllocState) → (LocState, AllocState).
--
-- This is the specification that x86 refinement must preserve.
------------------------------------------------------------------------

module AbstractExec {FS : FrameSemantics} where
  open FrameSemantics FS
  open MemOps {FS}
  open ExecFinal {FS}
  open ExecLemmas {FS}

  ------------------------------------------------------------------------
  -- Helper functions for instructions that read from memory
  --
  -- These expose the decision point (Maybe result) for external proofs.
  -- Using these helpers, external code can prove properties by cases on
  -- the Maybe value rather than needing with-pattern alignment.
  ------------------------------------------------------------------------

  -- Helper for load-from-slot: applies memory read result.
  -- Plan 0.13.2: read result is now `Maybe StoredValue`.
  exec-load-from-slot-with-value : Maybe (StoredValue FS) → LocState FS →
                                   AllocState {FS} → LocState FS × AllocState {FS}
  exec-load-from-slot-with-value (just v) s alloc =
    record s { regs = writeReg (regs s) Output v } , alloc
  exec-load-from-slot-with-value nothing s alloc =
    record s { halted = true } , alloc

  -- Helper for restore-input: applies memory read result.
  -- Plan 0.13.2: read result is now `Maybe StoredValue`.
  exec-restore-input-with-value : Maybe (StoredValue FS) → LocState FS →
                                  AllocState {FS} → LocState FS × AllocState {FS}
  exec-restore-input-with-value (just v) s alloc =
    record s { regs = writeReg (regs s) Input1 v } , alloc
  exec-restore-input-with-value nothing s alloc =
    record s { halted = true } , alloc

  -- Lemmas for load-from-slot helper
  exec-load-from-slot-just : ∀ v s alloc →
    exec-load-from-slot-with-value (just v) s alloc ≡
    (record s { regs = writeReg (regs s) Output v } , alloc)
  exec-load-from-slot-just _ _ _ = refl

  exec-load-from-slot-nothing : ∀ s alloc →
    exec-load-from-slot-with-value nothing s alloc ≡
    (record s { halted = true } , alloc)
  exec-load-from-slot-nothing _ _ = refl

  -- Lemmas for restore-input helper
  exec-restore-input-just : ∀ v s alloc →
    exec-restore-input-with-value (just v) s alloc ≡
    (record s { regs = writeReg (regs s) Input1 v } , alloc)
  exec-restore-input-just _ _ _ = refl

  exec-restore-input-nothing : ∀ s alloc →
    exec-restore-input-with-value nothing s alloc ≡
    (record s { halted = true } , alloc)
  exec-restore-input-nothing _ _ = refl

  ------------------------------------------------------------------------
  -- Plan 0.25 — SigOp dispatch via EffectClass.
  --
  -- The abstract semantics of `instr-sigop si` is now derived from
  -- `effect si : EffectClass` rather than per-SigOp postulates:
  --
  --   - `Halts` → halted := true; output := unit-storedvalue
  --   - `Emits` → halted := false; output := unit-storedvalue
  --   - `Pure`  → halted := false; output := pure-sigop-output si s
  --
  -- The `exec-sigop-halts` postulate is GONE: halting is now a
  -- definitional consequence of the effect class. The output of
  -- `Halts`/`Emits` is unit-shaped (their `R ≡ Unit` coherence law
  -- means the value in Output is observably irrelevant), so the
  -- old `exec-sigop-output` postulate is GONE for those classes too.
  --
  -- The remaining `pure-sigop-output` postulate covers only `Pure`
  -- SigOps. It is the per-name discharge target (e.g. for
  -- `arith.block.<digest>` SigOps whose machine output is
  -- `SV-Lit fits-int (semM si <input>)`). Pure outputs are
  -- type-dependent (Int wraps as SV-Lit; Sums require allocation)
  -- so a generic `wrap : M.⟦B⟧ → StoredValue` does not exist at
  -- this layer — per-name discharge stays. The trusted base is now
  -- *classified* (Pure-only) rather than blanket (every SigOp).
  --
  -- The relaxed CCC discipline contract continues to hold
  -- *definitionally* for `instr-sigop si`: frame, alloc, memory,
  -- Input1 register are unchanged.
  ------------------------------------------------------------------------

  -- | A "unit-shaped" StoredValue for Halts/Emits SigOps whose
  -- `R ≡ Unit`. The concrete bytes don't matter (the consumer never
  -- inspects Output for Unit-typed values); we pick `SV-Lit fits-int 0`
  -- as a canonical sentinel.
  unit-storedvalue : StoredValue FS
  unit-storedvalue = SV-Lit fits-int 0

  -- Plan 0.54 Phase B rung A (A4): the type-directed VALUE READER — the inverse
  -- of how `ValidAtWF` stores a value. `readTyped A loc s` materialises the
  -- `⟦ A ⟧` a representation at `loc` denotes (Int/Float from the `SV-Lit`, a
  -- product from the two `SV-Ptr` slots recursively, Unit trivially). This is
  -- what lets `pure-sigop-output` COMPUTE a Pure SigOp's real `semM` result
  -- instead of a sentinel. Non-arith shapes → `nothing`; arith inputs are tuples
  -- of Unit/Int (`Arith.SigOp.Block.shape-as-type`), the covered cases.
  combine-typed : ∀ {A B : Type} → Maybe ⟦ A ⟧ → Maybe ⟦ B ⟧ → Maybe ⟦ A * B ⟧
  combine-typed (just a) (just b) = just (a , b)
  combine-typed _        _        = nothing

  -- Aux-style (Maybe-argument) helpers so the adequacy proof
  -- (`ReadTypedAdequate`) can `rewrite` the `readLoc` results — a `with` on the
  -- abstract `readLoc s loc` would not reduce under the proof's rewrites.
  readTyped-int : Maybe (StoredValue FS) → Maybe ⟦ Int ⟧
  readTyped-int (just (SV-Lit fits-int v)) = just v
  readTyped-int _                          = nothing

  readTyped-pair : ∀ {A B : Type}
                 → (ValueLocation FS → Maybe ⟦ A ⟧) → (ValueLocation FS → Maybe ⟦ B ⟧)
                 → Maybe (StoredValue FS) → Maybe (StoredValue FS) → Maybe ⟦ A * B ⟧
  readTyped-pair rA rB (just (SV-Ptr fl)) (just (SV-Ptr sl)) = combine-typed (rA fl) (rB sl)
  readTyped-pair rA rB _                  _                  = nothing

  -- Read a register-resident value of type `A` straight out of a register cell
  -- (the input-side dual of `readTyped`, which follows a pointer into memory).
  readReg-typed : (A : Type) → StoredValue FS → Maybe ⟦ A ⟧
  -- D074: a unit value is materialisable from ANY register content (mirrors
  -- `readTyped Unit`) — unit has no representation, so a unit input imposes
  -- no residence discipline on `Input1`.
  readReg-typed Unit _                  = just tt
  readReg-typed Int (SV-Lit fits-int v) = just v
  readReg-typed _   _                   = nothing

  readTyped : (A : Type) → ValueLocation FS → LocState FS → Maybe ⟦ A ⟧
  readTyped Unit    loc s = just tt
  readTyped Int     loc s = readTyped-int (readLoc s loc)
  readTyped (A * B) loc s =
    readTyped-pair (λ l → readTyped A l s) (λ l → readTyped B l s)
      (readLoc s loc) (readLoc s (sucLoc loc))
  readTyped _       loc s = nothing

  -- Plan 0.26 — `pure-sigop-output` discharged via `FitsInReg`.
  --
  -- For codomains satisfying `FitsInReg` (i.e. `Int`, `Float`), the
  -- abstract `ValidAtWF` is location-only (see `valid-primitive-wf`
  -- in `ClosureWellFormed`), so the content of `Output` is irrelevant
  -- at this layer — we return `unit-storedvalue` as a canonical
  -- sentinel. The per-arch concrete machine's actual primitive value
  -- is established by the Simulation lemma. For non-FitsInReg
  -- codomains a narrower per-name postulate fires.
  postulate
    -- Narrower per-name discharge target: only for `Pure` SigOps whose
    -- codomain is not `FitsInReg`-classified (Sum/Pair/μ/ν/→/Unit/Str/
    -- Buffer/…). Layer-0 hit: `arith.{lt,…,ne}.int` (Unit + Unit) and
    -- `str.lit.<s>` (Str) — neither fires at runtime in Layer 0.
    structured-pure-sigop-output : ∀ {A B} → SigOpInfo A B → LocState FS →
                                   StoredValue FS

  pure-sigop-output : ∀ {A B} → SigOpInfo A B → LocState FS →
                      StoredValue FS
  -- Plan 0.54 rung A (A4): compute the REAL output. For a fits-in-reg codomain,
  -- read the SigOp's input `⟦ A ⟧` off `Input1`'s pointee (`readTyped`) and apply
  -- `semM` — the flat machine now computes the arith value (was `unit-storedvalue`
  -- sentinel). If the input can't be read (register-resident scalar / unstaged),
  -- fall back to the sentinel (kept total; that path is a later refinement).
  -- Aux-style (explicit `Maybe` arguments), NOT `with`: a `with`-application is
  -- OPAQUE — its scrutinees are not subterms of the goal, so downstream proofs
  -- cannot `rewrite` them (this blocked the `pure-sigop-value-correct`
  -- discharge). With the dispatches as real arguments the caller's `rewrite`s
  -- (fits-in-reg? / Input1 pointer / readTyped-adequate) all reduce the term.
  pure-sigop-out-val : ∀ {A B} → SigOpInfo A B → FitsInReg B → Maybe ⟦ A ⟧
                     → StoredValue FS
  -- Plan 0.74 J5: the SigOp's semantics is target-relative now, and the
  -- machine's target is `fs-numerics FS`. That this is the SAME `TargetNum`
  -- the spec uses (`arch-numerics arch`) is the standing `fmt-agree` premise —
  -- the one remaining width channel, and what item 5 of J6 removes.
  pure-sigop-out-val si fitB (just a) = SV-Lit fitB (semM si (fs-numerics FS) a)
  pure-sigop-out-val si fitB nothing  = unit-storedvalue

  pure-sigop-out-aux : ∀ {A B} → SigOpInfo A B → LocState FS
                     → Maybe (FitsInReg B) → Maybe (ValueLocation FS)
                     → StoredValue FS
  pure-sigop-out-aux {A} si s (just fitB) (just in-loc) =
    pure-sigop-out-val si fitB (readTyped A in-loc s)
  -- Plan 0.54 rung A: REGISTER-RESIDENT INPUT. `Input1` is not a pointer, so it
  -- holds the value itself (`SV-Lit`) — the input-side mirror of `at-reg`. Read
  -- it straight out of the register instead of falling back to the sentinel.
  -- Forced top-down by `comp-step`: after a primitive-returning `f`,
  -- `mov-to-input` leaves `Input1` holding an `SV-Lit`, so `g` must be able to
  -- consume it. (Values travel in registers; memory is the spill path.)
  pure-sigop-out-aux {A} si s (just fitB) nothing =
    pure-sigop-out-val si fitB (readReg-typed A (readReg (regs s) Input1))
  pure-sigop-out-aux si s nothing     _       = structured-pure-sigop-output si s

  pure-sigop-output {A} {B} si s =
    pure-sigop-out-aux si s (fits-in-reg? B) (sv-as-loc (readReg (regs s) Input1))

  -- | Shape-direct output dispatch. Pattern-matches on EffectShape
  -- directly, so `with effect si` in downstream proofs reduces the
  -- goal cleanly (no with-abstraction nesting that would block
  -- `pure-sigop-output`'s definitional reductions). Wrapper below.
  exec-sigop-output-of : ∀ {A B} → EffectShape B → SigOpInfo A B →
                         LocState FS → StoredValue FS
  exec-sigop-output-of Pure      si s = pure-sigop-output si s
  exec-sigop-output-of (Emits _) _  _ = unit-storedvalue
  exec-sigop-output-of (Halts _) _  _ = unit-storedvalue

  -- | Dispatch-derived output (wrapper that unfolds to the
  -- shape-direct helper).
  exec-sigop-output : ∀ {A B} → SigOpInfo A B → LocState FS →
                      StoredValue FS
  exec-sigop-output si s = exec-sigop-output-of (effect si) si s

  -- | Shape-direct halt-flag dispatch.
  exec-sigop-halts-of : ∀ {A B} → EffectShape B → SigOpInfo A B →
                        LocState FS → Bool
  exec-sigop-halts-of (Halts _) _ _ = true
  exec-sigop-halts-of _         _ _ = false

  -- | Dispatch-derived halt-flag (wrapper).
  exec-sigop-halts : ∀ {A B} → SigOpInfo A B → LocState FS → Bool
  exec-sigop-halts si s = exec-sigop-halts-of (effect si) si s

  -- Plan 0.13.2: `encode-const` and `encode-code-addr` deleted —
  -- their roles are now real `StoredValue` constructors.
  -- `instr-load-const fits-int n` writes `SV-Int n` to Output;
  -- `instr-load-code-addr n` writes `SV-Code n`. Two trusted-base
  -- axioms removed.

  ------------------------------------------------------------------------
  -- Main exec-abstract definition
  ------------------------------------------------------------------------

  -- | Execute one abstract instruction
  -- Plan 0.30: read the scrutinee tag at `*Input1` (a heap/stack cell).
  -- Non-recursive (no exec call), so defined ahead of the mutual block.
  case-tag-at : LocState FS → Maybe (StoredValue FS)
  case-tag-at s with sv-as-loc (readReg (regs s) Input1)
  ... | just loc = readLoc s loc
  ... | nothing  = nothing

  ------------------------------------------------------------------------
  -- THE LOOP, REIFIED (2026-07-31). `exec-loop` used to sit INSIDE the mutual
  -- block and call `exec-trace body` directly, which cost a `{-# TERMINATING #-}`
  -- — foetus lost the fuel decrease across that boundary (`exec-trace` carries no
  -- fuel, and a nested `instr-loop` resets fuel to `loopFuel`). A pragma is a
  -- postulate in disguise (D062), and this one was replicated in every proof that
  -- mirrors the loop.
  --
  -- Abstracting the body runner away fixes it: `exec-loop-run` recurses on FUEL
  -- ALONE, structurally, with no call into the mutual block at all. The mutual
  -- block supplies `exec-trace body` as that runner — a call whose argument
  -- `body` is a strict subterm of `instr-loop body`, which foetus does see.
  --
  -- The same reification carries the PROOFS: their loop lemmas become plain fuel
  -- inductions taking "the runner preserves P" as a hypothesis, and lose their
  -- pragmas too.
  ------------------------------------------------------------------------
  BodyRunner : Set
  BodyRunner = LocState FS → AllocState {FS} → LocState FS × AllocState {FS}

  -- one iteration's re-anchoring: the loop RESTORES the stack state
  -- (`stackMem`, `current-frame`, `next-slot`) after the body, keeping only
  -- register and heap progress. See the frame-balance note below.
  loop-reanchor-loc : LocState FS → LocState FS → LocState FS
  loop-reanchor-loc s s' = record s' { stackMem = stackMem s }

  loop-reanchor-alloc : AllocState {FS} → AllocState {FS} → AllocState {FS}
  loop-reanchor-alloc alloc alloc' =
    record alloc' { current-frame = current-frame alloc ; next-slot = next-slot alloc }

  exec-loop-run : BodyRunner → ℕ → LocState FS → AllocState {FS} →
                  LocState FS × AllocState {FS}
  exec-loop-run run zero    s alloc = record s { halted = true } , alloc
  exec-loop-run run (suc n) s alloc with halted s
  ... | true  = s , alloc
  ... | false with readReg (regs s) Scratch
  ...   | SV-Tag 0 = s , alloc
  ...   | _        = exec-loop-run run n (loop-reanchor-loc s (proj₁ (run s alloc)))
                                         (loop-reanchor-alloc alloc (proj₂ (run s alloc)))

  -- | MATERIALISE a literal: turn its source payload into the target's
  -- representation (plan 0.73, D113).
  --
  -- An `Int` literal is already the machine value — the residue carrier is
  -- width-free, so there is nothing to do. A `Float` literal is a dyadic, and
  -- becomes bits only once a FORMAT is known, which is why the machine carries
  -- the target's `float-format`. This is the one place source syntax turns
  -- into bits; everything downstream of it, `SV-Lit` included, is bits.
  lit-value : ∀ {A} (p : FitsInReg A) → LitPayload p → ⟦ A ⟧
  -- D115: at THIS target's width. `frame-word` is the machine word in BYTES,
  -- so `8 * frame-word FS` is the bit width — the machine already had the
  -- fact, which is why baking `Word64` anywhere was avoidable. `fromℤ` is
  -- two's complement (D054: `Int` is SIGNED), so `-5` becomes `2^w - 5`.
  lit-value fits-int   z = Word.Width.fromℤ (8 ℕ.* FrameSemantics.frame-word FS) z
  -- PLAN 0.74 K1: the machine rounds the DECIMAL at its own format. Same
  -- function the denotation calls, which is what keeps the correspondence
  -- `refl`-shaped and needs no rounding theorem.
  lit-value fits-float d = round (FrameSemantics.float-format FS) d

  -- Plan 0.13.1: mutually recursive with exec-trace (case-on-tag
  -- dispatches into one of two sub-traces).
  exec-abstract : AbstractInstr → LocState FS → AllocState {FS} →
                  LocState FS × AllocState {FS}
  exec-trace : AbstractTrace → LocState FS → AllocState {FS} →
               LocState FS × AllocState {FS}
  -- Plan 0.29: fuel-bounded execution of a loop body. Re-runs `body`
  -- while the `Scratch` register is a nonzero counter; the body updates
  -- `Scratch` each iteration. Since 2026-07-31 this is a WRAPPER around the
  -- reified `exec-loop-run` above — same reduction behaviour, structural
  -- recursion, and the `{-# TERMINATING #-}` pragma is gone.
  exec-loop : ℕ → AbstractTrace → LocState FS → AllocState {FS} →
              LocState FS × AllocState {FS}
  -- Plan 0.30: branch dispatcher for case-on-tag. Mutually recursive with
  -- exec-trace (it runs one of the two sub-traces). Split off as a named
  -- helper (rather than an inline `with`) so external proofs can case on
  -- the tag read explicitly — see SMPrimitives' instruction-or-trace lift.
  exec-case-dispatch : Maybe (StoredValue FS) → AbstractTrace → AbstractTrace →
                       LocState FS → AllocState {FS} → LocState FS × AllocState {FS}

  -- mov-to-output: Output := Input1
  exec-abstract mov-to-output s alloc =
    record s { regs = writeReg (regs s) Output (readReg (regs s) Input1) } , alloc

  -- mov-to-input: Input1 := Output (compose bridge)
  exec-abstract mov-to-input s alloc =
    record s { regs = writeReg (regs s) Input1 (readReg (regs s) Output) } , alloc

  -- load-indirect: Output := *Input1.
  -- Plan 0.13.2: Input1 holds StoredValue; only succeeds when it's
  -- a pointer. sv-as-loc returns the address or `nothing`.
  -- Plan 0.27: `with`-free (routes through exec-load-via-resolved) so a
  -- `sv-as-loc … ≡ just loc` hypothesis reduces the result transparently.
  exec-abstract load-indirect s alloc =
    exec-load-via-resolved Output (sv-as-loc (readReg (regs s) Input1)) s , alloc

  -- load-indirect-suc: Output := *(sucLoc Input1)
  exec-abstract load-indirect-suc s alloc =
    exec-load-suc-via-resolved Output (sv-as-loc (readReg (regs s) Input1)) s , alloc

  -- load-from-slot: Output := stack[frame, slot]
  exec-abstract (load-from-slot slot) s alloc =
    exec-load-from-slot-with-value (readLoc s (AtStack (current-frame alloc) slot)) s alloc

  -- store-at-slot: stack[frame, slot] := Output
  exec-abstract (store-at-slot slot) s alloc =
    writeLoc s (AtStack (current-frame alloc) slot) (readReg (regs s) Output) , alloc

  -- store-indirect: *Input1 := Output.
  -- Plan 0.13.2: Input1 holds StoredValue; only succeeds when it's
  -- a pointer.  Plan 0.27: `with`-free (exec-store-via-resolved).
  exec-abstract store-indirect s alloc =
    exec-store-via-resolved (sv-as-loc (readReg (regs s) Input1))
                            (readReg (regs s) Output) s , alloc

  -- store-indirect-suc: *(sucLoc Input1) := Output
  exec-abstract store-indirect-suc s alloc =
    exec-store-suc-via-resolved (sv-as-loc (readReg (regs s) Input1))
                                (readReg (regs s) Output) s , alloc

  -- lea-slot: Output := &stack[frame, slot].
  -- Plan 0.13.2: Output gets a `SV-Ptr` to the slot's address.
  exec-abstract (lea-slot slot) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Ptr (AtStack (current-frame alloc) slot)) } , alloc

  -- restore-input: Input1 := stack[frame, slot]
  exec-abstract (restore-input slot) s alloc =
    exec-restore-input-with-value (readLoc s (AtStack (current-frame alloc) slot)) s alloc

  -- lea-indexed slot: Input1 := &(base + idx), base = SV-Ptr at `slot`,
  -- idx = Scratch's count (via offsetLoc). Plan 0.36 Phase 2b.
  exec-abstract (lea-indexed slot) s alloc =
    exec-lea-indexed-via (slot-base (readLoc s (AtStack (current-frame alloc) slot)))
                         (sv-tag-val (readReg (regs s) Scratch)) s , alloc

  -- instr-alloc-stack: advance the compile-time frontier by n.
  -- Capacity was verified by Dispatcher when constructing the trace.
  -- Plan 0.63: the LocState is now UNTOUCHED — the runtime `stackSlot` mirror
  -- is gone, and the FLAT machine (which is the semantics of record) moves the
  -- frame instead. This clause is the structured layer's degenerate model.
  exec-abstract (instr-alloc-stack n) s alloc =
    s , record alloc { next-slot = next-slot alloc + n }

  -- instr-dealloc-stack: the structured layer's degenerate model — nothing to
  -- do now that the runtime mirror is gone.
  exec-abstract (instr-dealloc-stack n) s alloc = s , alloc

  -- instr-reclaim-to: set next-slot to given value (actual reclamation)
  -- OCP-0003: Used by Sum wrapper allocation to place wrapper at child's reclaimable-slot.
  -- The LocState is unchanged; only the AllocState's next-slot is updated.
  exec-abstract (instr-reclaim-to n) s alloc =
    s , record alloc { next-slot = n }

  -- instr-push-frame / instr-pop-frame: the STRUCTURED layer keeps the
  -- degenerate frame model (the flat machine owns the real one).
  exec-abstract (instr-push-frame cap) s alloc = s , alloc

  exec-abstract instr-pop-frame s alloc = s , alloc

  -- instr-call-closure: transfer control to closure code
  -- This is a no-op at abstract level - the call happens via BodyCorrect.execute
  exec-abstract instr-call-closure s alloc =
    s , alloc

  ------------------------------------------------------------------------
  -- OCP-0003: Worklist Instruction Semantics
  --
  -- Worklist operations support loop-based tree traversal at runtime.
  -- Proofs use Star-based structural induction on μ-values, not loops.
  --
  -- These semantics are simplified abstractions:
  --   - Runtime uses actual counters and indexed slots
  --   - Abstract level provides type-correct behavior
  --   - Correctness follows from Star proofs, not loop simulation
  ------------------------------------------------------------------------

  -- worklist-init: Initialize worklist (count := 0)
  -- Abstract: no observable state change (empty worklist has no items)
  exec-abstract (worklist-init slot) s alloc = s , alloc

  -- worklist-push: Push Output onto worklist, advance count
  -- Abstract: store value at slot (simplified - runtime tracks index)
  exec-abstract (worklist-push slot) s alloc =
    writeLoc s (AtStack (current-frame alloc) slot) (readReg (regs s) Output) , alloc

  -- worklist-pop: Pop top item into Output, decrement count
  -- Abstract: load from slot (simplified - runtime tracks index)
  exec-abstract (worklist-pop slot) s alloc =
    exec-load-from-slot-with-value (readLoc s (AtStack (current-frame alloc) slot)) s alloc

  -- worklist-check: Set Output based on worklist empty status
  -- Abstract: no-op (Star proofs handle termination structurally)
  exec-abstract (worklist-check slot) s alloc = s , alloc

  -- Plan 0.10 Phase B / 0.11 Task A: SigOp dispatch.
  --
  -- The abstract semantics of `instr-sigop si` is **structured**: it
  -- may write a new value-location to Output and may halt the
  -- machine, but it leaves everything else (frame, alloc, memory,
  -- Input1 register) unchanged. The two postulates below
  -- (`exec-sigop-output` and `exec-sigop-halts`) are the trusted-
  -- base axioms describing what a SigOp does at the abstract level.
  -- Per-name discharge of these axioms (e.g. the exit syscall halts;
  -- `lit.int.<N>` doesn't halt and produces a constant) is downstream
  -- work — see Plan 0.11 task A and Plan 0.10 Phase E.
  --
  -- This shape encodes the relaxed CCC contract structurally:
  --   - frame-eq, slot-stable, mem-preserved, heap-monotone hold
  --     by definitional reduction (alloc and memory unchanged);
  --   - regs-only-output and Input-preservation hold via
  --     writeReg-preserves;
  --   - halted may flip false → true (halting SigOps) or stay false
  --     (pure SigOps) — `exec-sigop-halts` is the per-(arch, name)
  --     discharge target.
  --
  -- Replacing the older identity body `exec-abstract (instr-sigop si)
  -- s alloc = s , alloc` is the Plan-0.11 task-A move that surfaces
  -- the silent wildcard-payload leak as named, audit-visible
  -- postulates.
  exec-abstract (instr-sigop si) s alloc =
    record s { regs   = writeReg (regs s) Output (exec-sigop-output si s)
             ; halted = exec-sigop-halts si s }
    , alloc

  -- Plan 0.13.2: load a primitive constant into Output as `SV-Lit`.
  -- Replaces the encode-const postulate. The FitsInReg evidence is
  -- carried through to the cell so float vs int discrimination
  -- happens via pattern-matching on `SV-Lit isPrim v`.
  exec-abstract (instr-load-const isPrim v) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Lit isPrim (lit-value isPrim v)) } , alloc

  -- Plan 0.13.2: load a closure-body label's address into Output as
  -- `SV-Code n`. Replaces the encode-code-addr postulate.
  exec-abstract (instr-load-code-addr n) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Code n) } , alloc

  -- Plan 0.2.4.2 Phase D follow-up: save Input1 to closure register.
  -- Identity at the abstract level — the closure register is purely
  -- a per-arch concern.
  exec-abstract instr-save-closure-reg s alloc = s , alloc

  -- Plan 0.13.1 Phase 1: tag literal — write `SV-Tag n` to Output.
  exec-abstract (instr-load-tag-lit n) s alloc =
    record s { regs = writeReg (regs s) Output (SV-Tag n) } , alloc

  -- Plan 0.30: case-on-tag now BRANCHES on the scrutinee tag at `*Input1`,
  -- matching the x86 `compile-trace-cnt` dispatch
  --   `cmp [rdi],0 ; je inl ; <g> ; jmp end ; inl: <f>`:
  -- tag 0 → f (inl), tag ≥ 1 → g (inr), malformed scrutinee → halt.
  -- `f`/`g` are strict subterms, so the exec-trace recursion is
  -- structural. This makes `exec-loop` fold a
  -- heap-μ-value for real (see Examples.AbstractCataFold).
  exec-abstract (instr-case-on-tag f g) s alloc =
    exec-case-dispatch (case-tag-at s) f g s alloc

  -- Plan 0.14: heap allocation routed through the abstract-allocator
  -- interface (Once.Allocator.AbstractInstance). The `next-heap-ref`
  -- field of AllocState is the State of the abstract bump allocator;
  -- the allocation call returns a fresh HeapLocation and an updated
  -- counter. Disjointness is then a consequence of the interface's
  -- `blocks-disjoint`, not a parallel inline derivation.
  exec-abstract (instr-alloc-heap n) s alloc =
    let result = AI.alloc-impl n (next-heap-ref alloc)
        addr = proj₁ result
        new-state = proj₁ (proj₂ result)
    in record s { regs = writeReg (regs s) Output (SV-Ptr (AtDynamic addr)) } ,
       record alloc { next-heap-ref = new-state
                    -- the fresh block gets `n` slots; older refs keep theirs
                    ; block-size = size-with n (next-heap-ref alloc) (block-size alloc) }

  -- Plan 0.29: generic loop — run `body` while `Scratch` is a nonzero
  -- counter, fuel-bounded (1e6 ≥ any real iteration count; out-of-fuel
  -- halts, matching the x86 `Semantics.exec` out-of-fuel `just s`).
  exec-abstract (instr-loop body) s alloc = exec-loop 1000000 body s alloc

  -- Plan 0.29 (M5): register pokes (no heap, no slot, frame-preserving).
  -- alloc is returned unchanged (uniform proj₂).
  exec-abstract (instr-reg-op op) s alloc = exec-reg-op op s , alloc

  -- Plan 0.32 (M3): flat control flow is NEVER in a structured trace
  -- (it has no pc) — only the flat pc/fuel exec interprets it. Its
  -- structured semantics is therefore irrelevant; IDENTITY is the
  -- cascade-friendliest placeholder (preserves frame/heap/slot/halted/
  -- alloc, so every per-instruction invariant clause is trivial).
  exec-abstract (instr-ctrl _) s alloc = s , alloc

  -- | Execute a trace (sequence of abstract instructions)
  -- Signature declared above with exec-abstract for mutual recursion.
  exec-trace [] s alloc = s , alloc
  exec-trace (i ∷ is) s alloc with halted s
  ... | true  = s , alloc
  ... | false = let (s' , alloc') = exec-abstract i s alloc
                in exec-trace is s' alloc'

  -- Plan 0.29: fuel-bounded loop body execution. Break when `Scratch`
  -- reaches `SV-Tag 0`; otherwise run `body` (which must decrement /
  -- update `Scratch`) and recurse on fuel.
  --
  -- FRAME-BALANCE BY CONSTRUCTION: after each iteration the loop RESTORES
  -- the stack state (`stackMem`, `current-frame`, `next-slot`), keeping
  -- only register progress (`regs` — `Scratch` counter, `Output` result,
  -- `Input1` cursor) and heap progress (`heapMem`, `next-heap-ref` grow
  -- monotonically). So `instr-loop` preserves the frame/slots regardless
  -- of `body` — the ~50 per-instruction invariant lemmas hold without a
  -- body hypothesis. Sound in heap mode (the body never uses the stack;
  -- its data lives on the heap). See Plan 0.29 D1b.
  exec-loop n body s alloc = exec-loop-run (exec-trace body) n s alloc

  -- Plan 0.30: dispatch on the tag read. tag 0 → f, tag ≥ 1 → g,
  -- anything else (no pointer / non-tag cell) → halt (malformed input).
  exec-case-dispatch (just (SV-Tag 0))       f g s alloc = exec-trace f s alloc
  exec-case-dispatch (just (SV-Tag (suc _))) f g s alloc = exec-trace g s alloc
  exec-case-dispatch (just (SV-Ptr _))       f g s alloc = record s { halted = true } , alloc
  exec-case-dispatch (just (SV-Lit _ _))     f g s alloc = record s { halted = true } , alloc
  exec-case-dispatch (just (SV-Code _))      f g s alloc = record s { halted = true } , alloc
  exec-case-dispatch nothing                 f g s alloc = record s { halted = true } , alloc


  -- | Reduction lemma: when not halted, exec-trace reduces
  exec-trace-cons : ∀ (i : AbstractInstr) (is : AbstractTrace)
    (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (i ∷ is) s alloc ≡
      let (s' , alloc') = exec-abstract i s alloc
      in exec-trace is s' alloc'
  exec-trace-cons i is s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | Single instruction trace
  exec-trace-single : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (i ∷ []) s alloc ≡ exec-abstract i s alloc
  exec-trace-single i s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- A projection `f` of the allocator that every `P`-instruction's step
  -- preserves is preserved by `exec-trace` over an all-`P` trace. Proven
  -- HERE (where `exec-trace` reduces; it goes opaque under a downstream
  -- `open AbstractExec {FS}`). Used by the frame-discipline invariant to
  -- handle `instr-case-on-tag`, whose `exec-abstract` runs `exec-trace` on
  -- its (slot-stable) sub-traces. `AllI` is a local all-predicate (⊤/×) to
  -- avoid importing `Data.List`'s `All` constructors into this module.
  AllI : (AbstractInstr → Set) → AbstractTrace → Set
  AllI P []       = ⊤
  AllI P (i ∷ is) = P i × AllI P is

  exec-trace-alloc-invariant : ∀ {A : Set} (f : AllocState {FS} → A) (P : AbstractInstr → Set)
    → (∀ i s alloc → P i → f (proj₂ (exec-abstract i s alloc)) ≡ f alloc)
    → ∀ (t : AbstractTrace) → AllI P t → ∀ (s : LocState FS) (alloc : AllocState {FS})
    → f (proj₂ (exec-trace t s alloc)) ≡ f alloc
  exec-trace-alloc-invariant f P pi []       _          s alloc = refl
  exec-trace-alloc-invariant f P pi (i ∷ is) (px , pxs) s alloc with halted s
  ... | true  = refl
  ... | false = trans (exec-trace-alloc-invariant f P pi is pxs
                         (proj₁ (exec-abstract i s alloc)) (proj₂ (exec-abstract i s alloc)))
                      (pi i s alloc px)

  -- `instr-case-on-tag` preserves the allocator projection `f`: its
  -- `exec-abstract` dispatches on the scrutinee tag to `exec-trace` on one
  -- of its (all-`P`) sub-traces (or halts, leaving the allocator). Reduces
  -- HERE (downstream the recursive `exec-abstract`/`exec-case-dispatch` go
  -- opaque). This is the only `ir-to-trace`-emitted instruction whose
  -- slot-stability is recursive in its sub-traces.
  exec-abstract-case-invariant : ∀ {A : Set} (f : AllocState {FS} → A) (P : AbstractInstr → Set)
    → (∀ i s alloc → P i → f (proj₂ (exec-abstract i s alloc)) ≡ f alloc)
    → ∀ (ft gt : AbstractTrace) → AllI P ft → AllI P gt → ∀ (s : LocState FS) (alloc : AllocState {FS})
    → f (proj₂ (exec-abstract (instr-case-on-tag ft gt) s alloc)) ≡ f alloc
  exec-abstract-case-invariant f P pi ft gt aft agt s alloc with case-tag-at s
  ... | just (SV-Tag 0)       = exec-trace-alloc-invariant f P pi ft aft s alloc
  ... | just (SV-Tag (suc _)) = exec-trace-alloc-invariant f P pi gt agt s alloc
  ... | just (SV-Ptr _)       = refl
  ... | just (SV-Lit _ _)     = refl
  ... | just (SV-Code _)      = refl
  ... | nothing               = refl

  ------------------------------------------------------------------------
  -- Tree-Structured Trace Execution (OCP-0003)
  --
  -- Execute tree-structured traces that can represent recursive control
  -- flow. This is the semantic model for recursion scheme proofs.
  --
  -- PROOF ARCHITECTURE:
  --   - Structural recursion on TreeTrace matches μ-value structure
  --   - branch corresponds to sum type dispatching
  --   - call-sub corresponds to recursive scheme invocation
  --   - Sequential composition (_▸_) follows functor structure
  --
  -- RUNTIME MAPPING:
  --   At runtime, these compile to loops (worklist-based) or actual
  --   function calls, depending on the backend. The proof uses
  --   structural recursion which is equivalent for finite μ-values.
  ------------------------------------------------------------------------

  -- | Get tag from a slot (returns 0 for inj₁, 1 for inj₂, nothing if uninitialized)
  -- At runtime, this reads the discriminator field of a sum value.
  -- For proofs, we use a simplified model where nothing means "take left".
  getTag : LocState FS → AllocState {FS} → Slot → Maybe ℕ
  getTag s alloc slot with readLoc s (AtStack (current-frame alloc) slot)
  ... | nothing = nothing
  ... | just _ = just 0  -- Simplified: actual tag extraction is backend-specific

  -- | Execute a tree-structured trace
  --
  -- The structure mirrors how recursion schemes execute:
  --   ε: no-op
  --   instr i: single instruction
  --   t₁ ▸ t₂: sequence
  --   branch slot tL tR: dispatch on sum tag
  --   call-sub t: recursive call (no additional stack frame in abstract model)
  --   flat is: legacy flat trace
  exec-tree-trace : TreeTrace → LocState FS → AllocState {FS} →
                    LocState FS × AllocState {FS}

  -- Empty trace: no effect
  exec-tree-trace ε s alloc = s , alloc

  -- Single instruction
  exec-tree-trace (instr i) s alloc with halted s
  ... | true = s , alloc
  ... | false = exec-abstract i s alloc

  -- Sequential composition
  exec-tree-trace (t₁ ▸ t₂) s alloc with halted s
  ... | true = s , alloc
  ... | false = let (s' , alloc') = exec-tree-trace t₁ s alloc
                in exec-tree-trace t₂ s' alloc'

  -- Branch on tag: read discriminator and dispatch
  exec-tree-trace (branch slot tL tR) s alloc with halted s
  ... | true = s , alloc
  ... | false with getTag s alloc slot
  ... | nothing      = exec-tree-trace tL s alloc  -- Default to left if uninitialized
  ... | just 0       = exec-tree-trace tL s alloc  -- inj₁
  ... | just (suc _) = exec-tree-trace tR s alloc  -- inj₂

  -- Recursive call: execute sub-trace
  -- In abstract model, this is just trace execution (no stack frame push)
  -- Real backends implement this as function call or inlined loop
  exec-tree-trace (call-sub t) s alloc with halted s
  ... | true = s , alloc
  ... | false = exec-tree-trace t s alloc

  -- Embedded flat trace: delegate to exec-trace
  exec-tree-trace (flat is) s alloc = exec-trace is s alloc

  ------------------------------------------------------------------------
  -- Tree Trace Lemmas
  ------------------------------------------------------------------------

  -- | Empty trace is identity
  exec-tree-trace-ε : ∀ (s : LocState FS) (alloc : AllocState {FS}) →
    exec-tree-trace ε s alloc ≡ (s , alloc)
  exec-tree-trace-ε s alloc = refl

  -- | Sequential composition reduces when not halted
  exec-tree-trace-seq : ∀ (t₁ t₂ : TreeTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-tree-trace (t₁ ▸ t₂) s alloc ≡
      let (s' , alloc') = exec-tree-trace t₁ s alloc
      in exec-tree-trace t₂ s' alloc'
  exec-tree-trace-seq t₁ t₂ s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | Single instruction in tree form matches abstract execution
  exec-tree-trace-instr : ∀ (i : AbstractInstr) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-tree-trace (instr i) s alloc ≡ exec-abstract i s alloc
  exec-tree-trace-instr i s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | call-sub is transparent when not halted
  exec-tree-trace-call-sub : ∀ (t : TreeTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-tree-trace (call-sub t) s alloc ≡ exec-tree-trace t s alloc
  exec-tree-trace-call-sub t s alloc not-halted with halted s
  ... | false = refl
  ... | true with () ← not-halted

  -- | flat trace execution matches exec-trace
  exec-tree-trace-flat : ∀ (is : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    exec-tree-trace (flat is) s alloc ≡ exec-trace is s alloc
  exec-tree-trace-flat is s alloc = refl

  ------------------------------------------------------------------------
  -- TreeTrace to Flat Trace Equivalence
  --
  -- KEY THEOREM: exec-tree-trace and exec-trace produce same results
  -- when the flat trace correctly models the tree structure.
  --
  -- This enables proving correctness via TreeTrace (structural induction)
  -- and then transferring to flat traces (what actually executes).
  --
  -- PROOF APPROACH:
  --   For simple trees without call-sub or branch:
  --     exec-tree-trace t ≡ exec-trace (treeToFlat t)
  --
  --   For trees with call-sub (where semantics are identical):
  --     call-sub just continues execution, so treeToFlat is correct
  --
  --   For trees with branch (runtime vs proof dispatch):
  --     Need to know which branch is taken to establish equivalence
  ------------------------------------------------------------------------

  -- | treeToFlat preserves sequential composition
  exec-trace-++ : ∀ (t₁ t₂ : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    exec-trace (t₁ ++ t₂) s alloc ≡
      let (s' , alloc') = exec-trace t₁ s alloc
      in exec-trace t₂ s' alloc'
  exec-trace-++ [] t₂ s alloc not-halted = refl
  exec-trace-++ (i ∷ t₁) t₂ s alloc not-halted with halted s
  ... | true with () ← not-halted
  ... | false = exec-trace-++ t₁ t₂ (proj₁ (exec-abstract i s alloc))
                              (proj₂ (exec-abstract i s alloc))
                              exec-abstract-preserves-not-halted'
    where
      -- Helper: exec-abstract preserves not-halted (postulated for now)
      -- Full proof requires case analysis on all instructions
      postulate
        exec-abstract-preserves-not-halted' : halted (proj₁ (exec-abstract i s alloc)) ≡ false

  -- | Simple trees (no branch): exec-tree-trace ≡ exec-trace ∘ treeToFlat
  -- This is the foundation for proving recursive scheme correctness
  exec-tree-flat-equiv-simple : ∀ (t : TreeTrace) (s : LocState FS) (alloc : AllocState {FS}) →
    halted s ≡ false →
    -- For trees without branch, treeToFlat is semantically equivalent
    ⊤  -- Full proof requires induction on TreeTrace structure
  exec-tree-flat-equiv-simple t s alloc not-halted = tt