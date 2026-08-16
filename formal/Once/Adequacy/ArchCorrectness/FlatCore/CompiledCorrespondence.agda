-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
--
-- `CompiledCorr` — the correspondence AT A COMPILED PROGRAM — stated once for
-- every arch (plan 0.65 G2, item 4's first slice).
--
-- WHY IT NEEDS ITS OWN MODULE. The record mentions BOTH layers: `FlatCorr` and
-- `RetAddrs` come from `FlatCorrespondence`, while `blk-off` and the compiled
-- program come from `FlatComposition`. Neither of those imports the other, so
-- the record has no home in either — it belongs one level above both, which is
-- also where the generic event engine will live when `ConcFlatSim` follows.
--
-- WHAT THE MEASUREMENT SHOWED. x86-64's and riscv64's copies were STRUCTURALLY
-- IDENTICAL — same four fields, same shapes, differing only in `X.State` versus
-- `R.State` and the corresponding projections. That is the evidence this layer
-- is generic in fact and not just in aspiration, and it is why the extraction
-- starts here rather than with the 1,661-line engine: a small piece that is
-- provably shared, moved first, so the engine's parameter surface is settled
-- before the engine moves.
--
-- The four fields, and why each lives HERE rather than in `FlatCorr`:
--
--   dataCorr  the data correspondence proper — that one IS `FlatCorr`.
--   pc-off    translating an abstract pc needs `prog`, which `FlatCorr` has no
--             access to. Same for the two below.
--   ret-eq    D093: every ghost `fret` entry is REALLY in the machine's memory,
--             at its frame's window end, under the same block-offset
--             translation the pc uses. This is what makes a return a
--             correspondence step rather than an assumption.
--   code-eq   D096: a `SV-Code ℓ` encodes to `caddr hv ℓ`, and that is the index
--             the compiled program's OWN label scan finds — the same scan the
--             concrete code-address load and jump use.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; false)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (RegRoles)
open import Data.Nat using (NonZero)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label)
open import Once.CanonicalName using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
  -- Plan 0.63 (D089): the DEFINITION'S identity, which keys its labels — and
  -- therefore what `RunContext` needs. Added 2026-08-16 for `bs-lea-slot`'s
  -- `RunAt` premise; see the field.
  (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  ⦃ slot-size-nz : NonZero slot-size ⦄
  (word-eq : frame-word FS ≡ slot-size)
  (Reg : Set)
  (roles : RegRoles Reg)
  (State : Set)
  (rreg : State → Reg → ℕ)
  (memory : State → (ℕ → Maybe ℕ))
  (xhalted : State → Bool)
  -- WHERE AN UNSPILLED RETURN ADDRESS LIVES (plan 0.65 G2, 2026-08-16). In the
  -- one-instruction window between a call and the callee's body marker the head
  -- pending return has not reached its stack cell yet, and where it IS is an ABI
  -- fact — memory on x86-64, the link register on RISC-V. This is what the
  -- machine claims there; `ret-eq` hands it to `RetAddrs` as the head row, which
  -- `FlatState.flink` selects. See `FlatCorrespondence.RetAddrs`.
  (link-claim : State → ℕ → ℕ → Set)
  -- …and the two things `FlatCorrespondence` does not see: where the machine's
  -- program counter is, and how a compiled program resolves a label. Both are
  -- about the COMPILED program, which is this layer's whole subject.
  (xpc : State → ℕ)
  (Program : Set)
  (compile-trace : AbstractTrace → Program)
  (find-label : Program → Label → Maybe ℕ)
  -- the block-offset translation and block LENGTH, from `FlatComposition`
  (blk-off : AbstractTrace → ℕ → ℕ)
  (blk-len : AbstractInstr → ℕ)
  -- …and fuel-bounded execution, the one machine operation a BLOCK step needs
  -- that a state correspondence does not.
  (exec : ℕ → Program → State → Maybe State)
  -- THE MACHINE'S WORD MODULUS (plan 0.65 G2 item 4, slice 2, group 2). Added
  -- for `bs-load-tag-lit`, whose engine call site passes a literal-fits premise
  -- `n < W.modulus` — the ONE group-2 field with a premise beyond the three.
  -- Not derivable from `slot-size`: x86-32 has 32-bit words and 4-byte slots,
  -- but the two are different facts, and the correspondence needs only this one.
  (modulus : ℕ)
  where

open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fpc; fret; falloc; fclosure; flink)
open MemOps {FS} using (writeLoc; writeLocToHeap; readLoc)
open FlatMachine {FS} using (floc; halted; fetch)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-ref; ref-id)
open import Data.Nat using (zero; suc; _+_; _*_; _∸_; _≤_; _<_)
open import Data.Nat.Properties using (<-irrefl; <-transˡ; ≤-trans; m≤m+n)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Properties using (drop-[])
open import Data.Maybe using (nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong)
open import Once.CCC.Label using (LabelId; thunk)
-- …and the pieces the LAST FIVE fields' types need: the store-WF predicates
-- (arch-free, parameterised by `FS`) and the two literal shapes.
open import Once.CCC.Machine.FlatStoreWF FS using (sv-below; svm-below)
open import Once.Type using (fits-int; fits-float)
open import Once.Word using (Carrier)
open import Data.Float using () renaming (Float to AgdaFloat)
open import Once.Semantics.FloatBits using (float-bits)

import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
import Once.Adequacy.ArchCorrectness.FlatCore.RunContext as RC
-- PRIVATE: an instance re-opened publicly would clash with the `C` every arch
-- already binds for its own `FlatCorrespondence` instance. Only the record
-- below is exported.
--
-- `RC` is private for a different reason: `EventEngine` opens `RunContext`
-- PUBLICLY at the same arguments, so re-exporting it here would make `RunAt`
-- ambiguous at every engine consumer. Same instance either way (module
-- application is by alias), so the two `RunAt`s are one type.
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted
  module CRC = RC o FS slot-size word-eq

open CFC using (HeapView; FlatCorr; RetAddrs; frames-of; caddr; HDom; haddr
               ; lo; hfront; descend-view; extend-view; slots; dom-fresh)
open RegRoles roles using (sp-reg; in1-reg; scratch-reg; count-reg)

------------------------------------------------------------------------
-- THE COMPILED CORRESPONDENCE.
------------------------------------------------------------------------
record CompiledCorr (hv : HeapView) (prog : AbstractTrace)
                    (fs : FlatState) (s : State) : Set where
  field
    dataCorr : FlatCorr hv fs s
    pc-off   : xpc s ≡ blk-off prog (fpc fs)
    ret-eq   : RetAddrs (blk-off prog) (memory s) (link-claim s) (flink fs)
                        (frames-of (falloc fs)) (fret fs)
    code-eq  : ∀ (ℓ : LabelId) (j : ℕ)
             → find-label (compile-trace prog) (thunk ℓ) ≡ just j
             → caddr hv ℓ ≡ j
open CompiledCorr public

------------------------------------------------------------------------
-- THE ARCH-FREE HELPERS from `ConcFlatSim` (plan 0.65 G2 item 4, slice 1).
--
-- Classifying that file's 14 top-level definitions showed three groups: some
-- mention no machine at all, some mention it only through `rreg`, and some
-- enumerate the ISA. The first two move here; only the third has to become a
-- parameter of the engine. These are the first two groups.
------------------------------------------------------------------------

-- Fetching past the end means nothing is left to drop.
fetch-nothing-drop : ∀ (prog : AbstractTrace) (k : ℕ)
                   → FlatMachine.fetch {FS} prog k ≡ nothing → drop k prog ≡ []
fetch-nothing-drop []       k       eq = drop-[] k
fetch-nothing-drop (i ∷ is) zero    ()
fetch-nothing-drop (i ∷ is) (suc k) eq = fetch-nothing-drop is k eq

-- …and fetching AT `k` exposes that instruction at the head of the drop. The
-- abstract-side ingredient for per-instruction pc-alignment.
fetch-just-drop : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
                → FlatMachine.fetch {FS} prog k ≡ just i
                → drop k prog ≡ i ∷ drop (suc k) prog
fetch-just-drop []       k       i ()
fetch-just-drop (x ∷ xs) zero    i eq = cong (_∷ xs) (just-injective eq)
fetch-just-drop (x ∷ xs) (suc k) i eq = fetch-just-drop xs k i eq

-- An address at or above the heap frontier aliases no LIVE heap cell — every
-- mapped cell is strictly below it (`dom-below`).
above-frontier-disj : ∀ {hv : CFC.HeapView} (a : ℕ) → CFC.hfront hv ≤ a
                    → ∀ hl → CFC.HDom hv hl → a ≡ CFC.haddr hv hl → ⊥
above-frontier-disj {hv} a le hl live eq =
  <-irrefl (sym eq) (<-transˡ (CFC.dom-below hv live) le)

-- …and the instance every stack store needs: a current-frame slot address is at
-- or above the stack pointer, hence above every live heap cell. Stated through
-- `rreg`/`sp-reg`, which is why it is generic despite naming a register.
slot-heap-disj : ∀ {hv : CFC.HeapView} (fs : FlatState) (s : State) → CFC.FlatCorr hv fs s
               → (k : ℕ) → ∀ hl → CFC.HDom hv hl
               → (rreg s (sp-reg) + k * slot-size ≡ CFC.haddr hv hl) → ⊥
slot-heap-disj {hv} fs s corr k =
  above-frontier-disj {hv} (rreg s sp-reg + k * slot-size)
    (≤-trans (CFC.sep corr) (m≤m+n (rreg s sp-reg) (k * slot-size)))

-- A HEAP STORE THROUGH A DYNAMIC POINTER IS A HEAP STORE, for every value shape
-- the Output register can hold — the stack pointer included. Proven
-- unconditionally 2026-07-31 (it used to hold for four shapes of five, because
-- `writeLoc` dropped a stack pointer); arch-free, so it belongs here.
store-guard : ∀ (fs : FlatState) (hl : HeapLocation)
            → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
              ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
store-guard fs hl = go (readReg (regs (floc fs)) Output) refl
  where go : ∀ (v : StoredValue FS) → readReg (regs (floc fs)) Output ≡ v
           → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
             ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
        go (SV-Tag t)             o-eq rewrite o-eq = refl
        go (SV-Lit p v)           o-eq rewrite o-eq = refl
        go (SV-Code c)            o-eq rewrite o-eq = refl
        go (SV-Ptr (AtDynamic w)) o-eq rewrite o-eq = refl
        go (SV-Ptr (AtStack f k)) o-eq rewrite o-eq = refl

------------------------------------------------------------------------
-- A BLOCK STEP — one abstract instruction, the whole block it compiles to.
--
-- Identical on both arches before this moved: same Σ, same three components,
-- differing only in the state type and which `exec`. `BlockStepAt` carries TWO
-- views because the view-EXTENDING instructions (`alloc-heap` extends it,
-- `alloc-stack`/`c-thunk`/`call` descend it) land their post-state in a
-- different one; `BlockStep` is the diagonal, which is most of them.
------------------------------------------------------------------------
BlockStepAt : HeapView → HeapView → AbstractTrace → FlatState → State → AbstractInstr → Set
BlockStepAt hv hv' prog fs s i =
  Σ State (λ s' → (exec (blk-len i) (compile-trace prog) s ≡ just s')
                × CompiledCorr hv' prog (FlatMachine.flat-exec-instr {FS} i prog fs) s')

BlockStep : HeapView → AbstractTrace → FlatState → State → AbstractInstr → Set
BlockStep hv = BlockStepAt hv hv

------------------------------------------------------------------------
-- THE BLOCK-STEP SUPPLY (plan 0.65 G2 item 4, slice 2).
--
-- One field per abstract instruction: what an ARCH owes the generic engine.
-- The engine dispatches on `AbstractInstr` and calls these; giving it this
-- record is what makes the event/trace layer — the largest single file — written
-- once rather than per target.
--
-- BUILT GROUP BY GROUP, BY PREMISE COUNT, because the 42 fields are not
-- uniform: 11 take only (cc, h, ft), and the tail runs to `alloc-heap`'s 14,
-- carrying view-descent and resource premises where a transcription slip would
-- typecheck but mean the wrong thing. This is also each arch's checklist.
--
-- WHERE THE FIELD SHAPES COME FROM, and it is NOT either arch's block-step
-- declaration. A field's premises are exactly what the ENGINE can supply at the
-- dispatch site: the correspondence, non-halt, the fetch, and whatever it
-- derives from `FlatInv`/`RunAt`. Anything an arch needs BEYOND that is that
-- arch's own business, closed over when it builds its record.
--
-- The case that forced this, and that a declaration-driven transcription would
-- have got wrong: `lea-slot` takes (cc, h, ft) on x86-64, which computes the
-- address with `lea`, but riscv64 has no `lea` and uses `addi` — a real add —
-- so ITS block-step also needs an address no-wrap premise (plan 0.70). Copying
-- either signature into the record would be wrong: x86-64's under-constrains
-- riscv64, riscv64's imposes on x86-64 a premise it cannot discharge. The field
-- is the ENGINE's interface; riscv64 supplies it by applying its block-step to
-- a bound from its own resource parameters.
--
-- GROUP 1 — the straight-line register moves and the two no-op controls: no
-- premises beyond the correspondence, non-halt, and the fetch.
--
-- GROUP 2 — `lea-slot`, `save-closure-reg`, `load-tag-lit`. `save-closure-reg`
-- is three-premise like group 1; `load-tag-lit` is where the engine passes a
-- fact it DERIVED rather than one it was handed, and it is why this module
-- takes the machine's word `modulus`. `lea-slot` sits between the two: the
-- engine hands over the `RunAt` itself and lets the arch derive from it (see
-- the field — the three-premise form was refutable).
------------------------------------------------------------------------
-- `Set₁`: the fields quantify over `HeapView`, which is itself `Set₁`.
record BlockSteps : Set₁ where
  field
    bs-mov-to-output :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just mov-to-output
      → BlockStep hv prog fs s mov-to-output
    bs-mov-to-input :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just mov-to-input
      → BlockStep hv prog fs s mov-to-input
    bs-mov-input2-to-output :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just mov-input2-to-output
      → BlockStep hv prog fs s mov-input2-to-output
    bs-mov-output-to-input2 :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just mov-output-to-input2
      → BlockStep hv prog fs s mov-output-to-input2
    bs-scratch-one :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-one)
      → BlockStep hv prog fs s (instr-reg-op scratch-one)
    bs-scratch-zero :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-zero)
      → BlockStep hv prog fs s (instr-reg-op scratch-zero)
    bs-count-zero :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reg-op count-zero)
      → BlockStep hv prog fs s (instr-reg-op count-zero)
    bs-scratch-load-count :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-load-count)
      → BlockStep hv prog fs s (instr-reg-op scratch-load-count)
    bs-c-label :
      ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-label n))
      → BlockStep hv prog fs s (instr-ctrl (c-label n))
    bs-reclaim-to :
      ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reclaim-to n)
      → BlockStep hv prog fs s (instr-reclaim-to n)
    bs-worklist-init :
      ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (worklist-init n)
      → BlockStep hv prog fs s (worklist-init n)
    bs-worklist-check :
      ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (worklist-check n)
      → BlockStep hv prog fs s (worklist-check n)
    ------------------------------------------------------------------
    -- GROUP 2 — the three that still take (cc, h, ft) at the DISPATCH SITE,
    -- read off the engine's calls rather than either arch's declaration.
    --
    -- `lea-slot` is the case that made the rule (see the header): x86-64's
    -- block-step takes (cc, h, ft) and riscv64's takes a fourth address
    -- no-wrap premise, because it computes the address with a real `addi`.
    -- riscv64 applies its own resource parameter when it builds this record,
    -- and x86-64 is not made to discharge a bound its `lea` never needed.
    --
    -- …AND THE `RunAt`, ADDED 2026-08-16 BECAUSE THE THREE-PREMISE FORM WAS
    -- REFUTABLE. riscv64's parameter was the ONE member of the D087 bound
    -- family not conditioned on the run context, and the 2026-07-30 probe
    -- killed it: `CompiledCorr` at the empty view, a frame based at 0 and
    -- `prog = lea-slot modulus ∷ []` satisfies every premise while the
    -- conclusion says `modulus < modulus`. Nothing in a CORRESPONDENCE bounds
    -- a slot INDEX — that is `RunAt`'s shape check, via `Emitted`.
    --
    -- So the engine passes `inv-run wf` here, exactly as it does when deriving
    -- `bs-load-tag-lit`'s range premise. x86-64 ignores the argument (its
    -- `lea` needs no bound); riscv64 feeds it to `slot-addr-no-wrap`, which
    -- now has the same shape as `HeapRoom`/`StackRoom`/`CallRoom`.
    ------------------------------------------------------------------
    bs-lea-slot :
      ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (lea-slot slot)
      → CRC.RunAt prog fs
      → BlockStep hv prog fs s (lea-slot slot)
    bs-save-closure-reg :
      ∀ {hv : HeapView} prog fs s → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just instr-save-closure-reg
      → BlockStep hv prog fs s instr-save-closure-reg
    -- …and the group's one FOUR-premise field. The engine does not merely
    -- forward `cc`/`h`/`ft` here: it applies its own literal-fits resource
    -- parameter (`tag-fits prog fs s n (inv-run wf) cc ft`) and passes the
    -- RESULT. So `n < modulus` is what the field takes — the applied fact, not
    -- the parameter that produced it, which stays the engine's business.
    -- Both arches' block-steps already take exactly this premise (D087 /
    -- plan 0.70 phase D: an elaborated tag is in range by construction, it is
    -- simply not threaded from the frontend yet).
    bs-load-tag-lit :
      ∀ {hv : HeapView} prog fs s n → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-load-tag-lit n)
      → n < modulus
      → BlockStep hv prog fs s (instr-load-tag-lit n)
    ------------------------------------------------------------------
    -- GROUP 3, the 5–8 band's first half — THE LOADS AND THE STORES.
    --
    -- Where the extra premises come from, and it is a DIFFERENT source than
    -- group 2's: the engine does not hand these down from its own parameters,
    -- it CASE-SPLITS to get them. `load-indirect` is dispatched by a helper
    -- that splits `Input1`'s value and then the target cell, and calls a
    -- different block-step per branch — which is why one abstract instruction
    -- takes TWO fields here (`…` and `…-stack`) and not one. The field list
    -- follows the branches, because the branches are what the engine has.
    --
    -- SO THE `nothing` BRANCHES ARE NOT FIELDS. An unwritten slot or an empty
    -- heap cell does not step: it either goes to `⊥` (the shape table forbids
    -- reading an unwritten slot) or to a STUCK route, where the engine shows
    -- both machines halt. The stuck routes name concrete instructions, so they
    -- are a separate per-arch supply the engine will need — NOT block-steps,
    -- and not this record. See the handoff.
    --
    -- The disjointness premise is spelled in the shape the core's own
    -- `slot-heap-disj` produces, since that is what the engine passes. Both
    -- arches' `slot-to-disp k` IS `k * slot-size`, definitionally.
    ------------------------------------------------------------------
    bs-load-indirect :
      ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just load-indirect
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
      → HDom hv hl
      → heapMem (floc fs) hl ≡ just w
      → BlockStep hv prog fs s load-indirect
    bs-load-indirect-stack :
      ∀ {hv : HeapView} prog fs s f k w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just load-indirect
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
      → f ≡ current-frame (falloc fs)
      → k < frame-slots (falloc fs)
      → stackMem (floc fs) (current-frame (falloc fs)) k ≡ just w
      → BlockStep hv prog fs s load-indirect
    bs-load-indirect-suc :
      ∀ {hv : HeapView} prog fs s hl w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just load-indirect-suc
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
      → HDom hv (sucHL hl)
      → heapMem (floc fs) (sucHL hl) ≡ just w
      → BlockStep hv prog fs s load-indirect-suc
    bs-load-indirect-suc-stack :
      ∀ {hv : HeapView} prog fs s f k w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just load-indirect-suc
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
      → f ≡ current-frame (falloc fs)
      → suc k < frame-slots (falloc fs)
      → stackMem (floc fs) (current-frame (falloc fs)) (suc k) ≡ just w
      → BlockStep hv prog fs s load-indirect-suc
    -- The three STACK READS. Same two premises each — the slot is inside the
    -- runtime frame, and it has been written — and they differ only in which
    -- register receives the value, which is the arch's business, not the
    -- engine's.
    bs-load-from-slot :
      ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (load-from-slot slot)
      → slot < frame-slots (falloc fs)
      → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
      → BlockStep hv prog fs s (load-from-slot slot)
    bs-restore-input :
      ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (restore-input slot)
      → slot < frame-slots (falloc fs)
      → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
      → BlockStep hv prog fs s (restore-input slot)
    bs-worklist-pop :
      ∀ {hv : HeapView} prog fs s slot w → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (worklist-pop slot)
      → slot < frame-slots (falloc fs)
      → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ just w
      → BlockStep hv prog fs s (worklist-pop slot)
    -- The two STACK WRITES: in-frame (D085) plus the heap disjointness, which
    -- is where a slot store differs from a slot read — the abstract write goes
    -- to the stack and must be shown not to disturb a live heap cell.
    bs-store-at-slot :
      ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (store-at-slot slot)
      → slot < frame-slots (falloc fs)
      → (∀ hl' → HDom hv hl' → (rreg s sp-reg + slot * slot-size ≡ haddr hv hl') → ⊥)
      → BlockStep hv prog fs s (store-at-slot slot)
    bs-worklist-push :
      ∀ {hv : HeapView} prog fs s slot → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (worklist-push slot)
      → slot < frame-slots (falloc fs)
      → (∀ hl' → HDom hv hl' → (rreg s sp-reg + slot * slot-size ≡ haddr hv hl') → ⊥)
      → BlockStep hv prog fs s (worklist-push slot)
    -- …and the four INDIRECT WRITES. The heap branches take the `store-guard`
    -- equation (this module's own helper — the guard IS arch-free); the stack
    -- branches take the disjointness instead, at their own slot.
    bs-store-indirect :
      ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just store-indirect
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
      → HDom hv hl
      → writeLoc (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)
        ≡ writeLocToHeap (floc fs) hl (readReg (regs (floc fs)) Output)
      → BlockStep hv prog fs s store-indirect
    bs-store-indirect-stack :
      ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just store-indirect
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
      → f ≡ current-frame (falloc fs)
      → k < frame-slots (falloc fs)
      → (∀ hl' → HDom hv hl' → (rreg s sp-reg + k * slot-size ≡ haddr hv hl') → ⊥)
      → BlockStep hv prog fs s store-indirect
    bs-store-indirect-suc :
      ∀ {hv : HeapView} prog fs s hl → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just store-indirect-suc
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
      → HDom hv (sucHL hl)
      → writeLoc (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)
        ≡ writeLocToHeap (floc fs) (sucHL hl) (readReg (regs (floc fs)) Output)
      → BlockStep hv prog fs s store-indirect-suc
    bs-store-indirect-suc-stack :
      ∀ {hv : HeapView} prog fs s f k → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just store-indirect-suc
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
      → f ≡ current-frame (falloc fs)
      → suc k < frame-slots (falloc fs)
      → (∀ hl' → HDom hv hl' → (rreg s sp-reg + suc k * slot-size ≡ haddr hv hl') → ⊥)
      → BlockStep hv prog fs s store-indirect-suc
    ------------------------------------------------------------------
    -- GROUP 3b, the band's other half — CONTROL, the two counters, and the
    -- two frame markers.
    --
    -- THE LABEL PREMISE IS THE ABSTRACT SCAN ONLY. `FlatMachine.find-label`,
    -- qualified because this module's own `find-label` parameter is the
    -- CONCRETE program's scan — a different function over a different type,
    -- and confusing them is exactly the kind of slip the record exists to
    -- prevent. The engine passes the abstract one and nothing else, so that is
    -- the field. That the concrete scan AGREES is a theorem
    -- (`FlatComposition.find-label-corr`, already generic), which the arch
    -- applies inside its own block-step — x86-64 does; riscv64 currently takes
    -- it as a premise instead, which is riscv64's to fix, not the field's.
    --
    -- FIVE CONTROL FIELDS FOR THREE INSTRUCTIONS, again because the engine
    -- splits: a branch whose label is MISSING but which is NOT TAKEN never
    -- consults the label, so it is an ordinary fall-through step with no label
    -- premise at all (`…-nz`). Only taken-and-missing halts, and that is a
    -- stuck route, not a block-step.
    ------------------------------------------------------------------
    bs-c-jmp :
      ∀ {hv : HeapView} prog fs s n j → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp n))
      → FlatMachine.find-label {FS} prog n ≡ just j
      → BlockStep hv prog fs s (instr-ctrl (c-jmp n))
    bs-c-branch-scratch-zero :
      ∀ {hv : HeapView} prog fs s n k j → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
      → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
      → FlatMachine.find-label {FS} prog n ≡ just j
      → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    bs-c-branch-nz :
      ∀ {hv : HeapView} prog fs s n m → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero n))
      → readReg (regs (floc fs)) Scratch ≡ SV-Tag (suc m)
      → BlockStep hv prog fs s (instr-ctrl (c-branch-scratch-zero n))
    -- The tag branch reads its condition THROUGH a pointer, so it carries the
    -- concrete read as well — at the address the Input1 register holds, which
    -- is the generic reading of both arches' `effectiveAddr … 0`.
    bs-c-branch-tag-zero :
      ∀ {hv : HeapView} prog fs s n loc k j → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
      → readLoc (floc fs) loc ≡ just (SV-Tag k)
      → memory s (rreg s in1-reg + 0) ≡ just k
      → FlatMachine.find-label {FS} prog n ≡ just j
      → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    bs-c-branch-tag-nz :
      ∀ {hv : HeapView} prog fs s n loc m → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero n))
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
      → readLoc (floc fs) loc ≡ just (SV-Tag (suc m))
      → memory s (rreg s in1-reg + 0) ≡ just (suc m)
      → BlockStep hv prog fs s (instr-ctrl (c-branch-tag-zero n))
    -- THE TWO COUNTERS. Both are `add`/`sub` sites, so both pay plan 0.70's
    -- range obligation — the engine derives it from its own resource
    -- parameters and passes the result, exactly as at `load-tag-lit`. The
    -- registers are named by ROLE, which is what makes `rbx`/`s3` one field.
    bs-scratch-dec :
      ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
      → readReg (regs (floc fs)) Scratch ≡ SV-Tag k
      → 1 ≤ rreg s scratch-reg
      → rreg s scratch-reg < modulus
      → BlockStep hv prog fs s (instr-reg-op scratch-dec)
    bs-count-inc :
      ∀ {hv : HeapView} prog fs s k → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-reg-op count-inc)
      → readReg (regs (floc fs)) Count ≡ SV-Tag k
      → rreg s count-reg + 1 < modulus
      → BlockStep hv prog fs s (instr-reg-op count-inc)
    -- …AND THE TWO FRAME MARKERS, the band's top end.
    --
    -- `c-thunk` is the first field whose RESULT is not the diagonal: it
    -- DESCENDS the view, so it lands in `descend-view`, and the three
    -- ingredients of that view (`lo'` and its two bounds) are premises rather
    -- than derived — the engine computes `lo'` as a meet from the stack-room
    -- parameter and hands all three over. `frame-slots ≡ 0` is D093: a body
    -- entry is reached by a call, and `enter-call` reserves nothing.
    bs-c-thunk :
      ∀ {hv : HeapView} prog fs s n b → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk n b))
      → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
      → lo' ≤ rreg s sp-reg ∸ b * slot-size
      → b * slot-size ≤ rreg s sp-reg
      → frame-slots (falloc fs) ≡ 0
      → rreg s sp-reg < modulus
      → BlockStepAt hv (descend-view hv lo' lo'≤lo front-lo') prog fs s
                    (instr-ctrl (c-thunk n b))
    -- `c-ret` (D095): the two shapes only the RUN knows — the return stack is
    -- a cons and the released budget IS the reservation in force — plus the
    -- frame it returns into, which `RetMatch` pairs with the return stack for
    -- free. Nine parameters before the correspondence, and every one of them
    -- is a witness the engine already had to produce to reach this branch.
    bs-c-ret :
      ∀ {hv : HeapView} prog fs s b rpc rest f₀ b₀ frs
      → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
      → fret fs ≡ rpc ∷ rest
      → b ≡ frame-slots (falloc fs)
      → saved-frames (falloc fs) ≡ (f₀ , b₀) ∷ frs
      → rreg s sp-reg + b * slot-size < modulus
      -- …and NO UNSPILLED RETURN (2026-08-16). A return READS the head cell, so
      -- it needs `ret-eq`'s memory row rather than the arch's link claim. The
      -- engine derives this from `run-link-at-thunk`: a live link means the
      -- fetched instruction is a `c-thunk`, and this branch fetched a `c-ret`.
      → flink fs ≡ nothing
      → BlockStep hv prog fs s (instr-ctrl (c-ret b))
    ------------------------------------------------------------------
    -- GROUP 4 — THE LAST FIVE, and the record closes at 42.
    --
    -- WHAT IS NOT HERE, which is how the count came out exact. Five abstract
    -- instructions have block-steps in `FlatSimulation` and NO field:
    -- `alloc-stack`, `dealloc-stack`, `push-frame`, `pop-frame`,
    -- `lea-indexed`. The engine refutes every one of them (`frame-op-absurd`
    -- — the `Emitted`/`FrameFreeI` fence: `ir-to-trace` emits none). A
    -- block-step is a field only if the ENGINE CALLS IT. `instr-sigop` is
    -- absent for a different reason: it routes to the event layer, not to a
    -- block step.
    --
    -- The two literals take their range premise the way `load-tag-lit` does —
    -- the engine applies its own resource parameter and passes the result.
    ------------------------------------------------------------------
    bs-load-const :
      ∀ {hv : HeapView} prog fs s (v : Carrier) → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-load-const fits-int v)
      → v < modulus
      → BlockStep hv prog fs s (instr-load-const fits-int v)
    bs-load-const-float :
      ∀ {hv : HeapView} prog fs s (v : AgdaFloat) → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-load-const fits-float v)
      → float-bits v < modulus
      → BlockStep hv prog fs s (instr-load-const fits-float v)
    -- READ THE CALL, NOT THE NAME: this field's label premise is the CONCRETE
    -- scan — this module's `find-label` parameter — where the jump family's is
    -- the abstract one. The engine supplies it from `find-thunk-corr` and
    -- instantiates `j` to `blk-off prog j₀`; `code-eq` is what turns it into
    -- the address the load must produce (D096).
    bs-load-code-addr :
      ∀ {hv : HeapView} prog fs s n j → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-load-code-addr n)
      → find-label (compile-trace prog) (thunk n) ≡ just j
      → BlockStep hv prog fs s (instr-load-code-addr n)
    -- THE CALL (D098). The site's dataflow shape — closure pointer, code cell,
    -- the body it names — plus the descend-view quartet, which here reserves
    -- ONE slot (the return address) where `c-thunk` reserves the body's
    -- budget. The code cell's liveness is `dom-written`: the abstract machine
    -- wrote it, so the view maps it.
    bs-call :
      ∀ {hv : HeapView} prog fs s hl ℓ j → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just instr-call-closure
      → fclosure fs ≡ SV-Ptr (AtDynamic hl)
      → heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ)
      → HDom hv (sucHL hl)
      → FlatMachine.find-thunk {FS} prog ℓ ≡ just j
      → (lo' : ℕ) (lo'≤lo : lo' ≤ lo hv) (front-lo' : hfront hv ≤ lo')
      → lo' ≤ rreg s sp-reg ∸ slot-size
      → slot-size ≤ rreg s sp-reg
      -- …and NO UNSPILLED RETURN, for the same reason `c-ret` needs it: the
      -- call PUSHES a new head, so the old head must already be the memory row
      -- this step preserves. Same engine derivation (this branch fetched a
      -- `call`, not a `c-thunk`).
      → flink fs ≡ nothing
      → BlockStepAt hv (descend-view hv lo' lo'≤lo front-lo') prog fs s
                    instr-call-closure
    -- ALLOCATION, the widest field and the one a transcription slip would
    -- quietly wreck. It is wide because it EXTENDS the view, and a view
    -- extension has to know that the new block's references are fresh and its
    -- cells unwritten — hence five register-side `sv-below`s (the four
    -- abstract registers plus the closure, D097), the heap and EVERY frame's
    -- stack (D085), and the unwritten-cell fact. `room` measures the bump
    -- against the stack's HIGH-WATER MARK rather than the live `sp`, which is
    -- what makes the fresh cells provably unwritten and what retired the old
    -- `alloc-heap-fresh` postulate.
    --
    -- `cc` is NAMED because the result type uses it: the extended view is
    -- built from the correspondence's own `dom-fresh`.
    bs-alloc-heap :
      ∀ {hv : HeapView} prog fs s n → (cc : CompiledCorr hv prog fs s)
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-alloc-heap n)
      → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input1)
      → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Input2)
      → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Scratch)
      → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) Count)
      → sv-below (next-heap-ref (falloc fs)) (fclosure fs)
      → (∀ hl → HDom hv hl → svm-below (next-heap-ref (falloc fs)) (heapMem (floc fs) hl))
      → (∀ (f : FrameSemantics.Frame FS) (k : Slot)
           → svm-below (next-heap-ref (falloc fs)) (stackMem (floc fs) f k))
      → (∀ hl → ref-id (heap-ref hl) ≡ next-heap-ref (falloc fs)
              → heapMem (floc fs) hl ≡ nothing)
      → (room : hfront hv + slots n ≤ lo hv)
      → lo hv < modulus
      → BlockStep (extend-view hv (next-heap-ref (falloc fs)) n
                               (dom-fresh (dataCorr cc)) room)
                  prog fs s (instr-alloc-heap n)
open BlockSteps public
