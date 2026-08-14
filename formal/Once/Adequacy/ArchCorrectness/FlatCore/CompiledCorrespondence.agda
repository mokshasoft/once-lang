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
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (RegRoles)
open import Data.Nat using (NonZero)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label)

module Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
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
  where

open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fpc; fret; falloc)
open MemOps {FS} using (writeLoc; writeLocToHeap)
open FlatMachine {FS} using (floc; halted; fetch)
open import Once.Memory.HeapAddress using (HeapLocation)
open import Data.Nat using (zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (<-irrefl; <-transˡ; ≤-trans; m≤m+n)
open import Data.List using (List; []; _∷_; drop)
open import Data.List.Properties using (drop-[])
open import Data.Maybe using (nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong)
open import Once.CCC.Label using (LabelId; thunk)

import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
-- PRIVATE: an instance re-opened publicly would clash with the `C` every arch
-- already binds for its own `FlatCorrespondence` instance. Only the record
-- below is exported.
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted

open CFC using (HeapView; FlatCorr; RetAddrs; frames-of; caddr)
open RegRoles roles using (sp-reg)

------------------------------------------------------------------------
-- THE COMPILED CORRESPONDENCE.
------------------------------------------------------------------------
record CompiledCorr (hv : HeapView) (prog : AbstractTrace)
                    (fs : FlatState) (s : State) : Set where
  field
    dataCorr : FlatCorr hv fs s
    pc-off   : xpc s ≡ blk-off prog (fpc fs)
    ret-eq   : RetAddrs (blk-off prog) (memory s) (frames-of (falloc fs)) (fret fs)
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
open BlockSteps public
