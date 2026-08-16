-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.RunWF
--
-- THE FLAT MACHINE'S WELL-FORMEDNESS LAYER, arch-generic
-- (Plan 0.65 G1d, 2026-08-12).
--
-- Everything a REACHABLE state of an EMITTED program satisfies, driven by
-- `RunAt`: the segment discipline (`SegWF`, `RetMatch`, `run-seg-wf`), the two
-- pointer invariants (`StackPtrWF` via `stack-ptr-step`, `PtrBoundsWF` via
-- `ptr-bounds-step`), the shape-table consistency (`run-shape-check`), and the
-- dataflow disciplines the correspondence consumes at its load/store/branch
-- sites (`slot-read-*`, `{load,store}-indirect{,-suc}-target-*`,
-- `branch-tag-scrutinee-wf`).
--
-- WHY IT IS HERE. It was 1,076 of `X86-64.ConcFlatSim`'s 2,832 lines and it
-- mentions the machine ZERO times — no `X.State`, no register, no state
-- literal, and not even the correspondence (`FlatCorr`, `BlockStep`,
-- `HeapView` do not occur). It is about the ABSTRACT machine and the EMITTER,
-- both of which the three arches share, so it was never x86-64's to own. Ten
-- of `ConcFlatSim`'s imports are machine-specific and NONE of them is needed
-- here — that is the mechanical statement of the same fact.
--
-- The measurement also corrected the plan: `ConcFlatSim` was called "the most
-- machine-dependent, last", and it is the LEAST — 115 machine-mentioning code
-- lines out of 2,833, four percent, in two clumps with this block between them.
--
-- It also DECLARES the seven arch-generic residuals (G1d step 2), which were
-- `ConcFlatSim`'s. They are assumed once here rather than once per arch — the
-- second payoff this plan predicted for extracting a core at all. The companion
-- `RunWFTypes` module that carried them as parameters through step 1 is gone
-- with them.
------------------------------------------------------------------------


open import Once.CCC.FrameSemantics using (FrameSemantics; shift-frame; frame-word; frame-base; slot-addr; slot-addr-linear)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL; heap-offset; heap-ref; ref-id)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Label using (once; LabelId)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _∸_; _≡ᵇ_; _⊓_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; <-transˡ; <-irrefl; m≤m+n; m≤n+m; m∸n≤m
                                      ; ⊓-glb; m⊓n≤m; m⊓n≤n; m+n≤o⇒m≤o∸n; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_)
-- …and the pieces the RESOURCE parameter's type needs. Imported UNAPPLIED, so
-- the module's own `FS`/`word-eq` can be threaded into them by Agda's
-- telescoping (`RC.RunAt o FS word-eq …`) — a parameter's type is elaborated
-- before the body, where the applied `open import … FS word-eq` has not run.
open import Data.Maybe using (just)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; instr-alloc-heap; instr-ctrl; c-thunk; instr-call-closure)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CanonicalName using (CanonicalName)

open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no; Dec)

module Once.Adequacy.ArchCorrectness.FlatCore.RunWF
  (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where


open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeLoc-halted; readLoc)
open FrameSemantics FS using (Frame)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Machine.FlatStoreWF FS
open import Once.CCC.Machine.FlatRegTagWF FS
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Once.CCC.Codegen.IRToTrace o using (ir-to-trace; ir-stack-budget)
open import Once.CCC.Machine.FrameFree
open import Data.List.Relation.Unary.All using () renaming (All to AllL; [] to allL-[]; _∷_ to _allL∷_)
open import Once.CCC.Machine.InstrSlot
open import Once.CCC.Machine.FlatStackSlot FS
open import Once.CCC.Machine.FlatStackPtr FS
open import Once.CCC.Machine.FlatPtrBounds FS
open import Once.CCC.Codegen.FrameFreeTrace o
open import Once.CCC.Codegen.AllocMin o
open import Once.CCC.Codegen.ShapeTable as ST
open ST.Sem FS using (Meets; site-load-ptr; site-branch-tag; site-store-ptr; fetch-at-pc; site-slot-written)
open import Once.CCC.Codegen.LabelScope o
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.CCC.Codegen.SlotBudget o
open import Once.IR using (IR; Unit)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts)
open import Once.Type using (fits-int; fits-float)
open import Once.Word using (Carrier)
open import Once.Target.Symbol using (once-symbol-path)
open import Data.Product using (uncurry)

-- NON-HALTING ⇒ NON-CALL: `call-sym` is the ONLY instruction `matchCall` accepts,
-- and `execInstr (call-sym _)` always sets `halted := true`. So any step that
-- leaves the machine running (`halted s₁ ≡ false`) cannot have been a `call-sym`,
-- i.e. `matchCall j ≡ nothing`. (The one absurd case is `call-sym`, ruled out by
-- the halt clash; every other instruction is `matchCall … = nothing` definitionally.)
-- NOT `public`: `ConcFlatSim` already re-exports `RunContext` through its own
-- arch wrapper, and two public routes to one definition is a clash.
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq

------------------------------------------------------------------------
-- THE ARCH-GENERIC RESIDUALS (Plan 0.65 G1d step 2, 2026-08-12).
--
-- These seven were declared in `X86-64.ConcFlatSim`, and the block's own
-- comments already said why that was the wrong home: "No `X.State` in the
-- type: this is a fact about the ABSTRACT machine". Checked mechanically, not
-- taken on the comment's word — none of the seven mentions `X.State`,
-- `HeapView`, `RTx` or the correspondence in its TYPE (the flag that first
-- fired on `call-site-shape` was its own prose).
--
-- Left where they were, riscv64 and x86-32 would each have had to declare
-- their own copy of each, and the ledger would have grown threefold for facts
-- that are one fact. Here they are assumed ONCE and, when discharged,
-- discharged once for all three arches — the second payoff this plan predicted
-- for extracting a core at all.
--
-- The two that stayed behind are `arith-sigop-contract` and
-- `external-sigop-contract`: both quantify over `HeapView` and the x86-64
-- arith runtime, so they are genuinely x86-64's.
------------------------------------------------------------------------
postulate
  call-site-shape : ∀ prog (fs : FlatState) → RunAt prog fs
                  → fetch prog (fpc fs) ≡ just instr-call-closure
                  → Σ HeapLocation (λ hl → Σ LabelId (λ ℓ → Σ ℕ (λ j →
                      (fclosure fs ≡ SV-Ptr (AtDynamic hl))
                      × (heapMem (floc fs) (sucHL hl) ≡ just (SV-Code ℓ))
                      × (find-thunk prog ℓ ≡ just j))))

  -- (`events-running-thunk` LIVED HERE. It is now a THEOREM — `thunk-step`
  -- below.)
  --
  -- THE RETURN'S TWO INPUTS (D095). `events-running-ret` is GONE — the
  -- correspondence for `c-ret` is now the theorem `ret-step` below, built on
  -- the proven `block-step-c-ret`. What is left are two facts about the
  -- ABSTRACT machine running an EMITTED program; neither mentions `X.State`,
  -- so neither is a correspondence gap.
  --
  -- (1) A REACHABLE RETURN OWES A RETURN. A `c-ret` sits inside a closure body,
  -- and a body is entered only by a CALL, which pushes. (This is `ret-site-owes`
  -- from D091 — the same statement, but now TRUE-and-provable rather than
  -- colliding with `run-no-ret`: the call is modelled.) Route: the static
  -- segment stack and the dynamic `fret` have the same depth (with the same
  -- one-instant exception `SegCur` already names), and `SlotBudget`'s
  -- neutrality says an emitted body is a matched `c-thunk`/`c-ret` bracket —
  -- so at a `c-ret` the static stack is non-empty, hence so is `fret`.
  ret-site-owes : ∀ prog (fs : FlatState) (b : ℕ) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                → Σ ℕ (λ rpc → Σ (List ℕ) (λ rest → fret fs ≡ rpc ∷ rest))

  -- THE EMITTER'S GUARD (D094): in an emitted trace a `c-thunk` is at `suc q`
  -- with a `c-jmp` at `q` — the jump that stops the parent falling into the
  -- body. CODEGEN-class (only `ir-to-trace` in the type). Discharge: the
  -- structural induction over `ir-to-trace'`, shape written up in D094.
  emitted-thunk-guarded : ∀ (ir : IR Unit Unit) (p : ℕ) (ℓ : LabelId) (bb : ℕ)
                        → fetch (ir-to-trace ir) p ≡ just (instr-ctrl (c-thunk ℓ bb))
                        → Σ ℕ (λ q → (p ≡ suc q)
                              × Σ LabelId (λ m → fetch (ir-to-trace ir) q
                                                   ≡ just (instr-ctrl (c-jmp m))))

  -- …and its sibling (D096): an emitted code address names a body that EXISTS.
  -- `ir-to-trace'`'s `curry` clause emits `instr-load-code-addr (ℓ o this)` and
  -- `c-thunk (ℓ o this)` together, so the scan cannot miss. CODEGEN-class, and
  -- it belongs in the same induction as the two above.
  emitted-code-addr-has-body : ∀ (ir : IR Unit Unit) (p : ℕ) (ℓ : LabelId)
                             → fetch (ir-to-trace ir) p ≡ just (instr-load-code-addr ℓ)
                             → Σ ℕ (λ j → find-thunk (ir-to-trace ir) ℓ ≡ just j)

  -- (2) THE BRACKET: the budget a return RELEASES is the reservation in force.
  -- `ir-to-trace'` emits `c-thunk ℓ bb … c-ret bb` — one `bb`, written twice —
  -- so this is the emitter's own bracket, and it belongs with
  -- `emitted-thunk-guarded` in the same induction over `ir-to-trace'`.
  ret-budget-matches : ∀ prog (fs : FlatState) (b : ℕ) → RunAt prog fs
                     → fetch prog (fpc fs) ≡ just (instr-ctrl (c-ret b))
                     → b ≡ frame-slots (falloc fs)

  -- THE BRANCH SCRUTINEE DISCIPLINE (D073, replaces `branch-tag-badptr` +
  -- `branch-tag-bad`): at an emitted `c-branch-tag-zero` site the scrutinee
  -- register holds a live heap pointer to a WRITTEN TAG cell — codegen only
  -- emits the tag branch right after loading a constructed node's pointer.
  -- The old pair asserted a RUN-EVENTS equation for the divergent routes,
  -- which is closable by NO layout choice (D054 literals are arbitrary words,
  -- so a non-pointer's encoding can always collide with a mapped address);
  -- this is the honest dataflow fact instead, in the
  -- `store-indirect-inbounds` mold. Discharge trajectory: a per-site
  -- register-shape invariant (static expectation at each emitted site +
  -- preservation, the FlatStackPtr pattern).
  -- PLAN 0.62's TWO OBLIGATIONS (the dataflow disciplines' discharge now
  -- routes through the typed shape checker; these are the remaining named
  -- milestones — their TYPES are the M2b/M3 specs):
  --
  -- M2b — THE EMITTER SHAPE CHECK: for a heap-moded IR, the typed
  -- expectation checker accepts the emitted trace (some label environment —
  -- the cata/case loop invariants — makes every site and control transfer
  -- check). Discharge: the FrameFreeTrace/SlotBudget-mold walk over
  -- `ir-to-trace'`, `check-++` at every splice, the G2 invariants as the
  -- LabelEnv values.
  emitted-shape-check : ∀ (ir : IR Unit Unit) → HeapModed ir
                      → Σ LabelEnv (λ env →
                          check-shapes env (entry-expect Unit) (ir-to-trace ir) ≡ true)
  -- M3 — RUN CONSISTENCY: a reachable state of a CHECKED program meets the
  -- scanned expectation at its pc. Discharge: induction on `Reachable`
  -- (entry: the D074 all-tag state meets `entry-expect Unit` via `rs-unit`;
  -- step: per-instruction transfer soundness — the `shape-uw`/
  -- `meets-cell-uw` store bricks, `sub-expect-sound` at control).
  run-meets : ∀ prog (fs : FlatState) → RunAt prog fs → (env : LabelEnv)
            → check-shapes env (entry-expect Unit) prog ≡ true
            → Meets (state-at env (entry-expect Unit) prog (fpc fs)) fs
  -- `branch-tag-label-miss` RETIRED 2026-08-01 — a theorem now (`go-miss` in
  -- `tag-branch-step`): not-taken rides the label-free
  -- `block-step-c-branch-tag-nz`, taken-plus-missing is the je-halt template
  -- on `find-label-none-corr`, and the bad-read routes fold into
  -- `branch-tag-bad` (they never depended on the label).


  -- `stack-ptr-case` / `ptr-bounds-case` RETIRED with item 6: the case steps
  -- of both invariants are absurd on `FrameFreeI` now.

  -- The load/branch DISCIPLINE residuals are GONE (Plan 0.62 wiring,
  -- 2026-08-02): `load-indirect{,-suc}-target-ptr` and
  -- `branch-tag-scrutinee-wf` are now THEOREMS below, derived from
  -- `emitted-shape-check` + `run-meets` + the checker's site extraction.
  -- `store-indirect{,-suc}-bad` RETIRED 2026-08-03: the divergent route (a
  -- store through a NON-pointer) is unreachable in emitted code — the
  -- shape checker's store-site discipline (`is-fresh`) makes it absurd.
  -- See `store-indirect{,-suc}-target-ptr` below.

  -- A slot the emitted code READS is frame-live (`slot < frame-slots`): reads stay
  -- inside the frame the prologue reserved. Conditioned on the SITE (a property of
  -- emitted programs, not of arbitrary states) and covering the empty case too —
  -- which used to be what let the empty-slot reads be proved via
  -- `slot-empty-stop`. That lemma is GONE (Plan 0.54 rung D): the empty case is
  -- now UNREACHABLE instead, because `site-ok` requires a claim at every slot
  -- read and `MeetsSlot` refutes a claim at an unwritten slot. The slot MUST be the fetched instruction's own
  -- (`slot-of i ≡ just slot`): quantified over an unrelated `slot` this claims
  -- `slot < frame-slots` for every slot, which is inconsistent (take `slot ≡
  -- frame-slots`) — it would prove the whole correspondence vacuously.
  -- MEMORY EXHAUSTION (plan 0.54 rung D) — the price of "the two regions grow
  -- towards each other", and the ONLY thing the layout separation assumes. The
  -- ONE allocating instruction the emitter produces has room between the heap
  -- frontier and the stack's high-water mark; the
  -- disjointness facts that used to be postulated are derived from the carried
  -- `sep` these keep true. A real runtime failure mode (OOM / stack overflow),
  -- not a claim about addresses — the same class as the `conc-fuel` step budget.
  -- Plan 0.54 rung D step 3: the heap's room is measured against the stack's
  -- HIGH-WATER MARK, not the current `%rsp` — a region the stack has already
  -- visited keeps its (dead) contents, so only the VIRGIN part of the gap is
  -- available. That is also what discharges the fresh block's freshness on the
  -- concrete side, which is why `alloc-heap-fresh-x86` is gone.
  -- (`heap-room` is a MODULE PARAMETER now — see the header. It was the one
  -- resource bound stated inside the correspondence rather than at the apex
  -- beside `conc-fuel`.)
  -- RETIRED 2026-07-31 (plan 0.54 rung D, item 2): `stack-room` / `frame-room` /
  -- `pop-room`, and the alloc-stack FRESH-FRAME pair `alloc-stack-fresh-{abs,x86}`
  -- together with `alloc-stack-entry`, all conditioned a frame-op site — and an
  -- EMITTED program has none (`FrameFree` / `frame-op-absurd`). The fresh-frame
  -- pair was the one place where the correspondence assumed something FALSE of a
  -- re-entered frame (both halves false, agreeing); it is gone with its site.
  -- RETIRED 2026-07-30 (plan 0.54 rung D step 3): "the fresh block is UNWRITTEN on
  -- the concrete side" was `alloc-heap-fresh-x86`, and stated over the region at or
  -- above `%r15` it was FALSE — a deep call that returns leaves written cells below
  -- the current `%rsp`, and the heap can bump into them. It is now a THEOREM about
  -- the region the stack has never reached: `FlatCorr.untouched` on
  -- `[hfront, lo)`, which `heap-room` puts the fresh cells inside.
  -- (Its abstract counterpart — nothing references or has written the not-yet-
  -- allocated block — was already PROVEN, `FlatStoreWF`.)
  -- `lea-indexed-wf` RETIRED 2026-08-01: `lea-indexed` has NO PRODUCER — the
  -- cata codegen walks heap-LINKED stacks (`push2`/`pop2`; IRToTrace says
  -- "NOT lea-indexed") — so it joined `FrameFreeI`'s ⊥ set and its dispatch
  -- route is `⊥`-elim. The cursor-discipline residual died with its site.

  -- RETIRED 2026-07-31 (plan 0.54 rung D, item 2): the MATCHED PROLOGUE/EPILOGUE
  -- family — `dealloc-stack-restores`, `pop-frame-restores`, `dealloc-stack-full`,
  -- `pop-frame-empty`, `pop-frame-saved`. Each was a pairing property of emitted
  -- code at a frame-op site, and emitted code contains no frame op.
  -- `load-const-float` RETIRED 2026-08-03 (D079): a float CONSTANT is a
  -- 64-bit pattern, so codegen emits it as an ordinary immediate instead of
  -- `ud2` — both machines now load the same word and continue. (Float
  -- ARITHMETIC remains unsupported; that is a separate, unemitted path.)

  -- ARITH SIGOP interpretation contract (D061): the internal-producer obligation,
  -- discharged OFFLINE from the arith proofs (dispatch-arith-preserves + arith-block-
  -- correct). For a Pure SigOp, the arith-env maps its symbol to the block `pl`, and
  -- dispatching `pl` yields the CompiledCorr of the flat post-state. `sigop-step` proves
  -- the run-events mechanics AROUND this (pc-alignment + run-events-arith), so this
  -- states exactly the residual arith obligation — nothing about the machine loop.


--
-- `FrameFreeI` (`Once.CCC.Machine.FrameFree`) and its emitter induction live
-- below this layer
-- (`Once.CCC.Codegen.FrameFreeTrace`) — this is a fact about `ir-to-trace`, not
-- about the machine. Here it is only APPLIED, at the `Emitted` witness the run
-- context already carries.
-- Plan 0.63 step 2b: also needs HEAP MODE, because `lea-slot` joined the ⊥
-- set — it is emitted, but only by the four Stack-mode clauses. `RunAt`
-- carries `run-heap`, so every call site already has the evidence.
-- Plan 0.63 (the flip): this now yields the EMITTER FENCE (`EmittableI`), not
-- semantic frame-freeness — an emitted trace really does contain the two
-- closure markers, and they really do move the frame. The fossils are
-- unchanged, so every ⊥-route below still closes; what changed is that the
-- markers now need REAL clauses instead of `⊥-elim`.
frame-op-absurd : ∀ prog (fs : FlatState) (i : AbstractInstr) (em : Emitted prog)
                → HeapModed (proj₁ em)
                → fetch prog (fpc fs) ≡ just i → EmittableI i
frame-op-absurd .(ir-to-trace ir) fs i (ir , refl) hm ftq = fetch-frame-free {FS} ir hm ftq


------------------------------------------------------------------------
-- SLOT LIVENESS IS NOW A THEOREM (plan 0.54 rung D, item 2).
--
-- `slot-read-in-frame` used to be the residual that carried the whole slot
-- cluster (`load-from-slot`, `store-at-slot`, `restore-input`, `worklist-*`,
-- `lea-indexed`). It splits cleanly into a MACHINE fact and an EMITTER fact:
-- the live window never moves during a run, and it started out big enough.
------------------------------------------------------------------------

-- THE EMITTER HALF: every slot an emitted instruction addresses is below the
-- reservation IN FORCE AT ITS POSITION (`ir-to-trace'` threads the frontier and
-- hands it back as `ir-stack-budget`; a `c-thunk` inside the trace switches to
-- the body's). Proved in the codegen layer — see `SlotBudget.SegOK`.
--
-- Plan 0.63 (2b): the bound is POSITIONAL now, because with closure bodies
-- inlined a single budget per trace is false. `fetch` is the frame-semantics-
-- parameterised copy of the codegen layer's `trace-lookup`, so they bridge by
-- an induction on the trace.
fetch≡lookup : ∀ (t : AbstractTrace) (k : ℕ) → fetch t k ≡ trace-lookup t k
fetch≡lookup []       _       = refl
fetch≡lookup (i ∷ is) zero    = refl
fetch≡lookup (i ∷ is) (suc k) = fetch≡lookup is k

emitted-slot-below-budget : ∀ (ir : IR Unit Unit) (k : ℕ) (i : AbstractInstr) (slot : Slot)
                          → fetch (ir-to-trace ir) k ≡ just i → slot-of i ≡ just slot
                          → slot < cur (seg-at (ir-to-trace ir) k (mkSeg (ir-stack-budget ir) []))
emitted-slot-below-budget ir k i slot ftq soq =
  emitted-slot-seg ir k i slot (trans (sym (fetch≡lookup (ir-to-trace ir) k)) ftq) soq

-- THE SEGMENTATION IS STILL CONSTANT — for exactly as long as no emitted trace
-- contains a marker. `FrameFreeI` puts `c-thunk`/`c-ret` in its ⊥ set (they
-- MOVE THE FRAME), and `ir-to-trace-frame-free` says a heap-moded emitted trace
-- has none, so `seg-at` is the identity and the positional bound collapses to
-- the flat one. THIS IS THE BRIDGE THE FLIP REPLACES: once bodies are inlined
-- the fold genuinely varies, and what takes its place is the per-pc invariant
-- plus label scoping (a jump inside a body lands inside that body's segment).
-- ENUMERATED, like `stack-ptr-step`: a catchall would leave `seg-action i`
-- stuck on the variable, and neither classifier can be read off the other
-- without the split.
ff→seg-id : ∀ (i : AbstractInstr) → FrameFreeI i → is-id? (seg-action i) ≡ true
ff→seg-id (instr-ctrl (c-thunk _ _))          ()
ff→seg-id (instr-ctrl (c-ret _))              ()
ff→seg-id (instr-ctrl (c-label _))            _ = refl
ff→seg-id (instr-ctrl (c-jmp _))              _ = refl
ff→seg-id (instr-ctrl (c-branch-scratch-zero _)) _ = refl
ff→seg-id (instr-ctrl (c-branch-tag-zero _))  _ = refl
ff→seg-id mov-to-output                       _ = refl
ff→seg-id mov-to-input                        _ = refl
ff→seg-id mov-output-to-input2                _ = refl
ff→seg-id mov-input2-to-output                _ = refl
ff→seg-id load-indirect                       _ = refl
ff→seg-id load-indirect-suc                   _ = refl
ff→seg-id (load-from-slot _)                  _ = refl
ff→seg-id (store-at-slot _)                   _ = refl
ff→seg-id store-indirect                      _ = refl
ff→seg-id store-indirect-suc                  _ = refl
ff→seg-id (lea-slot _)                        _ = refl
ff→seg-id (lea-indexed _)                     _ = refl
ff→seg-id (restore-input _)                   _ = refl
ff→seg-id (instr-alloc-stack _)               _ = refl
ff→seg-id (instr-dealloc-stack _)             _ = refl
ff→seg-id (instr-reclaim-to _)                _ = refl
ff→seg-id (instr-push-frame _)                _ = refl
ff→seg-id instr-pop-frame                     _ = refl
ff→seg-id instr-call-closure                  ()
ff→seg-id (worklist-init _)                   _ = refl
ff→seg-id (worklist-push _)                   _ = refl
ff→seg-id (worklist-pop _)                    _ = refl
ff→seg-id (worklist-check _)                  _ = refl
ff→seg-id (instr-sigop _)                     _ = refl
ff→seg-id (instr-load-const _ _)              _ = refl
ff→seg-id (instr-load-code-addr _)            _ = refl
ff→seg-id instr-save-closure-reg              _ = refl
ff→seg-id (instr-load-tag-lit _)              _ = refl
ff→seg-id (instr-case-on-tag _ _)             _ = refl
ff→seg-id (instr-alloc-heap _)                _ = refl
ff→seg-id (instr-loop _)                      _ = refl
ff→seg-id (instr-reg-op _)                    _ = refl

-- …and the CALL's segment fact, standalone now that it has left `FrameFreeI`
-- (D092). The static segment does NOT move at a call: the reservation belongs
-- to the body's own `c-thunk` marker (D086), which is the next instruction the
-- callee runs. This is what pairs the caller's frame with the segment in force
-- at the pc it will return to — i.e. what `RetMatch` records at the push.
call-seg-id : is-id? (seg-action instr-call-closure) ≡ true
call-seg-id = refl

-- (`ff→idle` / `idle-seg-at` / `emitted-seg-const` are GONE with the flip.
-- They said "an emitted trace never moves the segment", which is exactly what
-- stopped being true: closure bodies are inline, so an emitted trace contains
-- the two markers and the segmentation genuinely varies along it. Everything
-- that leant on them is now proved per-instruction below — the last of them,
-- the JUMP case, is the label-scoping obligation.)

-- (An `emitted-jump-in-segment` POSTULATE stood here while the flip was being
-- measured. It is now the PROVED `LabelScope.emitted-jump-in-segment`, wired
-- into the jump clause below — so the scaffolding is deleted rather than left
-- beside its theorem.)

------------------------------------------------------------------------
-- THE FRAME STACK AND THE RETURN STACK ARE ONE STACK (Plan 0.63).
--
-- `c-thunk` pushes the caller's frame while `instr-call-closure` pushes the
-- return pc; `c-ret` pops both. So they have the same length, and — the part
-- that makes the SEGMENTED budget survive a return — each saved frame's
-- reservation is the segment in force at the pc it will return to. Without
-- that second half, `c-ret` restores a slot count from `saved-frames` and
-- lands the pc at a return address with NOTHING relating the two, and
-- `run-stack-slot` below cannot be re-established.
--
-- A DATATYPE (not a `with`-free function on two lists) so the cons/nil cases
-- compose at the pushes and pops the markers produce.
------------------------------------------------------------------------
data RetMatch (prog : AbstractTrace) (B : ℕ) : List (Frame × ℕ) → List ℕ → Set where
  rm-[]  : RetMatch prog B [] []
  rm-∷   : ∀ {f b rpc frs rs}
         → b ≡ cur (seg-at prog rpc (mkSeg B []))
         -- …and WHERE THE RETURN ADDRESS CAME FROM (D094): one past a CALL,
         -- because the call is the only pusher. That is what says a return
         -- lands after a call site rather than anywhere — in particular never
         -- on a body entry, whose predecessor is a `c-jmp`.
         → Σ ℕ (λ q → (rpc ≡ suc q) × (fetch prog q ≡ just instr-call-closure))
         → RetMatch prog B frs rs
         → RetMatch prog B ((f , b) ∷ frs) (rpc ∷ rs)

-- THE RESERVATION IN FORCE, and its ONE EXCEPTION (D092).
--
-- Normally the current frame's reservation IS the static segment at the pc.
-- The exception is the instant a CALL has landed on a body entry: the frame it
-- entered reserves NOTHING (D086 — the body's `c-thunk` marker has not run
-- yet), while the positional scan still reads the CALLER's segment, because
-- bodies are spliced inline and the scan walks the trace in order.
--
-- Naming that state precisely is what keeps the invariant both TRUE and
-- USABLE: the exception's pc holds a `c-thunk`, which addresses no slot, so
-- every consumer (all of them slot reads) refutes it from the instruction it
-- already has. Weakening the equation to "…or the frame is empty" would have
-- been unusable — a consumer cannot refute that.
SegCur : AbstractTrace → ℕ → FlatState → Set
SegCur prog B fs =
  (frame-slots (falloc fs) ≡ cur (seg-at prog (fpc fs) (mkSeg B [])))
  ⊎ (Σ LabelId (λ ℓ → Σ ℕ (λ bb →
       (fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb)))
       × (frame-slots (falloc fs) ≡ 0))))

-- THE RUN INVARIANT, per frame. `seg-cur` is what `slot-read-in-frame`
-- consumes; `seg-stack` is what a return consumes. One induction.
record SegWF (prog : AbstractTrace) (B : ℕ) (fs : FlatState) : Set where
  constructor mkSegWF
  field
    seg-cur   : SegCur prog B fs
    seg-stack : RetMatch prog B (saved-frames (falloc fs)) (fret fs)
    -- A BODY ENTRY IS REACHED WITH AN EMPTY RESERVATION (D094). The frame a
    -- `c-thunk` deepens is the one a CALL entered, and `enter-call` reserves
    -- nothing (D086). Every other way of arriving at a body entry is refuted:
    -- a fall-through cannot, because the emitter puts a `c-jmp` there
    -- (`emitted-thunk-guarded`); a jump cannot, because `find-label` resolves
    -- `c-label`s (`find-label-sound`, D082's disjoint provenances); and a
    -- return cannot, because its address is one past a CALL (`RetMatch`'s
    -- provenance), which is not a `c-jmp`.
    seg-entry : ∀ (ℓ : LabelId) (bb : ℕ)
              → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb))
              → frame-slots (falloc fs) ≡ 0
open SegWF public

------------------------------------------------------------------------
-- HOW THE PC MOVES, per instruction. Everything a frame-free step can be
-- either FALLS THROUGH (`flat-step-straight`, and `c-label`) or is one of the
-- three JUMPS. That split is what confines the label-scoping obligation:
-- a fall-through's segment fact is the fold's own recursion (`seg-at-suc`),
-- with nothing assumed about emitted code.
------------------------------------------------------------------------
-- where a jump can land: fall through, halt with the pc unmoved (the label
-- was not found), or at the label's resolved index. The last is the only case
-- that needs LABEL SCOPING, and carrying the target `m` here is what lets it
-- consume `emitted-jump-in-segment`.
-- the three post-pc shapes, read off `do-jump` / `do-branch`
dj-aux : ∀ (mj : Maybe ℕ) (fs : FlatState)
       → (fpc (do-jump mj fs) ≡ fpc fs)
         ⊎ (Σ ℕ (λ q → (mj ≡ just q) × (fpc (do-jump mj fs) ≡ q)))
dj-aux (just q) fs = inj₂ (q , refl , refl)
dj-aux nothing  fs = inj₁ refl

-- …and the branch, over a VARIABLE condition. Taking `b` as an argument is
-- what makes `do-branch b` reduce on the split — abstracting the scrutinee at
-- the use site does not work, because its normal form is spelled differently
-- from the source term (`readReg … Scratch` vs the field accessor).
db-aux : ∀ (b : Bool) (m : LabelId) (prog : AbstractTrace) (fs : FlatState)
       → (fpc (do-branch b m prog fs) ≡ suc (fpc fs))
         ⊎ ((fpc (do-branch b m prog fs) ≡ fpc fs)
            ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                        × (fpc (do-branch b m prog fs) ≡ q))))
db-aux false m prog fs = inj₁ refl
db-aux true  m prog fs = inj₂ (dj-aux (find-label prog m) fs)

-- "not the unconditional jump" (D094). The ONE instruction that can sit
-- immediately before a body entry is `c-jmp` — that is the guard `ir-to-trace'`
-- emits to stop the parent falling in. So every step that FALLS THROUGH has to
-- be able to say it is not one, and this is the witness. Enumerated by
-- catch-all, so it reduces to `⊤` at every concrete constructor.
NotJmpI : AbstractInstr → Set
NotJmpI (instr-ctrl (c-jmp _)) = ⊥
{-# CATCHALL #-}
NotJmpI _                      = ⊤

data JumpPost (i : AbstractInstr) (m : LabelId) (prog : AbstractTrace) (fs : FlatState) : Set where
  -- FALLING THROUGH carries `NotJmpI`: only a BRANCH falls through, and a
  -- `c-jmp` never produces this row (`dj-aux` has no fall-through case).
  jp-suc  : fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs) → NotJmpI i → JumpPost i m prog fs
  jp-halt : fpc (flat-exec-instr i prog fs) ≡ fpc fs → JumpPost i m prog fs
  jp-to   : ∀ (q : ℕ) → find-label prog m ≡ just q
          → fpc (flat-exec-instr i prog fs) ≡ q → JumpPost i m prog fs

-- Plan 0.63 (post-flip): an EMITTED instruction is one of four kinds, and the
-- markers are now among them. `pv-suc`/`pv-jump` are the frame-free ones (they
-- carry `FrameFreeI`, which is what `flat-same-frames` and the invariant
-- inductions consume); `pv-thunk`/`pv-ret` are the two that MOVE THE FRAME and
-- carry their reservation instead.
data PcView (i : AbstractInstr) : Set where
  pv-suc   : FrameFreeI i → NotJmpI i
           → (∀ prog fs → fpc (flat-exec-instr i prog fs) ≡ suc (fpc fs)) → PcView i
  pv-jump  : FrameFreeI i → ∀ (m : LabelId) → once-label-of i ≡ just m
           → (∀ prog fs → JumpPost i m prog fs) → PcView i
  pv-thunk : ∀ (ℓ : LabelId) (bb : ℕ) → i ≡ instr-ctrl (c-thunk ℓ bb) → PcView i
  pv-ret   : ∀ (bb : ℕ) → i ≡ instr-ctrl (c-ret bb) → PcView i
  -- D092: the call is the fifth kind. It moves BOTH stacks and lands the pc on
  -- a body entry, so it is neither frame-free nor a jump.
  pv-call  : i ≡ instr-call-closure → PcView i

pcView : ∀ (i : AbstractInstr) → EmittableI i → PcView i
pcView (instr-ctrl (c-label _))               _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-ctrl (c-jmp m))                 _ = pv-jump tt m refl go
  where go : ∀ prog fs → JumpPost (instr-ctrl (c-jmp m)) m prog fs
        go prog fs = mk (dj-aux (find-label prog m) fs)
          where mk : (fpc (do-jump (find-label prog m) fs) ≡ fpc fs)
                     ⊎ (Σ ℕ (λ q → (find-label prog m ≡ just q)
                                 × (fpc (do-jump (find-label prog m) fs) ≡ q)))
                   → JumpPost (instr-ctrl (c-jmp m)) m prog fs
                mk (inj₁ e)            = jp-halt e
                mk (inj₂ (q , fq , e)) = jp-to q fq e
-- the branches abstract their scrutinee WITH an equation (J-style), so the
-- goal's `do-branch <cond>` reduces on the taken/not-taken split
pcView (instr-ctrl (c-branch-scratch-zero m))     _ = pv-jump tt m refl go
  where
    go : ∀ prog fs → JumpPost (instr-ctrl (c-branch-scratch-zero m)) m prog fs
    go prog fs = mk (db-aux (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs)
      where mk : _ → JumpPost (instr-ctrl (c-branch-scratch-zero m)) m prog fs
            mk (inj₁ e)                     = jp-suc e tt
            mk (inj₂ (inj₁ e))              = jp-halt e
            mk (inj₂ (inj₂ (q , fq , e)))   = jp-to q fq e
pcView (instr-ctrl (c-branch-tag-zero m))     _ = pv-jump tt m refl go
  where
    go : ∀ prog fs → JumpPost (instr-ctrl (c-branch-tag-zero m)) m prog fs
    go prog fs = mk (db-aux (tag-zf (flat-read-tag (floc fs))) m prog fs)
      where mk : _ → JumpPost (instr-ctrl (c-branch-tag-zero m)) m prog fs
            mk (inj₁ e)                     = jp-suc e tt
            mk (inj₂ (inj₁ e))              = jp-halt e
            mk (inj₂ (inj₂ (q , fq , e)))   = jp-to q fq e
pcView (instr-ctrl (c-thunk ℓ bb))            _ = pv-thunk ℓ bb refl
pcView (instr-ctrl (c-ret bb))                _ = pv-ret bb refl
pcView (instr-alloc-stack _)                  ()
pcView (instr-dealloc-stack _)                ()
pcView (instr-push-frame _)                   ()
pcView instr-pop-frame                        ()
pcView (instr-case-on-tag _ _)                ()
pcView (instr-loop _)                         ()
pcView (lea-slot _)                           ()
pcView (lea-indexed _)                        ()
pcView mov-to-output                          _ = pv-suc tt tt (λ _ _ → refl)
pcView mov-to-input                           _ = pv-suc tt tt (λ _ _ → refl)
pcView mov-output-to-input2                   _ = pv-suc tt tt (λ _ _ → refl)
pcView mov-input2-to-output                   _ = pv-suc tt tt (λ _ _ → refl)
pcView load-indirect                          _ = pv-suc tt tt (λ _ _ → refl)
pcView load-indirect-suc                      _ = pv-suc tt tt (λ _ _ → refl)
pcView (load-from-slot _)                     _ = pv-suc tt tt (λ _ _ → refl)
pcView (store-at-slot _)                      _ = pv-suc tt tt (λ _ _ → refl)
pcView store-indirect                         _ = pv-suc tt tt (λ _ _ → refl)
pcView store-indirect-suc                     _ = pv-suc tt tt (λ _ _ → refl)
pcView (restore-input _)                      _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-reclaim-to _)                   _ = pv-suc tt tt (λ _ _ → refl)
pcView instr-call-closure                     _ = pv-call refl
pcView (worklist-init _)                      _ = pv-suc tt tt (λ _ _ → refl)
pcView (worklist-push _)                      _ = pv-suc tt tt (λ _ _ → refl)
pcView (worklist-pop _)                       _ = pv-suc tt tt (λ _ _ → refl)
pcView (worklist-check _)                     _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-sigop _)                        _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-load-const _ _)                 _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-load-code-addr _)               _ = pv-suc tt tt (λ _ _ → refl)
pcView instr-save-closure-reg                 _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-load-tag-lit _)                 _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-alloc-heap _)                   _ = pv-suc tt tt (λ _ _ → refl)
pcView (instr-reg-op _)                       _ = pv-suc tt tt (λ _ _ → refl)

-- The live stack window is the reservation IN FORCE at the current pc — the
-- CURRENT FRAME's, once frames move. Induction on `Reachable`; each step is
-- frame-free because the program is emitted (`frame-op-absurd`), so it moves
-- neither the frame stack nor the return stack (`flat-same-frames`).
--
-- THE ONE PLACE THE FLIP LANDS: the step case needs the segment in force to be
-- the same at the post-pc as at the pre-pc. Today that is `emitted-seg-const`
-- (no emitted trace holds a marker, so `seg-at` is the identity). With bodies
-- inlined it becomes two obligations — the marker steps, which move the
-- segment exactly as they move the frame, and LABEL SCOPING for the jumps.
run-seg-wf : ∀ prog (fs : FlatState) (r : RunAt prog fs)
           → SegWF prog (ir-stack-budget (run-ir r)) fs
run-seg-wf prog fs (mkRunAt ir eq hm reach) = go fs reach
  where
    B₀ = mkSeg (ir-stack-budget ir) []
    0≢suc : ∀ {n : ℕ} → 0 ≡ suc n → ⊥
    0≢suc ()
    suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
    suc-inj refl = refl
    just-injI : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
    just-injI refl = refl
    -- the emitter's guard, at THIS program
    guard : ∀ (p : ℕ) (ℓ : LabelId) (bb : ℕ)
          → fetch prog p ≡ just (instr-ctrl (c-thunk ℓ bb))
          → Σ ℕ (λ q → (p ≡ suc q)
                × Σ LabelId (λ m → fetch prog q ≡ just (instr-ctrl (c-jmp m))))
    guard p ℓ bb H =
      subst (λ pr → Σ ℕ (λ q → (p ≡ suc q)
                    × Σ LabelId (λ m → fetch pr q ≡ just (instr-ctrl (c-jmp m)))))
            (sym eq)
            (emitted-thunk-guarded ir p ℓ bb
              (subst (λ pr → fetch pr p ≡ just (instr-ctrl (c-thunk ℓ bb))) eq H))
    go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs'
       → SegWF prog (ir-stack-budget ir) fs'
    -- AT ENTRY the pc is 0 and `seg-at _ zero` is the starting state outright.
    go fs' (reach-start .fs' el eqB) =
      mkSegWF (inj₁ (subst (λ z → frame-slots (falloc fs') ≡ cur (seg-at prog z B₀))
                           (sym (proj₁ el)) eqB))
              (subst₂ (RetMatch prog (ir-stack-budget ir))
                      (sym (proj₁ (proj₂ (proj₂ (proj₂ el)))))
                      (sym (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ el))))))
                      rm-[])
              -- AT ENTRY the pc is 0, and a body entry is never at position 0
              -- (the emitter's guard sits before it).
              (λ ℓ bb H → ⊥-elim (0≢suc (proj₁ (proj₂ (guard 0 ℓ bb
                            (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb)))
                                   (proj₁ el) H))))))
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
      step (pcView i em)
      where
        em  = frame-op-absurd prog fs'' i (ir , eq) hm ftq
        ih  = go fs'' r'
        lk : trace-lookup prog (fpc fs'') ≡ just i
        lk = trans (sym (fetch≡lookup prog (fpc fs''))) ftq
        -- the segment one position along, stepped by the fetched instruction
        seg-suc : seg-at prog (suc (fpc fs'')) B₀ ≡ seg-step i (seg-at prog (fpc fs'') B₀)
        seg-suc = seg-at-suc prog (fpc fs'') B₀ lk
        -- THE PRE-STATE'S EQUATION (D092). `SegCur` has an exception row — the
        -- pc holds a body entry — and every case below is at an instruction
        -- that is NOT one, so each discharges the row from `i`'s own shape.
        ih-eq : (∀ ℓ bb → i ≡ instr-ctrl (c-thunk ℓ bb) → ⊥)
              → frame-slots (falloc fs'') ≡ cur (seg-at prog (fpc fs'') B₀)
        ih-eq nt = go-eq (seg-cur ih)
          where go-eq : SegCur prog (ir-stack-budget ir) fs''
                      → frame-slots (falloc fs'') ≡ cur (seg-at prog (fpc fs'') B₀)
                go-eq (inj₁ e) = e
                go-eq (inj₂ (ℓ , bb , tq , _)) =
                  ⊥-elim (nt ℓ bb (just-injI (trans (sym ftq) tq)))
        -- …and the two ways a case knows it is not at a body entry
        ff-not-thunk : FrameFreeI i → ∀ ℓ bb → i ≡ instr-ctrl (c-thunk ℓ bb) → ⊥
        ff-not-thunk ff ℓ bb e = subst FrameFreeI e ff
        -- D094: NO FALL-THROUGH LANDS ON A BODY ENTRY. The emitter's guard
        -- puts a `c-jmp` immediately before one, and the instruction actually
        -- fetched here is not a `c-jmp` — whoever calls this says so.
        no-fallthrough : ∀ (p : ℕ) (ℓ : LabelId) (bb : ℕ) (i' : AbstractInstr)
                       → NotJmpI i' → fetch prog p ≡ just i'
                       → fetch prog (suc p) ≡ just (instr-ctrl (c-thunk ℓ bb)) → ⊥
        no-fallthrough p ℓ bb i' nj ftq' H = clash (guard (suc p) ℓ bb H)
          where clash : Σ ℕ (λ q → (suc p ≡ suc q)
                              × Σ LabelId (λ m → fetch prog q ≡ just (instr-ctrl (c-jmp m))))
                      → ⊥
                clash (q , sq , m , fq) =
                  subst NotJmpI
                        (just-injI (trans (sym ftq')
                                          (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-jmp m)))
                                                 (sym (suc-inj sq)) fq)))
                        nj
        step : PcView i → SegWF prog (ir-stack-budget ir) (flat-exec-instr i prog fs'')
        -- FRAME-FREE, FALLING THROUGH: frames untouched, segment unmoved.
        step (pv-suc ff nj adv) =
          mkSegWF
            (inj₁ (trans (sf-slots same) (trans (ih-eq (ff-not-thunk ff)) (sym stable))))
            (subst₂ (RetMatch prog (ir-stack-budget ir))
                    (sym (sf-saved same)) (sym (sf-ret same)) (seg-stack ih))
            -- a FALL-THROUGH cannot land on a body entry: the emitter put a
            -- `c-jmp` there, and this instruction is not one.
            (λ ℓ bb H → ⊥-elim (no-fallthrough (fpc fs'') ℓ bb i nj ftq
                          (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb)))
                                 (adv prog fs'') H)))
          where
            same = flat-same-frames i prog fs'' ff
            stable : cur (seg-at prog (fpc (flat-exec-instr i prog fs'')) B₀)
                   ≡ cur (seg-at prog (fpc fs'') B₀)
            stable = cong cur (trans (cong (λ z → seg-at prog z B₀) (adv prog fs''))
                              (trans seg-suc
                                     (idle-step i (ff→seg-id i ff) (seg-at prog (fpc fs'') B₀))))
        -- FRAME-FREE JUMP: frames untouched; the segment survives by LABEL
        -- SCOPING (`LabelScope.emitted-jump-in-segment`).
        step (pv-jump ff m mlab jp) =
          mkSegWF
            (inj₁ (trans (sf-slots same)
                         (trans (ih-eq (ff-not-thunk ff)) (sym (jgo (jp prog fs''))))))
            (subst₂ (RetMatch prog (ir-stack-budget ir))
                    (sym (sf-saved same)) (sym (sf-ret same)) (seg-stack ih))
            -- THE THREE WAYS A JUMP CAN LAND, and none is a body entry: a
            -- fall-through (branch not taken) is guarded as above; a HALT
            -- leaves the pc on this very instruction, which `once-label-of`
            -- says is not a `c-thunk`; and a resolved target holds a
            -- `c-label` (`find-label-sound` — D082's disjoint provenances).
            (λ ℓ bb H → ⊥-elim (ego (jp prog fs'') ℓ bb H))
          where
            same = flat-same-frames i prog fs'' ff
            lkm : mention-at prog (fpc fs'') ≡ just m
            lkm = trans (cong mention-of lk) mlab
            jgo : JumpPost i m prog fs''
                → cur (seg-at prog (fpc (flat-exec-instr i prog fs'')) B₀)
                ≡ cur (seg-at prog (fpc fs'') B₀)
            jgo (jp-suc adv nj) =
              cong cur (trans (cong (λ z → seg-at prog z B₀) adv)
                       (trans seg-suc (idle-step i (ff→seg-id i ff) (seg-at prog (fpc fs'') B₀))))
            jgo (jp-halt e) = cong cur (cong (λ z → seg-at prog z B₀) e)
            jgo (jp-to q fq e) =
              cong cur (trans (cong (λ z → seg-at prog z B₀) e)
                        (subst (λ pr → seg-at pr q B₀ ≡ seg-at pr (fpc fs'') B₀) (sym eq)
                          (emitted-jump-in-segment {FS} ir (fpc fs'') q m B₀
                            (subst (λ pr → mention-at pr (fpc fs'') ≡ just m) eq lkm)
                            (subst (λ pr → find-label pr m ≡ just q) eq fq))))
            -- …and the same three rows, for the body-entry claim
            ego : JumpPost i m prog fs'' → ∀ ℓ bb
                → fetch prog (fpc (flat-exec-instr i prog fs''))
                    ≡ just (instr-ctrl (c-thunk ℓ bb)) → ⊥
            ego (jp-suc adv nj) ℓ bb H =
              no-fallthrough (fpc fs'') ℓ bb i nj ftq
                (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb))) adv H)
            -- the pc did not move, so the instruction there is `i` itself —
            -- and a `c-thunk` mentions no `once` label
            ego (jp-halt e) ℓ bb H = no-once (trans (sym mlab) (cong once-label-of i≡thunk))
              where i≡thunk : i ≡ instr-ctrl (c-thunk ℓ bb)
                    i≡thunk = just-injI (trans (sym ftq)
                                (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb))) e H))
                    no-once : ∀ {A : Set} → just m ≡ nothing → A
                    no-once ()
            -- a resolved jump target holds a `c-label`, never a body entry
            ego (jp-to q fq e) ℓ bb H = clash (trans (sym (find-label-sound prog m q fq))
                    (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb))) e H))
              where clash : ∀ {A : Set}
                          → just (instr-ctrl (c-label m)) ≡ just (instr-ctrl (c-thunk ℓ bb)) → A
                    clash ()
        -- THE BODY MARKER: `grow-frame bb` sets `frame-slots := bb` and the
        -- static `seg-push bb` sets `cur := bb` — they agree by construction,
        -- which is the whole point of D086 putting the PUSH at the call and
        -- only the reservation here. `saved-frames`/`fret` are untouched, so
        -- `RetMatch` rides through.
        step (pv-thunk ℓ bb ieq) =
          mkSegWF (inj₁ (trans (cong (λ z → frame-slots (falloc (flat-exec-instr z prog fs''))) ieq)
                         (sym (cong cur (trans (cong (λ z → seg-at prog z B₀) (pc-eq ieq))
                                               (trans seg-suc (step-eq ieq)))))))
                  (subst₂ (RetMatch prog (ir-stack-budget ir))
                          (sym (cong (λ z → saved-frames (falloc (flat-exec-instr z prog fs''))) ieq))
                          (sym (cong (λ z → fret (flat-exec-instr z prog fs'')) ieq))
                          (seg-stack ih))
                  -- the marker FALLS THROUGH, so the same guard applies: the
                  -- position after a body entry is not another body entry.
                  (λ ℓ' bb' H → ⊥-elim (no-fallthrough (fpc fs'') ℓ' bb' i
                                  (subst NotJmpI (sym ieq) tt) ftq
                                  (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ' bb')))
                                         (pc-eq ieq) H)))
          where
            pc-eq : i ≡ instr-ctrl (c-thunk ℓ bb)
                  → fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')
            pc-eq refl = refl
            step-eq : i ≡ instr-ctrl (c-thunk ℓ bb)
                    → seg-step i (seg-at prog (fpc fs'') B₀)
                      ≡ mkSeg bb (cur (seg-at prog (fpc fs'') B₀) ∷ saved (seg-at prog (fpc fs'') B₀))
            step-eq refl = refl
        -- THE RETURN: `leave-frame` restores the caller's count and the pc goes
        -- to the popped return address. That those two BELONG TOGETHER is
        -- exactly `RetMatch`, which is what it was built for.
        step (pv-ret bb ieq) = ret-step ieq
          where
            -- the pc has not moved, so the instruction is this `c-ret`
            ret-clash : i ≡ instr-ctrl (c-ret bb) → ∀ ℓ bb'
                      → fetch prog (fpc fs'') ≡ just (instr-ctrl (c-thunk ℓ bb')) → ⊥
            ret-clash refl ℓ bb' H = go-c (just-injI (trans (sym ftq) H))
              where go-c : instr-ctrl (c-ret bb) ≡ instr-ctrl (c-thunk ℓ bb') → ⊥
                    go-c ()
            ret-step : i ≡ instr-ctrl (c-ret bb)
                     → SegWF prog (ir-stack-budget ir) (flat-exec-instr i prog fs'')
            ret-step refl = go-rm (fret fs'') (saved-frames (falloc fs'')) refl refl (seg-stack ih)
              where
                -- J-style on BOTH stacks at once: `RetMatch` pairs them, so
                -- the length-mismatch rows are absurd and the cons row hands
                -- back exactly the two facts the post-state needs — the
                -- caller's reservation (`beq`) and the tail pairing.
                go-rm : ∀ (rs : List ℕ) (frs : List (Frame × ℕ))
                      → fret fs'' ≡ rs → saved-frames (falloc fs'') ≡ frs
                      → RetMatch prog (ir-stack-budget ir) frs rs
                      → SegWF prog (ir-stack-budget ir)
                              (flat-exec-instr (instr-ctrl (c-ret bb)) prog fs'')
                -- an empty return stack HALTS with the pc unmoved, so the
                -- caller's window is this frame's and the pairing stays empty
                go-rm [] [] req feq rm-[] =
                  mkSegWF (inj₁ (trans (cong frame-slots (do-ret-alloc fs''))
                          (trans (leave-frame-slots-[] (falloc fs'') feq)
                          (trans (ih-eq (λ _ _ ()))
                                 (cong (λ z → cur (seg-at prog z B₀))
                                       (sym (do-ret-pc-[] fs'' req)))))))
                          (subst₂ (RetMatch prog (ir-stack-budget ir))
                                  (sym (trans (cong saved-frames (do-ret-alloc fs''))
                                              (leave-frame-saved-[] (falloc fs'') feq)))
                                  (sym (do-ret-fret-[] fs'' req)) rm-[])
                          -- an empty return stack HALTS with the pc unmoved,
                          -- so the instruction there is still this `c-ret`
                          (λ ℓ bb H → ⊥-elim (ret-clash ieq ℓ bb
                                        (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb)))
                                               (do-ret-pc-[] fs'' req) H)))
                -- …and a real return takes the caller's reservation `b` and
                -- lands at `rpc`; `RetMatch` says those two belong together
                go-rm (rpc ∷ rs) ((f , b) ∷ frs) req feq (rm-∷ beq prov rest) =
                  mkSegWF (inj₁ (trans (cong frame-slots (do-ret-alloc fs''))
                          (trans (leave-frame-slots-∷ (falloc fs'') f b frs feq)
                          (trans beq (cong (λ z → cur (seg-at prog z B₀))
                                           (sym (do-ret-pc-∷ fs'' rpc rs req)))))))
                          (subst₂ (RetMatch prog (ir-stack-budget ir))
                                  (sym (trans (cong saved-frames (do-ret-alloc fs''))
                                              (leave-frame-saved-∷ (falloc fs'') f b frs feq)))
                                  (sym (do-ret-fret-∷ fs'' rpc rs req)) rest)
                          -- …and a REAL return lands one past a CALL
                          -- (`RetMatch`'s provenance), which is not the `c-jmp`
                          -- a body entry is preceded by.
                          (λ ℓ bb H → ⊥-elim
                            (no-fallthrough (proj₁ prov) ℓ bb instr-call-closure tt
                              (proj₂ (proj₂ prov))
                              (subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ bb)))
                                     (trans (do-ret-pc-∷ fs'' rpc rs req) (proj₁ (proj₂ prov)))
                                     H)))
                go-rm [] ((f , b) ∷ frs) req feq ()
                go-rm (rpc ∷ rs) [] req feq ()
        -- THE CALL (D092): it PUSHES both stacks and lands on a body entry.
        --
        -- `seg-cur` takes the EXCEPTION row: the frame `enter-call` entered
        -- reserves nothing (`refl`), and the pc holds the `c-thunk` the scan
        -- found (`find-thunk-sound`) — the body's reservation is that marker's
        -- job, one step later.
        --
        -- `seg-stack` gains a pair, and its `rm-∷` obligation is exactly what
        -- D086 was for: the caller's reservation must be the segment in force
        -- at the pc it will RETURN to. That pc is `suc (fpc fs'')` and the call
        -- is segment-idle (`call-seg-id`), so it is the caller's own segment —
        -- which the pre-state's equation supplies.
        step (pv-call ieq) = call-go ieq
          where
            call-go : i ≡ instr-call-closure
                    → SegWF prog (ir-stack-budget ir) (flat-exec-instr i prog fs'')
            call-go refl = cgo (callView prog fs'')
              where
                call-clash : ∀ {ℓ' bb'} → instr-call-closure ≡ instr-ctrl (c-thunk ℓ' bb') → ⊥
                call-clash ()
                -- the caller's reservation IS the segment at its return pc
                beq : frame-slots (falloc fs'')
                    ≡ cur (seg-at prog (suc (fpc fs'')) B₀)
                beq = trans (ih-eq (λ _ _ ()))
                            (sym (cong cur (trans seg-suc
                                   (idle-step instr-call-closure call-seg-id
                                              (seg-at prog (fpc fs'') B₀)))))
                cgo : CallPost prog fs''
                    → SegWF prog (ir-stack-budget ir) (do-call prog fs'')
                -- a malformed call HALTS: no stack moves, so both fields ride
                cgo (cp-halt e) rewrite e =
                  mkSegWF (seg-cur ih) (seg-stack ih)
                          -- the pc has not moved: this instruction is the call
                          (λ ℓ bb H → ⊥-elim (call-clash (just-injI (trans (sym ftq) H))))
                cgo (cp-enter ℓ j fteq e) rewrite e =
                  mkSegWF (inj₂ (ℓ , proj₁ landing , proj₂ landing , refl))
                          (rm-∷ beq (fpc fs'' , refl , ftq) (seg-stack ih))
                          -- …and THIS is the case the whole invariant is about:
                          -- the frame a call enters reserves nothing (D086).
                          (λ _ _ _ → refl)
                  where landing = find-thunk-sound prog ℓ j fteq

-- …and the form the correspondence consumes (D093/D094). Was a POSTULATE for
-- one commit; it is now a projection of the run invariant, which is where it
-- always belonged — the emitter's guard is the only assumption left under it.
thunk-entry-empty : ∀ prog (fs : FlatState) (ℓ : LabelId) (bb : ℕ) → RunAt prog fs
                  → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb))
                  → frame-slots (falloc fs) ≡ 0
thunk-entry-empty prog fs ℓ bb r ftq = seg-entry (run-seg-wf prog fs r) ℓ bb ftq

-- (`run-stack-slot` — "the window is the whole trace's budget" — is GONE with
-- the flip. It is FALSE inside a closure body, whose window is the body's own
-- reservation. Its consumer wants the POSITIONAL form, which `SegWF.seg-cur`
-- already is, so the two now compose with no intermediate at all.)

------------------------------------------------------------------------
-- (`run-no-ret` STOOD HERE and is now DELETED — on purpose, and it is the
-- check that D092 really landed.
--
-- It was the theorem "`fret` and `saved-frames` are empty in EVERY reachable
-- state", true only because `instr-call-closure` was the IDENTITY: nothing
-- pushed, so no closure body was ever entered and the return correspondence
-- spoke about a state that could not arise (D091). Now that the call is
-- MODELLED it pushes, the theorem is FALSE, and it stops typechecking — which
-- is exactly the signal that the machine changed. `events-running-ret` is a
-- live route again, and `ret-site-owes` — the residual that stood in for it —
-- is gone with it.)
------------------------------------------------------------------------

-- ONE FRAME-FREE STEP PRESERVES THE INVARIANT — a THEOREM for EVERY
-- constructor. Plan 0.63 step 2b SIMPLIFIED this: `lea-slot` joined
-- `FrameFreeI`'s ⊥ set (a heap-moded trace emits none), so its route is now
-- absurd like the fossils' and the whole pair-bound plumbing it used to need
-- — `emitted-lea-slot-pair`, `SlotBudget.SlotBelow`'s second field, and the
-- `run-stack-slot` transport — is gone with it.
stack-ptr-step : ∀ (i : AbstractInstr) prog (fs : FlatState) → RunAt prog fs
               → fetch prog (fpc fs) ≡ just i → EmittableI i
               → StackPtrWF fs → StackPtrWF (flat-exec-instr i prog fs)
stack-ptr-step (lea-slot slot) prog fs r ftq () wf
stack-ptr-step (lea-indexed slot) prog fs r ftq () wf
stack-ptr-step (instr-case-on-tag f g) prog fs r ftq () wf
stack-ptr-step (instr-alloc-stack n)   prog fs r ftq () wf
stack-ptr-step (instr-dealloc-stack n) prog fs r ftq () wf
stack-ptr-step (instr-push-frame cap)  prog fs r ftq () wf
stack-ptr-step instr-pop-frame         prog fs r ftq () wf
stack-ptr-step (instr-loop body)       prog fs r ftq () wf
stack-ptr-step mov-to-output prog fs r ftq ff wf =
  flat-stack-ptr mov-to-output prog fs ff wf
stack-ptr-step mov-to-input prog fs r ftq ff wf =
  flat-stack-ptr mov-to-input prog fs ff wf
stack-ptr-step mov-output-to-input2 prog fs r ftq ff wf =
  flat-stack-ptr mov-output-to-input2 prog fs ff wf
stack-ptr-step mov-input2-to-output prog fs r ftq ff wf =
  flat-stack-ptr mov-input2-to-output prog fs ff wf
stack-ptr-step load-indirect prog fs r ftq ff wf =
  flat-stack-ptr load-indirect prog fs ff wf
stack-ptr-step load-indirect-suc prog fs r ftq ff wf =
  flat-stack-ptr load-indirect-suc prog fs ff wf
stack-ptr-step (load-from-slot k) prog fs r ftq ff wf =
  flat-stack-ptr (load-from-slot k) prog fs ff wf
stack-ptr-step (store-at-slot k) prog fs r ftq ff wf =
  flat-stack-ptr (store-at-slot k) prog fs ff wf
stack-ptr-step store-indirect prog fs r ftq ff wf =
  flat-stack-ptr store-indirect prog fs ff wf
stack-ptr-step store-indirect-suc prog fs r ftq ff wf =
  flat-stack-ptr store-indirect-suc prog fs ff wf
stack-ptr-step (restore-input k) prog fs r ftq ff wf =
  flat-stack-ptr (restore-input k) prog fs ff wf
stack-ptr-step (instr-reclaim-to k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-reclaim-to k) prog fs ff wf
stack-ptr-step instr-call-closure prog fs r ftq ff wf =
  flat-stack-ptr instr-call-closure prog fs ff wf
stack-ptr-step (worklist-init k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-init k) prog fs ff wf
stack-ptr-step (worklist-push k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-push k) prog fs ff wf
stack-ptr-step (worklist-pop k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-pop k) prog fs ff wf
stack-ptr-step (worklist-check k) prog fs r ftq ff wf =
  flat-stack-ptr (worklist-check k) prog fs ff wf
stack-ptr-step (instr-sigop si) prog fs r ftq ff wf =
  flat-stack-ptr (instr-sigop si) prog fs ff wf
stack-ptr-step (instr-load-const p v) prog fs r ftq ff wf =
  flat-stack-ptr (instr-load-const p v) prog fs ff wf
stack-ptr-step (instr-load-code-addr k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-load-code-addr k) prog fs ff wf
stack-ptr-step instr-save-closure-reg prog fs r ftq ff wf =
  flat-stack-ptr instr-save-closure-reg prog fs ff wf
stack-ptr-step (instr-load-tag-lit k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-load-tag-lit k) prog fs ff wf
stack-ptr-step (instr-alloc-heap k) prog fs r ftq ff wf =
  flat-stack-ptr (instr-alloc-heap k) prog fs ff wf
stack-ptr-step (instr-reg-op op) prog fs r ftq ff wf =
  flat-stack-ptr (instr-reg-op op) prog fs ff wf
stack-ptr-step (instr-ctrl c) prog fs r ftq ff wf =
  flat-stack-ptr (instr-ctrl c) prog fs ff wf

-- A start state satisfies the invariant vacuously: both memories are empty and
-- no register holds a pointer.
entry-stack-ptr : ∀ (fs : FlatState) → EntryLike fs → StackPtrWF fs
entry-stack-ptr fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr , _) = record
  { sp-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; sp-heap  = λ hl → subst StackPtrOK? (sym (hemp hl)) tt
  ; sp-stack = λ f k → subst StackPtrOK? (sym (semp f k)) tt }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → StackPtrOK (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

-- …and the pointer-bounds and store-WF invariants likewise (D074: the entry
-- registers are all tags, both memories empty).
entry-ptr-bounds : ∀ (fs : FlatState) → EntryLike fs → PtrBoundsWF fs
entry-ptr-bounds fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr , _) = record
  { pb-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; pb-heap  = λ hl → subst (PtrB? _) (sym (hemp hl)) tt
  ; pb-stack = λ f k → subst (PtrB? _) (sym (semp f k)) tt }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → PtrB (block-size (falloc fs)) (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

entry-flat-wf : ∀ (fs : FlatState) → EntryLike fs → FlatWF fs
entry-flat-wf fs (_ , _ , _ , _ , _ , hemp , semp , _ , noptr , _) = record
  { wf-regs  = λ r → go r (readReg (regs (floc fs)) r) refl
  ; wf-heap  = λ hl → subst (svm-below _) (sym (hemp hl)) tt
  ; wf-stack = λ f k → subst (svm-below _) (sym (semp f k)) tt
  ; wf-fresh = λ hl _ → hemp hl }
  where go : ∀ (r : AbstractReg) (v : StoredValue FS) → readReg (regs (floc fs)) r ≡ v
           → sv-below (next-heap-ref (falloc fs)) (readReg (regs (floc fs)) r)
        go r (SV-Ptr loc)  eq = ⊥-elim (noptr r loc eq)
        go r (SV-Tag t)    eq rewrite eq = tt
        go r (SV-Lit p v)  eq rewrite eq = tt
        go r (SV-Code c)   eq rewrite eq = tt

-- Every stack pointer in a reachable state addresses a live pair of the current
-- frame. Induction on `Reachable`, exactly like `run-stack-slot`: the entry
-- state holds no stack pointer at all (its registers hold the heap filler and
-- both memories are empty), and each step preserves the invariant because the
-- program is emitted — frame-free, and its `lea-slot`s address reserved pairs.
run-stack-ptr : ∀ prog (fs : FlatState) (r : RunAt prog fs) → StackPtrWF fs
run-stack-ptr prog fs (mkRunAt ir eq hm reach) = go fs reach
  where go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs' → StackPtrWF fs'
        go fs' (reach-start .fs' el _) = entry-stack-ptr fs' el
        go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
          stack-ptr-step i prog fs'' (mkRunAt ir eq hm r') ftq
            (frame-op-absurd prog fs'' i (ir , eq) hm ftq)
            (go fs'' r')

-- The two forms the block-steps ask for. Since Plan 0.63's `StackPtrWF`
-- became "there is no stack pointer", holding one in `Input1` is refuted
-- outright — these keep their signatures so nothing downstream changes, but
-- both components are now `⊥-elim`.
stack-ptr-current : ∀ prog (fs : FlatState) (f : Frame) (k : Slot) → RunAt prog fs
                  → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                  → (f ≡ current-frame (falloc fs)) × (k < frame-slots (falloc fs))
stack-ptr-current prog fs f k r eq =
  stack-ptr-frame fs Input1 f k (run-stack-ptr prog fs r) eq
  , ⊥-elim (stack-ptr-live fs Input1 f k (run-stack-ptr prog fs r) eq)

stack-ptr-current-suc : ∀ prog (fs : FlatState) (f : Frame) (k : Slot) → RunAt prog fs
                      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtStack f k)
                      → (f ≡ current-frame (falloc fs)) × (suc k < frame-slots (falloc fs))
stack-ptr-current-suc prog fs f k r eq =
  stack-ptr-frame fs Input1 f k (run-stack-ptr prog fs r) eq
  , ⊥-elim (stack-ptr-suc-live fs Input1 f k (run-stack-ptr prog fs r) eq)

slot-read-in-frame : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunAt prog fs
                   → fetch prog (fpc fs) ≡ just i → slot-of i ≡ just slot
                   → slot < frame-slots (falloc fs)
-- the positional bound, then the two equations that place it: the segment in
-- force at this pc (constant today — `emitted-seg-const`) and the machine's own
-- window (`run-stack-slot`).
slot-read-in-frame prog fs slot i r ftq soq =
  -- the emitter's positional bound, at the machine's positional window
  subst (slot <_) (sym seg-eq)
    (subst (λ pr → slot < cur (seg-at pr (fpc fs) (mkSeg (ir-stack-budget (run-ir r)) [])))
           (sym (run-emit r))
           (emitted-slot-below-budget (run-ir r) (fpc fs) i slot
             (subst (λ p → fetch p (fpc fs) ≡ just i) (run-emit r) ftq) soq))
  where
    -- D092: `SegCur`'s exception row is a pc holding a body ENTRY, and a
    -- marker addresses no slot (`slot-of (instr-ctrl _) = nothing`) — so the
    -- instruction this very lemma was handed refutes it.
    just-injI : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
    just-injI refl = refl
    seg-eq : frame-slots (falloc fs)
           ≡ cur (seg-at prog (fpc fs) (mkSeg (ir-stack-budget (run-ir r)) []))
    seg-eq = go (seg-cur (run-seg-wf prog fs r))
      where go : SegCur prog (ir-stack-budget (run-ir r)) fs
               → frame-slots (falloc fs)
               ≡ cur (seg-at prog (fpc fs) (mkSeg (ir-stack-budget (run-ir r)) []))
            go (inj₁ e) = e
            go (inj₂ (ℓ , bb , tq , _)) =
              ⊥-elim (no-slot (subst (λ z → slot-of z ≡ just slot)
                                     (just-injI (trans (sym ftq) tq)) soq))
              where no-slot : ∀ {A : Set} → nothing ≡ just slot → A
                    no-slot ()

------------------------------------------------------------------------
-- THE POINTER-BOUNDS INVARIANT IS A THEOREM (plan 0.54 rung D, item 5).
--
-- Every dynamic pointer a reachable state holds is in-bounds for its block —
-- in the PAIR form (`Once.CCC.Machine.FlatPtrBounds`). Same shape as
-- `run-stack-ptr`, with two extra inputs: the emitter's allocation discipline
-- (every emitted `instr-alloc-heap` is a 2-cell pair block, `AllocMin`) and
-- the store-WF invariant (carried through the SAME induction — an allocation
-- cannot shrink the block under a live pointer because no live pointer
-- references the fresh ref). This is what turned the in-bounds residual
-- family into theorems: `store-indirect{,-suc}-inbounds` outright, and the
-- in-bounds conjunct of `load-indirect{,-suc}-target-wf` (whose pointer-SHAPE
-- half stays the D073 site-discipline residual, now named `-target-ptr`).
------------------------------------------------------------------------

-- THE EMITTER HALF: a fetched instruction of an emitted program satisfies the
-- allocation discipline (`AllocMinI`).
emitted-alloc-min : ∀ prog (fs : FlatState) (i : AbstractInstr) → Emitted prog
                  → fetch prog (fpc fs) ≡ just i → AllocMinI i
emitted-alloc-min .(ir-to-trace ir) fs i (ir , refl) ftq = fetch-alloc-min {FS} ir ftq

-- ONE FRAME-FREE STEP PRESERVES THE INVARIANT — enumerated like
-- `stack-ptr-step` (the vacuous alloc premises need `i` concrete).
ptr-bounds-step : ∀ (i : AbstractInstr) prog (fs : FlatState) → RunAt prog fs
                → fetch prog (fpc fs) ≡ just i → EmittableI i
                → FlatWF fs
                → PtrBoundsWF fs → PtrBoundsWF (flat-exec-instr i prog fs)
ptr-bounds-step (instr-case-on-tag f g) prog fs r ftq () wfS wf
ptr-bounds-step (instr-alloc-stack n)   prog fs r ftq () wfS wf
ptr-bounds-step (instr-dealloc-stack n) prog fs r ftq () wfS wf
ptr-bounds-step (instr-push-frame cap)  prog fs r ftq () wfS wf
ptr-bounds-step instr-pop-frame         prog fs r ftq () wfS wf
ptr-bounds-step (instr-loop body)       prog fs r ftq () wfS wf
ptr-bounds-step (lea-indexed slot)      prog fs r ftq () wfS wf
-- THE PRODUCER: the emitter's alloc discipline comes in through the premise.
ptr-bounds-step (instr-alloc-heap k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-alloc-heap k) prog fs ff
    (λ n eq → subst AllocMinI eq
                (emitted-alloc-min prog fs (instr-alloc-heap k) (run-emitted r) ftq))
    wfS wf
ptr-bounds-step mov-to-output prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-to-output prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-to-input prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-to-input prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-output-to-input2 prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-output-to-input2 prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step mov-input2-to-output prog fs r ftq ff wfS wf =
  flat-ptr-bounds mov-input2-to-output prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step load-indirect prog fs r ftq ff wfS wf =
  flat-ptr-bounds load-indirect prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step load-indirect-suc prog fs r ftq ff wfS wf =
  flat-ptr-bounds load-indirect-suc prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (load-from-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (load-from-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (store-at-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (store-at-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step store-indirect prog fs r ftq ff wfS wf =
  flat-ptr-bounds store-indirect prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step store-indirect-suc prog fs r ftq ff wfS wf =
  flat-ptr-bounds store-indirect-suc prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (lea-slot k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (lea-slot k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (restore-input k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (restore-input k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-reclaim-to k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-reclaim-to k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step instr-call-closure prog fs r ftq ff wfS wf =
  flat-ptr-bounds instr-call-closure prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-init k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-init k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-push k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-push k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-pop k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-pop k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (worklist-check k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (worklist-check k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-sigop si) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-sigop si) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-const p v) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-const p v) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-code-addr k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-code-addr k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step instr-save-closure-reg prog fs r ftq ff wfS wf =
  flat-ptr-bounds instr-save-closure-reg prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-load-tag-lit k) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-load-tag-lit k) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-reg-op op) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-reg-op op) prog fs ff (λ { _ () }) wfS wf
ptr-bounds-step (instr-ctrl c) prog fs r ftq ff wfS wf =
  flat-ptr-bounds (instr-ctrl c) prog fs ff (λ { _ () }) wfS wf

-- THE RUN INDUCTION, carrying the store-WF invariant alongside (the alloc
-- step's freshness needs it at every PRE state, and `EntryLike` — all-tag
-- registers, empty memories — starts both off).
run-wf-ptr-bounds : ∀ prog (fs : FlatState) (r : RunAt prog fs)
                  → FlatWF fs × PtrBoundsWF fs
run-wf-ptr-bounds prog fs (mkRunAt ir eq hm reach) = go fs reach
  where go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs'
           → FlatWF fs' × PtrBoundsWF fs'
        go fs' (reach-start .fs' el _) = entry-flat-wf fs' el , entry-ptr-bounds fs' el
        go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
          let ih = go fs'' r' in
          flat-wf-step i prog fs'' (proj₁ ih) ,
          ptr-bounds-step i prog fs'' (mkRunAt ir eq hm r') ftq
            (frame-op-absurd prog fs'' i (ir , eq) hm ftq)
            (proj₁ ih) (proj₂ ih)

run-ptr-bounds : ∀ prog (fs : FlatState) (r : RunAt prog fs) → PtrBoundsWF fs
run-ptr-bounds prog fs r = proj₂ (run-wf-ptr-bounds prog fs r)

------------------------------------------------------------------------
-- THE DATAFLOW DISCIPLINES ARE THEOREMS (Plan 0.62 wiring, 2026-08-02).
--
-- The emitter's typed shape check (`emitted-shape-check`, M2b) accepts the
-- program; run consistency (`run-meets`, M3) puts the current state inside
-- the checker's expectation at its pc; `check-at` localizes the positive
-- check to the fetched site; and the SITE FACTS (`site-load-ptr`,
-- `site-branch-tag` — proven in `ShapeTable.Sem`) convert expectation +
-- state into exactly the residual conclusions. This is what makes the
-- whole shape layer (ShapeAt, the checker, the interpretation, the store
-- bricks) LOAD-BEARING on the apex path.
------------------------------------------------------------------------

-- the run's program passes the shape check (via `Emitted` + `HeapModed`)
run-shape-check : ∀ prog (fs : FlatState) (r : RunAt prog fs)
                → Σ LabelEnv (λ env →
                    check-shapes env (entry-expect Unit) prog ≡ true)
run-shape-check prog fs r =
  proj₁ chk ,
  subst (λ p → check-shapes (proj₁ chk) (entry-expect Unit) p ≡ true)
        (sym (run-emit r)) (proj₂ chk)
  where chk = emitted-shape-check (run-ir r) (run-heap r)

-- A SLOT READ NEVER FINDS AN UNWRITTEN SLOT (Plan 0.54 rung D).
--
-- This is what makes the `*-empty-*` routes UNREACHABLE. It replaces what the
-- OLD bidirectional `Window` supplied for free: that assertion made the
-- concrete cell unmapped wherever the abstract one was, so an empty-slot read
-- "corresponded" by getting both machines stuck. That was false on frame
-- re-entry, and with `Window` one-directional the read would be a genuine
-- DIVERGENCE — abstract halts, concrete reads the previous frame's data.
--
-- So the emitter's discipline has to rule it out, and it does: `site-ok` now
-- requires a non-`e-any` claim at every slot read, and `MeetsSlot` sends every
-- such claim at `nothing` to `⊥`. Same shape as `slot-read-in-frame` — the
-- checker's site fact, localized by `check-at`, met by `run-meets`.
--
-- `sok` is how the caller says which site this is; every call passes `λ _ → refl`.
slot-read-written : ∀ prog (fs : FlatState) (slot : Slot) (i : AbstractInstr) → RunAt prog fs
                  → fetch prog (fpc fs) ≡ just i
                  → (∀ st → ST.site-ok st i ≡ ST.not-any (ST.slot-get (ST.e-slot st) slot))
                  → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ nothing → ⊥
slot-read-written prog fs slot i r ftq sok empty =
  site-slot-written (ST.slot-get (ST.e-slot st) slot) claim met
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    claim : ST.not-any (ST.slot-get (ST.e-slot st) slot) ≡ true
    claim = trans (sym (sok st))
                  (proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                            (trans (sym (fetch-at-pc prog (fpc fs))) ftq)))
    met = subst (λ m → ST.Sem.MeetsSlot FS (ST.slot-get (ST.e-slot st) slot) (falloc fs) m (floc fs))
                empty
                (proj₂ (proj₂ (proj₂ (run-meets prog fs r env chk))) slot)

load-indirect-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                         → fetch prog (fpc fs) ≡ just load-indirect
                         → Σ (ValueLocation FS) (λ loc →
                             readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-indirect-target-ptr prog fs r ftq =
  site-load-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-ptr (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

load-indirect-suc-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                             → fetch prog (fpc fs) ≡ just load-indirect-suc
                             → Σ (ValueLocation FS) (λ loc →
                                 readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
load-indirect-suc-target-ptr prog fs r ftq =
  site-load-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-ptr (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

-- THE STORE TARGET DISCIPLINE (2026-08-03): at an emitted store site the
-- target register holds a POINTER — the shape checker requires the block
-- under construction there (`site-ok … store-indirect = is-fresh`), which
-- is the emitter's initialization discipline (allocate, fill, then share).
-- This is what retires `store-indirect{,-suc}-bad`: the divergent route
-- (a store THROUGH a non-pointer, where the concrete `mov [rdi],rax`
-- writes at the value's encoding and continues while the abstract machine
-- halts) is UNREACHABLE in emitted code, so it needs no correspondence.
store-indirect-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                          → fetch prog (fpc fs) ≡ just store-indirect
                          → Σ (ValueLocation FS) (λ loc →
                              readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-indirect-target-ptr prog fs r ftq =
  site-store-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-fresh (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

store-indirect-suc-target-ptr : ∀ prog (fs : FlatState) → RunAt prog fs
                              → fetch prog (fpc fs) ≡ just store-indirect-suc
                              → Σ (ValueLocation FS) (λ loc →
                                  readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
store-indirect-suc-target-ptr prog fs r ftq =
  site-store-ptr (e-in1 st) ok (proj₁ (run-meets prog fs r env chk))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.is-fresh (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))

-- the non-pointer routes of a store site are absurd
store-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunAt prog fs
                    → fetch prog (fpc fs) ≡ just store-indirect
                    → readReg (regs (floc fs)) Input1 ≡ v
                    → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                    → ⊥
store-nonptr-absurd prog fs r ftq i-eq nptr =
  nptr (proj₁ wits) (trans (sym i-eq) (proj₂ wits))
  where wits = store-indirect-target-ptr prog fs r ftq

store-suc-nonptr-absurd : ∀ prog (fs : FlatState) {v : StoredValue FS} → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just store-indirect-suc
                        → readReg (regs (floc fs)) Input1 ≡ v
                        → (∀ (loc : ValueLocation FS) → v ≡ SV-Ptr loc → ⊥)
                        → ⊥
store-suc-nonptr-absurd prog fs r ftq i-eq nptr =
  nptr (proj₁ wits) (trans (sym i-eq) (proj₂ wits))
  where wits = store-indirect-suc-target-ptr prog fs r ftq

branch-tag-scrutinee-wf : ∀ prog (fs : FlatState) (m : LabelId) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
                        → Σ (ValueLocation FS) (λ loc → Σ ℕ (λ k →
                            (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (readLoc (floc fs) loc ≡ just (SV-Tag k))))
branch-tag-scrutinee-wf prog fs m r ftq =
  repack (site-branch-tag (e-in1 st) ok (proj₁ (run-meets prog fs r env chk)))
  where
    sc  = run-shape-check prog fs r
    env = proj₁ sc
    chk = proj₂ sc
    st  = state-at env (entry-expect Unit) prog (fpc fs)
    ok : ST.tag-site-ok (e-in1 st) ≡ true
    ok = proj₁ (check-at env (entry-expect Unit) prog (fpc fs) chk
                  (trans (sym (fetch-at-pc prog (fpc fs))) ftq))
    repack : Σ (ValueLocation FS) (λ loc →
               (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
               × Σ ℕ (λ t → readLoc (floc fs) loc ≡ just (SV-Tag t)))
           → Σ (ValueLocation FS) (λ loc → Σ ℕ (λ k →
               (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
               × (readLoc (floc fs) loc ≡ just (SV-Tag k))))
    repack (loc , i-eq , t , r-eq) = loc , t , i-eq , r-eq

-- THE FOUR IN-BOUNDS FACTS THE BLOCK-STEPS CONSUME, now read off the
-- invariant (the store pair was residual until 2026-08-01; the load pair
-- combines the `-target-ptr` residual's pointer shape with the theorem).
store-indirect-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just store-indirect
                        → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                        → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))
store-indirect-inbounds prog fs hl r ftq eq =
  ptr-bounds-cell fs Input1 hl (run-ptr-bounds prog fs r) eq

store-indirect-suc-inbounds : ∀ prog (fs : FlatState) (hl : HeapLocation) → RunAt prog fs
                            → fetch prog (fpc fs) ≡ just store-indirect-suc
                            → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                            → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))
store-indirect-suc-inbounds prog fs hl r ftq eq =
  ptr-bounds-suc fs Input1 hl (run-ptr-bounds prog fs r) eq

load-indirect-target-wf : ∀ prog (fs : FlatState) → RunAt prog fs
                        → fetch prog (fpc fs) ≡ just load-indirect
                        → Σ (ValueLocation FS) (λ loc →
                            (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                            × (∀ hl → loc ≡ AtDynamic hl
                               → heap-offset hl < block-size (falloc fs) (ref-id (heap-ref hl))))
load-indirect-target-wf prog fs r ftq with load-indirect-target-ptr prog fs r ftq
... | loc , eq = loc , eq ,
  λ hl leq → ptr-bounds-cell fs Input1 hl (run-ptr-bounds prog fs r)
               (trans eq (cong SV-Ptr leq))

load-indirect-suc-target-wf : ∀ prog (fs : FlatState) → RunAt prog fs
                            → fetch prog (fpc fs) ≡ just load-indirect-suc
                            → Σ (ValueLocation FS) (λ loc →
                                (readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc)
                                × (∀ hl → loc ≡ AtDynamic hl
                                   → heap-offset (sucHL hl) < block-size (falloc fs) (ref-id (heap-ref (sucHL hl)))))
load-indirect-suc-target-wf prog fs r ftq with load-indirect-suc-target-ptr prog fs r ftq
... | loc , eq = loc , eq ,
  λ hl leq → ptr-bounds-suc fs Input1 hl (run-ptr-bounds prog fs r)
               (trans eq (cong SV-Ptr leq))


------------------------------------------------------------------------
-- THE CALL WINDOW IS ONE STEP WIDE, AND ITS INSTRUCTION IS A BODY MARKER
-- (plan 0.65 G2, 2026-08-16).
--
-- `flink ≡ just _` says a call has happened and the callee has not spilled its
-- return address yet. The callee's FIRST instruction is its own `c-thunk`: a
-- call lands the pc on `find-thunk prog ℓ`, and `find-thunk-sound` — already a
-- theorem — says what that index fetches.
--
-- WHY IT EARNS ITS KEEP. Without it, every block-step that is NOT the body
-- marker would have to show it leaves the link alone: 41 obligations per arch,
-- and on x86-64 the claim is not even true in general, since its link lives at
-- `[rsp]` and a slot store can reach that address. With it, the engine hands
-- those fields `flink fs ≡ nothing` and each discharges its link component by
-- absurdity. One induction instead of 82 proofs.
--
-- The induction is `Reachable`, and every case is a clash rather than an
-- argument:
--
--   entry        `EntryLike` says `flink ≡ nothing`.
--   after a call `callView`: the halting route preserves the link and hands
--                the clash to the IH; the entering route IS the theorem.
--   after a body marker  `do-thunk` clears the link.
--   after anything else  `FlinkView`'s `fv-pres` threads it, so the IH applies
--                at the PRE-state and says the fetched instruction was a body
--                marker — whereupon `fv-pres` at THAT instruction says the
--                link was cleared, contradicting it being live.
------------------------------------------------------------------------
private
  nothing≢justℕ : ∀ {x : ℕ} → nothing ≡ just x → ⊥
  nothing≢justℕ ()

run-link-at-thunk : ∀ prog (fs : FlatState) → RunAt prog fs
                  → ∀ {r : ℕ} → flink fs ≡ just r
                  → Σ LabelId (λ ℓ → Σ ℕ (λ bb →
                      fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb))))
run-link-at-thunk prog fs (mkRunAt ir eq hm reach) = go fs reach
  where
    Goal : FlatState → Set
    Goal fs' = Σ LabelId (λ ℓ → Σ ℕ (λ bb →
                 fetch prog (fpc fs') ≡ just (instr-ctrl (c-thunk ℓ bb))))

    go : ∀ (fs' : FlatState) → Reachable prog (ir-stack-budget ir) fs'
       → ∀ {r : ℕ} → flink fs' ≡ just r → Goal fs'
    go fs' (reach-start .fs' (_ , _ , _ , _ , _ , _ , _ , _ , _ , fl) _) lk =
      ⊥-elim (nothing≢justℕ (trans (sym fl) lk))
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) {r} lk =
      step (flinkView i)
      where
        -- the IH, once the link is known live at the PRE-state
        ih-thunk : flink fs'' ≡ just r → Σ LabelId (λ ℓ → Σ ℕ (λ bb →
                     i ≡ instr-ctrl (c-thunk ℓ bb)))
        ih-thunk pre = proj₁ ihr , proj₁ (proj₂ ihr) ,
                       just-injective (trans (sym ftq) (proj₂ (proj₂ ihr)))
          where ihr = go fs'' r' pre

        step : FlinkView i → Goal (flat-exec-instr i prog fs'')
        -- THE CALL. `callView` splits into halt and enter.
        step (fv-call ieq) = call-step (callView prog fs'')
          where
            red : flat-exec-instr i prog fs'' ≡ do-call prog fs''
            red = cong (λ z → flat-exec-instr z prog fs'') ieq
            call-step : CallPost prog fs'' → Goal (flat-exec-instr i prog fs'')
            -- a HALTING call writes no link, so the link was already live and
            -- the IH says the pc held a body marker — but `ftq` says it held
            -- the call.
            call-step (cp-halt heq) =
              ⊥-elim (thunk≢call (proj₂ (proj₂ (ih-thunk pre))))
              where
                pre : flink fs'' ≡ just r
                pre = trans (sym (cong flink (trans red heq))) lk
                thunk≢call : ∀ {ℓ bb} → i ≡ instr-ctrl (c-thunk ℓ bb) → ⊥
                thunk≢call teq with trans (sym teq) ieq
                ... | ()
            -- and an ENTERING call is the theorem: its pc IS the resolved
            -- body index, and `find-thunk-sound` says what sits there.
            call-step (cp-enter ℓ j feq eeq) =
              ℓ , proj₁ fts ,
              subst (λ z → fetch prog z ≡ just (instr-ctrl (c-thunk ℓ (proj₁ fts))))
                    (sym (cong fpc (trans red eeq))) (proj₂ fts)
              where fts = find-thunk-sound prog ℓ j feq
        -- THE BODY MARKER clears the link, so it cannot be live after one.
        step (fv-thunk ℓ bb ieq) =
          ⊥-elim (nothing≢justℕ (trans (sym cleared) lk))
          where cleared : flink (flat-exec-instr i prog fs'') ≡ nothing
                cleared = cong (λ z → flink (flat-exec-instr z prog fs'')) ieq
        -- EVERYTHING ELSE threads the link, so the IH applies at the
        -- pre-state and says the instruction was a body marker — which this
        -- very equation then says cleared the link.
        step (fv-pres pres) =
          ⊥-elim (nothing≢justℕ (trans (sym cleared) pre))
          where
            pre : flink fs'' ≡ just r
            pre = trans (sym (pres prog fs'')) lk
            ihr = ih-thunk pre
            cleared : flink fs'' ≡ nothing
            cleared = trans (sym (pres prog fs''))
                            (cong (λ z → flink (flat-exec-instr z prog fs''))
                                  (proj₂ (proj₂ ihr)))

-- …AND THE FORM THE ENGINE ACTUALLY CONSUMES. `bs-call` and `bs-c-ret` need
-- `flink fs ≡ nothing` — both READ the head return cell, so they need
-- `ret-eq`'s memory row rather than the arch's link claim — and the engine is
-- the only layer that can supply it, because it holds the `RunAt`. The
-- contrapositive of the lemma above at a fetch that is not a body marker.
--
-- With-free by the standard aux (`de-with by parameterizing the equation`):
-- the split is on `flink fs`, which is not a pattern position.
run-link-nothing-aux : ∀ prog (fs : FlatState) → RunAt prog fs
                     → (∀ (ℓ : LabelId) (bb : ℕ)
                          → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb)) → ⊥)
                     → ∀ (m : Maybe ℕ) → flink fs ≡ m → flink fs ≡ nothing
run-link-nothing-aux prog fs ra nt nothing  eq = eq
run-link-nothing-aux prog fs ra nt (just r) eq =
  ⊥-elim (nt (proj₁ res) (proj₁ (proj₂ res)) (proj₂ (proj₂ res)))
  where res = run-link-at-thunk prog fs ra eq

run-link-nothing : ∀ prog (fs : FlatState) → RunAt prog fs
                 → (∀ (ℓ : LabelId) (bb : ℕ)
                      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-thunk ℓ bb)) → ⊥)
                 → flink fs ≡ nothing
run-link-nothing prog fs ra nt = run-link-nothing-aux prog fs ra nt (flink fs) refl
