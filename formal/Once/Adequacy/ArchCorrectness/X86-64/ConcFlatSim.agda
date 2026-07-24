-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim  (Plan 0.54 rung D / D4.3)
--
-- Wiring the recovered flat↔x86-64 refinement cluster (FlatSimulation +
-- FlatCorrespondence + FlatComposition + StepLemmas) toward the apex
-- `x86-64-conc-flat-sim`. This module is the ASSEMBLY layer:
--
--   * `ccc-step-bs` — the CCC engine: given a `BlockStep` (one flat step ↔
--     `X.exec` of its compiled x86 block, preserving `CompiledCorr`), mirror it
--     into run-events (block-run-exec) and recurse (events-agree). Each fetched
--     AbstractInstr feeds its PROVEN `block-step-*` lemma directly (moves/reg-ops/
--     label straight through; c-jmp/scratch-dec/load-store-indirect case their
--     witness then feed the proven lemma, WF/liveness bad-cases as named residuals).
--     No `block-step-any` dispatcher / `block-step-rest` catch-all — deleted.
--
-- Parameterised exactly like FlatSimulation (FS + the heap-address encoding),
-- so the concrete instantiation (x86-64-frame-semantics + the heap layout) is
-- supplied once, at the point this feeds `conc-flat-sim`.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.Memory.HeapAddress using (HeapLocation; sucHL)
open import Once.CCC.Machine.SMCore using (AllocState)
open import Once.CCC.Target.X86-64.Syntax using
  ( slot-size; Program; Instr; rsp
  ; mov; lea; add; sub; cmp; test; jmp; je; jne; call; call-sym
  ; ret; push; pop; nop; ud2; syscall; label )
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.X86-64.ConcFlatSim
  (FS : FrameSemantics)
  (enc-hl : HeapLocation → ℕ)
  -- CompCert memory injection on LIVE cells (the allocator interface supplies
  -- these — see FlatCorrespondence); replaces the unsatisfiable global enc-hl-inj.
  (LiveIn : AllocState {FS} → HeapLocation → Set)
  (enc-hl-inj-live : ∀ (as : AllocState {FS}) {a b : HeapLocation}
                   → LiveIn as a → LiveIn as b → enc-hl a ≡ enc-hl b → a ≡ b)
  (enc-hl-suc : ∀ (hl : HeapLocation) → enc-hl (sucHL hl) ≡ enc-hl hl + slot-size)
  where

open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)

open import Once.CCC.Machine.SMCore
open MemOps {FS} using (writeLoc; writeLocToHeap; writeLoc-halted)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X

open import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation
  FS enc-hl LiveIn enc-hl-inj-live enc-hl-suc public
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Once.Adequacy.ArchCorrectness.X86-64.FlatComposition FS
  using (x86-len; x86-off; drop-compile; fetch-drop; drop-[])
open import Once.CCC.Target.X86-64.AbstractToX86 using (compile-trace; slot-to-disp)

------------------------------------------------------------------------
-- Imports for the run-events event-trace correspondence (block-run-exec + the
-- events-agree induction below).
open import Once.Adequacy.CPU.X86-64 using (val-x86-64)
import Once.Arith.Backend.X86-64.RunTrace as RTx
open import Data.Empty using (⊥; ⊥-elim)
open import Once.SigOp.Info using (SigOpInfo; effect; EffectShape; Pure; Emits; Halts)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Arith.Backend.XInstr.Syntax using (XInstr)
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith)
open import Data.Product using (uncurry)

-- NON-HALTING ⇒ NON-CALL: `call-sym` is the ONLY instruction `matchCall` accepts,
-- and `execInstr (call-sym _)` always sets `halted := true`. So any step that
-- leaves the machine running (`halted s₁ ≡ false`) cannot have been a `call-sym`,
-- i.e. `matchCall j ≡ nothing`. (The one absurd case is `call-sym`, ruled out by
-- the halt clash; every other instruction is `matchCall … = nothing` definitionally.)
nonhalt-noncall : ∀ prog s j {s₁} → X.execInstr prog s j ≡ just s₁
                → X.State.halted s₁ ≡ false → RTx.matchCall j ≡ nothing
nonhalt-noncall prog s (call-sym lbl) eq hnh
  with trans (cong X.State.halted (just-injective eq)) hnh
... | ()
nonhalt-noncall prog s (mov _ _)  eq hnh = refl
nonhalt-noncall prog s (lea _ _)  eq hnh = refl
nonhalt-noncall prog s (add _ _)  eq hnh = refl
nonhalt-noncall prog s (sub _ _)  eq hnh = refl
nonhalt-noncall prog s (cmp _ _)  eq hnh = refl
nonhalt-noncall prog s (test _ _) eq hnh = refl
nonhalt-noncall prog s (jmp _)    eq hnh = refl
nonhalt-noncall prog s (je _)     eq hnh = refl
nonhalt-noncall prog s (jne _)    eq hnh = refl
nonhalt-noncall prog s (call _)   eq hnh = refl
nonhalt-noncall prog s ret        eq hnh = refl
nonhalt-noncall prog s (push _)   eq hnh = refl
nonhalt-noncall prog s (pop _)    eq hnh = refl
nonhalt-noncall prog s nop        eq hnh = refl
nonhalt-noncall prog s ud2        eq hnh = refl
nonhalt-noncall prog s syscall    eq hnh = refl
nonhalt-noncall prog s (label _)  eq hnh = refl

private
  t≢f : true ≡ false → ⊥
  t≢f ()
  n≢j : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  n≢j ()

-- WITNESS-FREE block chaining: if `X.exec L` reaches a NON-halted `s'`, then every
-- one of the L steps was non-halting (else exec would have stopped at a halted
-- state ≠ s'), hence non-call — so run-events mirrors it, emitting [] and landing
-- on s'. The concrete-side backbone of the per-instruction dispatch, derived purely
-- from `X.exec L ≡ just s'` + `halted s' ≡ false` (no separate call-free witness).
--
-- Key mechanism: in each branch the `with … in` abstraction has ALREADY reduced
-- `X.exec (suc L)` inside `eq`'s type (through `halted s` / fetch / execInstr /
-- `halted s₁`), so `eq` speaks directly about the peeled result — we USE that rather
-- than fight it by re-introducing `X.exec` via lemmas. Every early-stop leaves
-- `eq : just <a halted state> ≡ just s'`, whose `halted = true` clashes with `hs'`
-- (`maybe′ halted`-cong avoids `just-injective`'s eta-expansion of `s'`); the one
-- running step is non-call (nonhalt-noncall) so run-events-noncall advances, then recurse.
block-run-exec : ∀ (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                   L rest cprog s {s'} → X.exec L cprog s ≡ just s' → X.State.halted s' ≡ false
               → RTx.run-events val-x86-64 ev env (L + rest) cprog s
                   ≡ RTx.run-events val-x86-64 ev env rest cprog s'
block-run-exec ev env zero rest cprog s eq hs' =
  cong (λ z → RTx.run-events val-x86-64 ev env rest cprog z) (just-injective eq)
block-run-exec ev env (suc L) rest cprog s {s'} eq hs' with X.State.halted s in hs
... | true  = ⊥-elim (t≢f (trans (sym hs) (trans (cong (maybe′ X.State.halted true) eq) hs')))
... | false with X.fetch cprog (X.State.pc s) in ft
...   | nothing = ⊥-elim (t≢f (trans (cong (maybe′ X.State.halted true) eq) hs'))
...   | just j with X.execInstr cprog s j in exq
...     | nothing = ⊥-elim (n≢j eq)
...     | just s₁ with X.State.halted s₁ in hs1
...       | true  = ⊥-elim (t≢f (trans (sym hs1) (trans (cong (maybe′ X.State.halted true) eq) hs')))
...       | false rewrite nonhalt-noncall cprog s j exq hs1 | exq =
              block-run-exec ev env L rest cprog s₁ eq hs'

------------------------------------------------------------------------
-- (3) events-agree: the fuel induction relating the concrete run-events event
-- trace to the abstract flat-events, threading CompiledCorr. Base + halted are
-- proven here; the running case dispatches each fetched abstract instruction to
-- its brick (block-run-1 / run-events-arith / run-events-external), accumulating
-- events on both sides (events-running, the per-instruction step).
------------------------------------------------------------------------
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch; event-of)
open import Data.List using (List; []; _∷_; _++_; drop)
open import Once.Denotation.Trace using (SigOpEvent)

-- fetch prog k ≡ nothing (k past the trace) ⇒ dropping k blocks leaves []. The
-- abstract-side ingredient for the program-end boundary.
fetch-nothing-drop : ∀ (prog : AbstractTrace) (k : ℕ) → fetch prog k ≡ nothing → drop k prog ≡ []
fetch-nothing-drop []       k       eq = drop-[] k
fetch-nothing-drop (i ∷ is) zero    ()
fetch-nothing-drop (i ∷ is) (suc k) eq = fetch-nothing-drop is k eq

-- fetch prog k ≡ just i ⇒ dropping k blocks exposes i at the head. The abstract-
-- side ingredient for the per-instruction pc-alignment (concrete fetch = the
-- compiled head of the fetched abstract instruction).
fetch-just-drop : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
                → fetch prog k ≡ just i → drop k prog ≡ i ∷ drop (suc k) prog
fetch-just-drop []       k       i ()
fetch-just-drop (x ∷ xs) zero    i eq = cong (_∷ xs) (just-injective eq)
fetch-just-drop (x ∷ xs) (suc k) i eq = fetch-just-drop xs k i eq

-- pc-alignment at a SigOp: the concrete pc = x86-off prog (fpc fs) (pc-off) fetches
-- the compiled head of `instr-sigop si`, which is exactly its one `call-sym`
-- (compile-sigOp = call-sym (once-symbol-path (name si)) ∷ []). Chain: pc-off ▸
-- fetch-drop ▸ drop-compile ▸ fetch-just-drop ▸ (compile-trace cons reduces the head).
sigop-concrete-fetch : ∀ prog fs s {A B} (si : SigOpInfo A B)
                     → CompiledCorr prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                     → X.fetch (compile-trace prog) (X.State.pc s)
                         ≡ just (call-sym (once-symbol-path (SigOpInfo.name si)))
sigop-concrete-fetch prog fs s si cc ftq =
  trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
  (trans (fetch-drop (compile-trace prog) (x86-off prog (fpc fs)))
  (trans (cong (λ z → X.fetch z 0) (drop-compile prog (fpc fs)))
         (cong (λ z → X.fetch (compile-trace z) 0) (fetch-just-drop prog (fpc fs) (instr-sigop si) ftq))))

-- The run-events REDUCTION at an ARITH (Pure) SigOp, PROVEN given the arith-env
-- contract (env maps the symbol to the block pl): the compiled `call-sym` is fetched
-- (sigop-concrete-fetch), matched (matchCall refl), dispatched to the arith block with
-- NO event (run-events-arith). halted s is false via halt-eq. Leaves the concrete
-- state at `dispatch-arith`'s post-state — the value-carrying step, mirroring
-- flat-events' [] for a Pure SigOp.
sigop-run-arith : ∀ ev env n prog fs s {A B} (si : SigOpInfo A B) (pl : List XInstr × ℕ)
                → CompiledCorr prog fs s → halted (floc fs) ≡ false
                → fetch prog (fpc fs) ≡ just (instr-sigop si)
                → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                → RTx.run-events val-x86-64 ev env (suc n) (compile-trace prog) s
                    ≡ RTx.run-events val-x86-64 ev env n (compile-trace prog)
                        (uncurry (dispatch-arith val-x86-64) pl s)
sigop-run-arith ev env n prog fs s si pl cc h ftq env-eq =
  RTx.run-events-arith val-x86-64 ev env n (compile-trace prog) s
    (call-sym (once-symbol-path (SigOpInfo.name si))) (once-symbol-path (SigOpInfo.name si)) pl
    (trans (C.halt-eq (dataCorr cc)) h)
    (sigop-concrete-fetch prog fs s si cc ftq)
    refl
    env-eq

-- A Pure SigOp emits no event (ev-of-loc's Pure branch is []).
event-of-pure : ∀ {A B} (si : SigOpInfo A B) fs → effect si ≡ Pure → event-of (instr-sigop si) fs ≡ []
event-of-pure si fs eqe rewrite eqe = refl

-- WF: the Output register never holds a STACK pointer at a heap store (cross-region
-- heap→stack refs are forbidden). The one residual behind the store-guard.
postulate
  store-output-not-stackref : ∀ fs {f k} → readReg (regs (floc fs)) Output ≡ SV-Ptr (AtStack f k) → ⊥

-- STORE-GUARD, PROVEN: `writeLoc (AtDynamic hl) v ≡ writeLocToHeap hl v` for the stored
-- value `v = readReg Output` — holds for every StoredValue shape EXCEPT a stack pointer
-- (which writeLoc drops as a no-op: cross-region heap→stack refs are forbidden). Case v;
-- the four legal shapes are `writeLocToHeap` definitionally (refl after `rewrite o-eq`),
-- and the illegal stack-ref shape is ruled out by WF (`store-output-not-stackref`). Covers
-- BOTH store-indirect (hl) and store-indirect-suc (sucHL hl) — parameterised by hl.
store-guard : ∀ fs (hl : HeapLocation)
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
        go (SV-Ptr (AtStack f k)) o-eq = ⊥-elim (store-output-not-stackref fs o-eq)

-- The run-events REDUCTION at an EXTERNAL (Emits/Halts) SigOp, PROVEN given the
-- external-env contract (env maps the symbol to `nothing`): the compiled `call-sym`
-- is fetched + matched, and run-events-external EMITS `ev lbl s` then continues past
-- the call (ret-past). This is the value-carrying observable emission; the `ev`
-- extractor's value is pinned to `machine-event` by the honest per-target contract.
sigop-run-external : ∀ ev env n prog fs s {A B} (si : SigOpInfo A B)
                   → CompiledCorr prog fs s → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-sigop si)
                   → env (once-symbol-path (SigOpInfo.name si)) ≡ nothing
                   → RTx.run-events val-x86-64 ev env (suc n) (compile-trace prog) s
                       ≡ ev (once-symbol-path (SigOpInfo.name si)) s
                         ++ RTx.run-events val-x86-64 ev env n (compile-trace prog) (RTx.ret-past s)
sigop-run-external ev env n prog fs s si cc h ftq env-eq =
  RTx.run-events-external val-x86-64 ev env n (compile-trace prog) s
    (call-sym (once-symbol-path (SigOpInfo.name si))) (once-symbol-path (SigOpInfo.name si))
    (trans (C.halt-eq (dataCorr cc)) h)
    (sigop-concrete-fetch prog fs s si cc ftq)
    refl
    env-eq

-- PROGRAM END (wp-end), PROVEN: the abstract fetch runs out (`fpc` past the trace),
-- so the concrete pc = `x86-off prog (fpc fs)` (pc-off) sits past `compile-trace prog`
-- — fetch there is `nothing`, hence run-events emits []. Chain: pc-off ▸ fetch-drop ▸
-- drop-compile ▸ fetch-nothing-drop (drop past ⇒ [] ⇒ compile-trace [] ⇒ fetch [] = nothing).
events-running-end : ∀ (n : ℕ) (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                       prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ nothing
                   → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s ≡ [])
events-running-end n ev env prog fs s cc h ftq =
  1 , RTx.run-events-fetch-none val-x86-64 ev env 0 (compile-trace prog) s cfetch-nothing
  where cfetch-nothing : X.fetch (compile-trace prog) (X.State.pc s) ≡ nothing
        cfetch-nothing =
          trans (cong (X.fetch (compile-trace prog)) (pc-off cc))
          (trans (fetch-drop (compile-trace prog) (x86-off prog (fpc fs)))
          (trans (cong (λ z → X.fetch z 0) (drop-compile prog (fpc fs)))
                 (cong (λ z → X.fetch (compile-trace z) 0) (fetch-nothing-drop prog (fpc fs) ftq))))

postulate
  -- PER-INSTRUCTION DISPATCH residual for the cases not yet routed to `ccc-step`
  -- (instr-sigop arith/external, control jmp/branch, memory/frame/slot). Shrinks as
  -- each is wired (arith→run-events-arith, external→run-events-external+contract, …).
  events-running-fetch-rest : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                                prog fs s i → CompiledCorr prog fs s → halted (floc fs) ≡ false
                            → fetch prog (fpc fs) ≡ just i
                            → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                                  ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs))

  -- c-jmp to a MISSING label: both the flat machine (do-jump nothing) and the concrete
  -- machine (x86 jmp to an absent label) HALT, so both traces are []. Residual = the
  -- x86↔flat label-miss correspondence (find-label-corr's negative direction).
  cjmp-miss : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                prog fs s m → CompiledCorr prog fs s → halted (floc fs) ≡ false
            → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m)) → find-label prog m ≡ nothing
            → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                  ≡ event-of (instr-ctrl (c-jmp m)) fs
                    ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs))

  -- scratch-dec on a NON-tag Scratch — ruled out by well-formedness (the loop counter
  -- is a tag at every scratch-dec site). The WF residual for this reg-op.
  scratch-dec-nontag : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of (instr-reg-op scratch-dec) fs
                             ++ flat-events n prog (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
  input2-inc-nontag : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                        prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just (instr-reg-op input2-inc)
                    → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                          ≡ event-of (instr-reg-op input2-inc) fs
                            ++ flat-events n prog (flat-exec-instr (instr-reg-op input2-inc) prog fs))

  -- STORE-LIVENESS witness for load-indirect: the loaded dynamic pointer targets a LIVE
  -- heap cell. This is the ONE genuinely-residual witness (LiveIn is a ConcFlatSim param
  -- fed by the allocator's blocks-disjoint); the mechanics use the PROVEN block-step.
  load-indirect-live : ∀ fs hl {w} → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                     → heapMem (floc fs) hl ≡ just w → LiveIn (falloc fs) hl

  -- load-indirect on a non-live-dynamic-pointer target (non-pointer / stack ptr /
  -- unallocated) — ruled out by well-formedness (loads hit live heap cells).
  load-indirect-bad : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                        prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just load-indirect
                    → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                          ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))

  -- Same WF witnesses/bad-case residuals for the other three heap ops (second-cell +
  -- the two stores). The store `guard` (writeLoc AtDynamic ≡ writeLocToHeap) is the
  -- heap-model consistency law; LiveIn is the store-liveness param.
  load-indirect-suc-live : ∀ fs hl {w} → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                         → heapMem (floc fs) (sucHL hl) ≡ just w → LiveIn (falloc fs) (sucHL hl)
  load-indirect-suc-bad : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                            prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                        → fetch prog (fpc fs) ≡ just load-indirect-suc
                        → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                              ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
  store-indirect-live : ∀ fs hl → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl) → LiveIn (falloc fs) hl
  store-indirect-bad : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just store-indirect
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of store-indirect fs ++ flat-events n prog (flat-exec-instr store-indirect prog fs))
  -- HEAP/STACK DISJOINTNESS at a heap store: the write target `enc-hl hl` aliases
  -- no current-frame stack slot `rsp + slot-to-disp k`. Heap and stack occupy
  -- disjoint x86 regions — an honest layout invariant, discharged at instantiation
  -- (allocator heap-base vs the rsp frame window). Needed now that FlatCorr tracks
  -- the current-frame stack (`stack-eq`): a heap store must not perturb it.
  store-indirect-stack-disj : ∀ (s : X.State) (hl : HeapLocation) →
      ∀ k → (X.readReg (X.State.regs s) rsp + slot-to-disp k ≡ enc-hl hl) → ⊥
  store-indirect-suc-stack-disj : ∀ (s : X.State) (hl : HeapLocation) →
      ∀ k → (X.readReg (X.State.regs s) rsp + slot-to-disp k ≡ enc-hl (sucHL hl)) → ⊥
  -- STACK-WRITE / HEAP disjointness: writing current-frame slot `slot` (x86 addr
  -- rsp+slot-to-disp slot) aliases no LIVE heap cell — symmetric to the store
  -- residuals above; the honest stack/heap layout invariant for store-at-slot.
  store-at-slot-stack-disj : ∀ (fs : FlatState) (s : X.State) (slot : Slot) →
      ∀ hl' → LiveIn (falloc fs) hl' → (X.readReg (X.State.regs s) rsp + slot-to-disp slot ≡ enc-hl hl') → ⊥
  store-indirect-suc-live : ∀ fs hl → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl) → LiveIn (falloc fs) (sucHL hl)
  store-indirect-suc-bad : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                             prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                         → fetch prog (fpc fs) ≡ just store-indirect-suc
                         → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                               ≡ event-of store-indirect-suc fs ++ flat-events n prog (flat-exec-instr store-indirect-suc prog fs))

  -- load-from-slot on an UNINITIALISED slot (`stackMem … slot ≡ nothing`): the abstract
  -- machine HALTS (exec-load-from-slot-with-value nothing → halted := true) and so does
  -- the concrete `mov rax, [rsp+disp]` from unmapped memory. A WF residual (a live cata
  -- never loads an unwritten slot), same class as `load-indirect-bad`.
  load-from-slot-empty : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                           prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
                       → fetch prog (fpc fs) ≡ just (load-from-slot slot)
                       → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                             ≡ event-of (load-from-slot slot) fs ++ flat-events n prog (flat-exec-instr (load-from-slot slot) prog fs))
  -- restore-input on an uninitialised slot: both machines halt (same as load-from-slot-empty).
  restore-input-empty : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                          prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
                      → fetch prog (fpc fs) ≡ just (restore-input slot)
                      → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                            ≡ event-of (restore-input slot) fs ++ flat-events n prog (flat-exec-instr (restore-input slot) prog fs))
  -- worklist-pop from an empty worklist slot: both machines halt (as load-from-slot-empty).
  worklist-pop-empty : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just (worklist-pop slot)
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of (worklist-pop slot) fs ++ flat-events n prog (flat-exec-instr (worklist-pop slot) prog fs))

  -- ARITH SIGOP interpretation contract (D061): the internal-producer obligation,
  -- discharged OFFLINE from the arith proofs (dispatch-arith-preserves + arith-block-
  -- correct). For a Pure SigOp, the arith-env maps its symbol to the block `pl`, and
  -- dispatching `pl` yields the CompiledCorr of the flat post-state. `sigop-step` proves
  -- the run-events mechanics AROUND this (pc-alignment + run-events-arith), so this
  -- states exactly the residual arith obligation — nothing about the machine loop.
  arith-sigop-contract : ∀ (env : RTx.ArithEnv val-x86-64) prog fs s {A B} (si : SigOpInfo A B)
                       → effect si ≡ Pure → CompiledCorr prog fs s → fetch prog (fpc fs) ≡ just (instr-sigop si)
                       → Σ (List XInstr × ℕ) (λ pl → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                           × CompiledCorr prog (flat-exec-instr (instr-sigop si) prog fs)
                               (uncurry (dispatch-arith val-x86-64) pl s))

  -- EXTERNAL SIGOP (Emits/Halts) interpretation contract — the value-carrying observable,
  -- the honest per-(SigOp×target) TrustedBase (D061). Bundles: env maps the symbol to
  -- `nothing` (external, not an arith block); the `ev` extractor emits EXACTLY the
  -- abstract `event-of` (`ev ≡ machine-event` — matching the observable value); and the
  -- concrete post-call state (ret-past) is the CompiledCorr of the flat post-state.
  -- `sigop-external` proves the run-events emission mechanics AROUND this.
  external-sigop-contract : ∀ (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                              prog fs s {A B} (si : SigOpInfo A B) → CompiledCorr prog fs s
                          → fetch prog (fpc fs) ≡ just (instr-sigop si)
                          → (env (once-symbol-path (SigOpInfo.name si)) ≡ nothing)
                            × (ev (once-symbol-path (SigOpInfo.name si)) s ≡ event-of (instr-sigop si) fs)
                            × CompiledCorr prog (flat-exec-instr (instr-sigop si) prog fs) (RTx.ret-past s)

-- The event-trace induction, fully with-FREE (J-style aux bridges for every case
-- split — no `with … in` goal-abstraction). `ccc-step` is the reusable CCC engine:
-- one abstract step ↦ its compiled block (block-step-any) mirrored into run-events
-- (the proven block-run-exec), then recurse (events-agree). Mutual on the fuel n.
mutual
  events-agree : ∀ N (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                   prog fs s → CompiledCorr prog fs s
               → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s ≡ flat-events N prog fs)
  events-agree zero    ev env prog fs s cc = 0 , refl
  events-agree (suc n) ev env prog fs s cc = go-h (halted (floc fs)) refl
    where go-h : ∀ (b : Bool) → halted (floc fs) ≡ b
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ flat-events-step b n prog fs)
          go-h true  eqh = 1 , RTx.run-events-halted val-x86-64 ev env 0 (compile-trace prog) s
                                 (trans (C.halt-eq (dataCorr cc)) eqh)
          go-h false eqh = events-running n ev env prog fs s cc eqh

  -- Running step: `flat-events (suc n)` (halted false) reduces to the abstract
  -- fetch-dispatch; case the fetch via a J-style `go` bridge and route.
  events-running : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                     prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                              ≡ flat-events-fetch (fetch prog (fpc fs)) n prog fs)
  events-running n ev env prog fs s cc h = go (fetch prog (fpc fs)) refl
    where go : ∀ (mi : Maybe AbstractInstr) → fetch prog (fpc fs) ≡ mi
             → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                          ≡ flat-events-fetch mi n prog fs)
          go nothing  eqf = events-running-end   n ev env prog fs s cc h eqf
          go (just i) eqf = events-running-fetch n ev env prog fs s i cc h eqf

  -- Per-instruction dispatch (with-free constructor matching on `i`). c-label is a
  -- CCC step (event-of []; flat-exec-instr leaves `floc` unchanged so halted-post =
  -- h). All other `i` route to the residual for now.
  events-running-fetch : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                           prog fs s i → CompiledCorr prog fs s → halted (floc fs) ≡ false
                       → fetch prog (fpc fs) ≡ just i
                       → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                             ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs))
  -- The straight-line CCC cases: register moves / reg-ops / load-tag-lit / c-label all
  -- leave `halted` untouched (exec-abstract is a `record {regs=…}` or flat-exec-instr
  -- just bumps fpc), so halted-post = h and event-of = [] (refl). Each feeds its PROVEN
  -- block-step lemma directly to ccc-step-bs (no block-step-any dispatcher — deleted).
  events-running-fetch n ev env prog fs s mov-to-output          cc h ftq = ccc-step-bs n ev env prog fs s mov-to-output          (block-step-mov-to-output          prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s mov-to-input           cc h ftq = ccc-step-bs n ev env prog fs s mov-to-input           (block-step-mov-to-input           prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s mov-output-to-input2   cc h ftq = ccc-step-bs n ev env prog fs s mov-output-to-input2   (block-step-mov-output-to-input2   prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s mov-input2-to-output   cc h ftq = ccc-step-bs n ev env prog fs s mov-input2-to-output   (block-step-mov-input2-to-output   prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-reg-op scratch-one)        cc h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op scratch-one)        (block-step-scratch-one        prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-reg-op scratch-zero)       cc h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op scratch-zero)       (block-step-scratch-zero       prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-reg-op input2-zero)        cc h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op input2-zero)        (block-step-input2-zero        prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-reg-op scratch-load-count) cc h ftq = ccc-step-bs n ev env prog fs s (instr-reg-op scratch-load-count) (block-step-scratch-load-count prog fs s cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-reg-op scratch-dec) cc h ftq = scratch-dec-step n ev env prog fs s cc h ftq
  events-running-fetch n ev env prog fs s (instr-reg-op input2-inc) cc h ftq = input2-inc-step n ev env prog fs s cc h ftq
  events-running-fetch n ev env prog fs s load-indirect cc h ftq = load-indirect-step n ev env prog fs s cc h ftq
  events-running-fetch n ev env prog fs s load-indirect-suc cc h ftq = load-indirect-suc-step n ev env prog fs s cc h ftq
  events-running-fetch n ev env prog fs s store-indirect cc h ftq = store-indirect-step n ev env prog fs s cc h ftq
  events-running-fetch n ev env prog fs s store-indirect-suc cc h ftq = store-indirect-suc-step n ev env prog fs s cc h ftq
  events-running-fetch n ev env prog fs s (load-from-slot slot) cc h ftq = load-from-slot-step n ev env prog fs s slot cc h ftq
  events-running-fetch n ev env prog fs s (store-at-slot slot) cc h ftq =
    ccc-step-bs n ev env prog fs s (store-at-slot slot)
      (block-step-store-at-slot prog fs s slot cc h ftq (store-at-slot-stack-disj fs s slot)) refl h
  events-running-fetch n ev env prog fs s (restore-input slot) cc h ftq = restore-input-step n ev env prog fs s slot cc h ftq
  events-running-fetch n ev env prog fs s (worklist-push slot) cc h ftq =
    ccc-step-bs n ev env prog fs s (worklist-push slot)
      (block-step-worklist-push prog fs s slot cc h ftq (store-at-slot-stack-disj fs s slot)) refl h
  events-running-fetch n ev env prog fs s (worklist-pop slot) cc h ftq = worklist-pop-step n ev env prog fs s slot cc h ftq
  -- Trivial cata bookkeeping (x86-len 0, flat identity): proven block-step ⇒ ccc-step-bs.
  events-running-fetch n ev env prog fs s (worklist-init k) cc h ftq = ccc-step-bs n ev env prog fs s (worklist-init k) (block-step-worklist-init prog fs s k cc h ftq) refl h
  events-running-fetch n ev env prog fs s (worklist-check k) cc h ftq = ccc-step-bs n ev env prog fs s (worklist-check k) (block-step-worklist-check prog fs s k cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-reclaim-to k) cc h ftq = ccc-step-bs n ev env prog fs s (instr-reclaim-to k) (block-step-reclaim-to prog fs s k cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-load-tag-lit k) cc h ftq = ccc-step-bs n ev env prog fs s (instr-load-tag-lit k) (block-step-load-tag-lit prog fs s k cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-ctrl (c-label m)) cc h ftq = ccc-step-bs n ev env prog fs s (instr-ctrl (c-label m)) (block-step-c-label prog fs s m cc h ftq) refl h
  events-running-fetch n ev env prog fs s (instr-ctrl (c-jmp m)) cc h ftq = cjmp-step n ev env prog fs s m cc h ftq
  events-running-fetch n ev env prog fs s (instr-sigop si) cc h ftq = sigop-step n ev env prog fs s si cc h ftq
  events-running-fetch n ev env prog fs s i cc h ftq =
    events-running-fetch-rest n ev env prog fs s i cc h ftq

  -- The reusable CCC engine, GENERALISED to take an explicit BlockStep: one abstract
  -- step `i` (event-of i fs = [], flat step leaves the machine running: hpost) ↦ its
  -- compiled block `X.exec (x86-len i)` (the given BlockStep), mirrored into run-events
  -- (block-run-exec), then recurse via events-agree. Taking the BlockStep explicitly
  -- lets witnessed cases (c-jmp with its found-label, …) feed their PROVEN block-step
  -- lemma rather than routing through block-step-any's residual.
  ccc-step-bs : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                  prog fs s i → BlockStep prog fs s i → event-of i fs ≡ []
              → halted (floc (flat-exec-instr i prog fs)) ≡ false
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                    ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs))
  ccc-step-bs n ev env prog fs s i bs ev[] hpost = (x86-len i + proj₁ rec) , result
    where rec = events-agree n ev env prog (flat-exec-instr i prog fs) (proj₁ bs) (proj₂ (proj₂ bs))
          result : RTx.run-events val-x86-64 ev env (x86-len i + proj₁ rec) (compile-trace prog) s
                 ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs)
          result rewrite ev[] =
            trans (block-run-exec ev env (x86-len i) (proj₁ rec) (compile-trace prog) s
                     (proj₁ (proj₂ bs)) (trans (C.halt-eq (dataCorr (proj₂ (proj₂ bs)))) hpost))
                  (proj₂ rec)

  -- CONTROL c-jmp: case the found label (J-bridge on find-label, no with). Found ⇒
  -- do-jump just bumps fpc (halted preserved: hpost=h) and the PROVEN block-step-c-jmp
  -- gives the BlockStep ⇒ ccc-step-bs. Missing ⇒ both machines halt on the missing
  -- label — the small `cjmp-miss` residual (the label-missing halt correspondence).
  cjmp-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                prog fs s m → CompiledCorr prog fs s → halted (floc fs) ≡ false
              → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m))
              → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                    ≡ event-of (instr-ctrl (c-jmp m)) fs
                      ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs))
  cjmp-step n ev env prog fs s m cc h ftq = go-fl (find-label prog m) refl
    where go-fl : ∀ (mj : Maybe ℕ) → find-label prog m ≡ mj
                → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                      ≡ event-of (instr-ctrl (c-jmp m)) fs
                        ++ flat-events n prog (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs))
          go-fl (just j) fl-eq =
            ccc-step-bs n ev env prog fs s (instr-ctrl (c-jmp m))
              (block-step-c-jmp prog fs s m j cc h ftq fl-eq) refl hpost
            where hpost : halted (floc (flat-exec-instr (instr-ctrl (c-jmp m)) prog fs)) ≡ false
                  hpost rewrite fl-eq = h
          go-fl nothing fl-eq = cjmp-miss n ev env prog fs s m cc h ftq fl-eq

  -- REG-OP scratch-dec: case the Scratch value (J-bridge, no with). A tag ⇒ the PROVEN
  -- block-step-scratch-dec applies (reg-op preserves halted: hpost=h) ⇒ ccc-step-bs.
  -- A non-tag ⇒ the WF residual (a loop counter is always a tag at scratch-dec).
  scratch-dec-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                       prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-reg-op scratch-dec)
                   → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                         ≡ event-of (instr-reg-op scratch-dec) fs
                           ++ flat-events n prog (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
  scratch-dec-step n ev env prog fs s cc h ftq = go-sv (readReg (regs (floc fs)) Scratch) refl
    where go-sv : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Scratch ≡ sv
                → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                      ≡ event-of (instr-reg-op scratch-dec) fs
                        ++ flat-events n prog (flat-exec-instr (instr-reg-op scratch-dec) prog fs))
          go-sv (SV-Tag k)   sc-eq =
            ccc-step-bs n ev env prog fs s (instr-reg-op scratch-dec)
              (block-step-scratch-dec prog fs s k cc h ftq sc-eq) refl h
          go-sv (SV-Ptr _)   sc-eq = scratch-dec-nontag n ev env prog fs s cc h ftq
          go-sv (SV-Lit _ _) sc-eq = scratch-dec-nontag n ev env prog fs s cc h ftq
          go-sv (SV-Code _)  sc-eq = scratch-dec-nontag n ev env prog fs s cc h ftq

  -- REG-OP input2-inc: mirror of scratch-dec on Input2 (block-step-input2-inc exists).
  input2-inc-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                      prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                  → fetch prog (fpc fs) ≡ just (instr-reg-op input2-inc)
                  → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                        ≡ event-of (instr-reg-op input2-inc) fs
                          ++ flat-events n prog (flat-exec-instr (instr-reg-op input2-inc) prog fs))
  input2-inc-step n ev env prog fs s cc h ftq = go-sv (readReg (regs (floc fs)) Input2) refl
    where go-sv : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input2 ≡ sv
                → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                      ≡ event-of (instr-reg-op input2-inc) fs
                        ++ flat-events n prog (flat-exec-instr (instr-reg-op input2-inc) prog fs))
          go-sv (SV-Tag k)   i2-eq =
            ccc-step-bs n ev env prog fs s (instr-reg-op input2-inc)
              (block-step-input2-inc prog fs s k cc h ftq i2-eq) refl h
          go-sv (SV-Ptr _)   i2-eq = input2-inc-nontag n ev env prog fs s cc h ftq
          go-sv (SV-Lit _ _) i2-eq = input2-inc-nontag n ev env prog fs s cc h ftq
          go-sv (SV-Code _)  i2-eq = input2-inc-nontag n ev env prog fs s cc h ftq

  -- MEMORY load-indirect: case the Input1 pointer + the heap cell (both J-bridges, no
  -- with). A live dynamic pointer to an allocated cell ⇒ the PROVEN block-step-load-
  -- indirect ⇒ ccc-step-bs. The `LiveIn` store-liveness witness is a ConcFlatSim param,
  -- so it comes from the WF residual `load-indirect-live`; bad shapes (non-pointer /
  -- stack pointer / unallocated) ⇒ `load-indirect-bad` (WF: loads hit live heap cells).
  load-indirect-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just load-indirect
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
  load-indirect-step n ev env prog fs s cc h ftq = go-ptr (readReg (regs (floc fs)) Input1) refl
    where go-mem : ∀ hl → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → ∀ (mw : Maybe (StoredValue FS)) → heapMem (floc fs) hl ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
          go-mem hl i-eq (just w) h-eq =
            ccc-step-bs n ev env prog fs s load-indirect
              (block-step-load-indirect prog fs s hl w cc h ftq i-eq
                 (load-indirect-live fs hl i-eq h-eq) h-eq)
              refl hpost
            where hpost : halted (floc (flat-exec-instr load-indirect prog fs)) ≡ false
                  hpost rewrite i-eq | h-eq = h
          go-mem hl i-eq nothing h-eq = load-indirect-bad n ev env prog fs s cc h ftq
          go-ptr : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ sv
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect fs ++ flat-events n prog (flat-exec-instr load-indirect prog fs))
          go-ptr (SV-Ptr (AtDynamic hl)) i-eq = go-mem hl i-eq (heapMem (floc fs) hl) refl
          go-ptr (SV-Ptr (AtStack _ _))  i-eq = load-indirect-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Tag _)              i-eq = load-indirect-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Lit _ _)            i-eq = load-indirect-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Code _)             i-eq = load-indirect-bad n ev env prog fs s cc h ftq

  -- MEMORY load-indirect-suc: as load-indirect but the SECOND cell (sucHL hl).
  load-indirect-suc-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                             prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                         → fetch prog (fpc fs) ≡ just load-indirect-suc
                         → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                               ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
  load-indirect-suc-step n ev env prog fs s cc h ftq = go-ptr (readReg (regs (floc fs)) Input1) refl
    where go-mem : ∀ hl → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
                 → ∀ (mw : Maybe (StoredValue FS)) → heapMem (floc fs) (sucHL hl) ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
          go-mem hl i-eq (just w) h-eq =
            ccc-step-bs n ev env prog fs s load-indirect-suc
              (block-step-load-indirect-suc prog fs s hl w cc h ftq i-eq
                 (load-indirect-suc-live fs hl i-eq h-eq) h-eq)
              refl hpost
            where hpost : halted (floc (flat-exec-instr load-indirect-suc prog fs)) ≡ false
                  hpost rewrite i-eq | h-eq = h
          go-mem hl i-eq nothing h-eq = load-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ sv
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of load-indirect-suc fs ++ flat-events n prog (flat-exec-instr load-indirect-suc prog fs))
          go-ptr (SV-Ptr (AtDynamic hl)) i-eq = go-mem hl i-eq (heapMem (floc fs) (sucHL hl)) refl
          go-ptr (SV-Ptr (AtStack _ _))  i-eq = load-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Tag _)              i-eq = load-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Lit _ _)            i-eq = load-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Code _)             i-eq = load-indirect-suc-bad n ev env prog fs s cc h ftq

  -- STACK load-from-slot: J-bridge on the slot's abstract value. `just w` ⇒ the PROVEN
  -- block-step-load-from-slot (the stack read pinned by stack-eq) ⇒ ccc-step-bs; the
  -- empty-slot `nothing` ⇒ `load-from-slot-empty` (both machines halt — WF residual).
  load-from-slot-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                          prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
                      → fetch prog (fpc fs) ≡ just (load-from-slot slot)
                      → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                            ≡ event-of (load-from-slot slot) fs ++ flat-events n prog (flat-exec-instr (load-from-slot slot) prog fs))
  load-from-slot-step n ev env prog fs s slot cc h ftq =
    go-mem (stackMem (floc fs) (current-frame (falloc fs)) slot) refl
    where go-mem : ∀ (mw : Maybe (StoredValue FS)) → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (load-from-slot slot) fs ++ flat-events n prog (flat-exec-instr (load-from-slot slot) prog fs))
          go-mem (just w) st-eq =
            ccc-step-bs n ev env prog fs s (load-from-slot slot)
              (block-step-load-from-slot prog fs s slot w cc h ftq st-eq)
              refl hpost
            where hpost : halted (floc (flat-exec-instr (load-from-slot slot) prog fs)) ≡ false
                  hpost rewrite st-eq = h
          go-mem nothing st-eq = load-from-slot-empty n ev env prog fs s slot cc h ftq

  -- STACK restore-input: identical to load-from-slot but writes Input1 (rdi).
  restore-input-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                         prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
                     → fetch prog (fpc fs) ≡ just (restore-input slot)
                     → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                           ≡ event-of (restore-input slot) fs ++ flat-events n prog (flat-exec-instr (restore-input slot) prog fs))
  restore-input-step n ev env prog fs s slot cc h ftq =
    go-mem (stackMem (floc fs) (current-frame (falloc fs)) slot) refl
    where go-mem : ∀ (mw : Maybe (StoredValue FS)) → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (restore-input slot) fs ++ flat-events n prog (flat-exec-instr (restore-input slot) prog fs))
          go-mem (just w) st-eq =
            ccc-step-bs n ev env prog fs s (restore-input slot)
              (block-step-restore-input prog fs s slot w cc h ftq st-eq)
              refl hpost
            where hpost : halted (floc (flat-exec-instr (restore-input slot) prog fs)) ≡ false
                  hpost rewrite st-eq = h
          go-mem nothing st-eq = restore-input-empty n ev env prog fs s slot cc h ftq

  -- STACK worklist-pop: identical to load-from-slot (same abstract sem + lowering).
  worklist-pop-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                        prog fs s slot → CompiledCorr prog fs s → halted (floc fs) ≡ false
                    → fetch prog (fpc fs) ≡ just (worklist-pop slot)
                    → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                          ≡ event-of (worklist-pop slot) fs ++ flat-events n prog (flat-exec-instr (worklist-pop slot) prog fs))
  worklist-pop-step n ev env prog fs s slot cc h ftq =
    go-mem (stackMem (floc fs) (current-frame (falloc fs)) slot) refl
    where go-mem : ∀ (mw : Maybe (StoredValue FS)) → stackMem (floc fs) (current-frame (falloc fs)) slot ≡ mw
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (worklist-pop slot) fs ++ flat-events n prog (flat-exec-instr (worklist-pop slot) prog fs))
          go-mem (just w) st-eq =
            ccc-step-bs n ev env prog fs s (worklist-pop slot)
              (block-step-worklist-pop prog fs s slot w cc h ftq st-eq)
              refl hpost
            where hpost : halted (floc (flat-exec-instr (worklist-pop slot) prog fs)) ≡ false
                  hpost rewrite st-eq = h
          go-mem nothing st-eq = worklist-pop-empty n ev env prog fs s slot cc h ftq

  -- MEMORY store-indirect: case the Output-target pointer. A live dynamic pointer ⇒ the
  -- PROVEN block-step-store-indirect (LiveIn from store-indirect-live; the writeLoc↔heap
  -- guard from store-indirect-guard) ⇒ ccc-step-bs. Bad shapes ⇒ store-indirect-bad.
  store-indirect-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                          prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                      → fetch prog (fpc fs) ≡ just store-indirect
                      → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                            ≡ event-of store-indirect fs ++ flat-events n prog (flat-exec-instr store-indirect prog fs))
  store-indirect-step n ev env prog fs s cc h ftq = go-ptr (readReg (regs (floc fs)) Input1) refl
    where go-ptr : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ sv
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of store-indirect fs ++ flat-events n prog (flat-exec-instr store-indirect prog fs))
          go-ptr (SV-Ptr (AtDynamic hl)) i-eq =
            ccc-step-bs n ev env prog fs s store-indirect
              (block-step-store-indirect prog fs s hl cc h ftq i-eq
                 (store-indirect-live fs hl i-eq) (store-guard fs hl)
                 (store-indirect-stack-disj s hl))
              refl hpost
            where hpost : halted (floc (flat-exec-instr store-indirect prog fs)) ≡ false
                  hpost rewrite i-eq = trans (writeLoc-halted (floc fs) (AtDynamic hl) (readReg (regs (floc fs)) Output)) h
          go-ptr (SV-Ptr (AtStack _ _))  i-eq = store-indirect-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Tag _)              i-eq = store-indirect-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Lit _ _)            i-eq = store-indirect-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Code _)             i-eq = store-indirect-bad n ev env prog fs s cc h ftq

  -- MEMORY store-indirect-suc: as store-indirect but the SECOND cell (sucHL hl).
  store-indirect-suc-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                              prog fs s → CompiledCorr prog fs s → halted (floc fs) ≡ false
                          → fetch prog (fpc fs) ≡ just store-indirect-suc
                          → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                                ≡ event-of store-indirect-suc fs ++ flat-events n prog (flat-exec-instr store-indirect-suc prog fs))
  store-indirect-suc-step n ev env prog fs s cc h ftq = go-ptr (readReg (regs (floc fs)) Input1) refl
    where go-ptr : ∀ (sv : StoredValue FS) → readReg (regs (floc fs)) Input1 ≡ sv
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of store-indirect-suc fs ++ flat-events n prog (flat-exec-instr store-indirect-suc prog fs))
          go-ptr (SV-Ptr (AtDynamic hl)) i-eq =
            ccc-step-bs n ev env prog fs s store-indirect-suc
              (block-step-store-indirect-suc prog fs s hl cc h ftq i-eq
                 (store-indirect-suc-live fs hl i-eq) (store-guard fs (sucHL hl))
                 (store-indirect-suc-stack-disj s hl))
              refl hpost
            where hpost : halted (floc (flat-exec-instr store-indirect-suc prog fs)) ≡ false
                  hpost rewrite i-eq = trans (writeLoc-halted (floc fs) (AtDynamic (sucHL hl)) (readReg (regs (floc fs)) Output)) h
          go-ptr (SV-Ptr (AtStack _ _))  i-eq = store-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Tag _)              i-eq = store-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Lit _ _)            i-eq = store-indirect-suc-bad n ev env prog fs s cc h ftq
          go-ptr (SV-Code _)             i-eq = store-indirect-suc-bad n ev env prog fs s cc h ftq

  -- SIGOP engine. Split on effect si (J-bridge, no with): Pure ⇒ arith — the run-events
  -- mechanics are PROVEN (sigop-run-arith: pc-align + run-events-arith), event-of is []
  -- (event-of-pure), recurse via events-agree on the flat post-state; the only residual
  -- is `arith-sigop-contract` (the offline arith obligation). Emits/Halts ⇒ external
  -- (sigop-external-rest, the value-carrying observable — next).
  sigop-step : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                 prog fs s {A B} (si : SigOpInfo A B) → CompiledCorr prog fs s → halted (floc fs) ≡ false
               → fetch prog (fpc fs) ≡ just (instr-sigop si)
               → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                     ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs))
  sigop-step n ev env prog fs s {A} {B} si cc h ftq = go-eff (effect si) refl
    where go-eff : ∀ (e : EffectShape B) → effect si ≡ e
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs))
          go-eff Pure eqe = suc (proj₁ rec) , goal
            where contract = arith-sigop-contract env prog fs s si eqe cc ftq
                  pl  = proj₁ contract
                  rec = events-agree n ev env prog (flat-exec-instr (instr-sigop si) prog fs)
                          (uncurry (dispatch-arith val-x86-64) pl s) (proj₂ (proj₂ contract))
                  goal : RTx.run-events val-x86-64 ev env (suc (proj₁ rec)) (compile-trace prog) s
                       ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs)
                  goal rewrite event-of-pure si fs eqe =
                    trans (sigop-run-arith ev env (proj₁ rec) prog fs s si pl cc h ftq (proj₁ (proj₂ contract)))
                          (proj₂ rec)
          go-eff (Emits _) eqe = sigop-external n ev env prog fs s si cc h ftq
          go-eff (Halts _) eqe = sigop-external n ev env prog fs s si cc h ftq

  -- EXTERNAL SIGOP engine: run-events-external EMITS `ev lbl s` then continues past the
  -- call (sigop-run-external, PROVEN); the external contract pins `ev ≡ event-of` and the
  -- ret-past state; recurse via events-agree. The only residual is external-sigop-contract
  -- (the honest per-target observable obligation). Emits AND Halts share this — for Halts
  -- the flat post-state is halted and both tails run to [] (events-agree's halted case).
  sigop-external : ∀ n (ev : RTx.EvExtractor val-x86-64) (env : RTx.ArithEnv val-x86-64)
                     prog fs s {A B} (si : SigOpInfo A B) → CompiledCorr prog fs s → halted (floc fs) ≡ false
                 → fetch prog (fpc fs) ≡ just (instr-sigop si)
                 → Σ ℕ (λ M → RTx.run-events val-x86-64 ev env M (compile-trace prog) s
                       ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs))
  sigop-external n ev env prog fs s si cc h ftq = suc (proj₁ rec) , goal
    where contract = external-sigop-contract ev env prog fs s si cc ftq
          rec = events-agree n ev env prog (flat-exec-instr (instr-sigop si) prog fs)
                  (RTx.ret-past s) (proj₂ (proj₂ contract))
          goal : RTx.run-events val-x86-64 ev env (suc (proj₁ rec)) (compile-trace prog) s
               ≡ event-of (instr-sigop si) fs ++ flat-events n prog (flat-exec-instr (instr-sigop si) prog fs)
          goal = trans (sigop-run-external ev env (proj₁ rec) prog fs s si cc h ftq (proj₁ contract))
                 (trans (cong (_++ RTx.run-events val-x86-64 ev env (proj₁ rec) (compile-trace prog) (RTx.ret-past s))
                              (proj₁ (proj₂ contract)))
                        (cong (event-of (instr-sigop si) fs ++_) (proj₂ rec)))
