-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.EventEngine
--
-- THE EVENT ENGINE, stated once for every arch (plan 0.65 G2 item 4, slice 3).
--
-- `ConcFlatSim` is the largest single file in the cluster and the one every
-- new target would otherwise have to write again: the fuel induction relating
-- the concrete `run-events` trace to the abstract `flat-events`, the
-- per-instruction dispatch, and the invariant threaded through both. Slice 2
-- built the interface it needs from an arch (`BlockSteps`); this module is
-- what consumes that interface.
--
-- WHAT MAKES IT GENERIC, and it is not that the machine went away. The engine
-- touches the machine in exactly four ways, and each is a parameter here:
--
--   the EMITTER          `compile-abstract` and the label scans, through
--                        `FlatComposition`'s law surface — 39 lowering clauses
--                        at the arch, none of them here.
--   the TRACE LOOP       `RunTraceCore.RunTrace`, which was ALREADY generic;
--                        each arch's `RunTrace` module is a ~40-line
--                        instantiation of it, so the event layer is a
--                        parameter surface rather than a subsystem.
--   the STEP             `mexecInstr`/`exec`, plus the ONE ISA enumeration the
--                        trace backbone needs (`nonhalt-noncall`).
--   the BLOCK STEPS      `BlockSteps`, slice 2's record.
--
-- Everything else — `FlatInv`, the run context, the well-formedness layer — is
-- about the ABSTRACT machine and was never arch-specific to begin with.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; NonZero)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; drop)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CCC.FrameSemantics using (FrameSemantics; frame-word)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (RegRoles)
import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles as RR
open import Once.CCC.Machine.SMCore using (AbstractTrace; AbstractInstr; instr-sigop)
open import Once.SigOp.Info using (SigOpInfo; effect; Pure)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.CCC.Label using (Label; LabelId; _≡ᵇᴸ_)
open import Once.CanonicalName using (CanonicalName)
open import Once.Denotation.Trace using (SigOpEvent)
import Once.Adequacy.ArchCorrectness.FlatCore.HeadView as HV

module Once.Adequacy.ArchCorrectness.FlatCore.EventEngine
  -- Plan 0.63 (D089): the DEFINITION'S identity, which keys its labels.
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
  (xpc : State → ℕ)
  (modulus : ℕ)
  ------------------------------------------------------------------
  -- THE EMITTER AND THE ISA VIEW — `FlatComposition`'s own parameter list,
  -- passed straight through so this module can instantiate it rather than
  -- take a dozen of its lemmas one at a time.
  ------------------------------------------------------------------
  (Instr : Set)
  (compile-abstract : AbstractInstr → List Instr)
  (compile-trace : AbstractTrace → List Instr)
  (ct-nil  : compile-trace [] ≡ [])
  (ct-cons : ∀ i is → compile-trace (i ∷ is) ≡ compile-abstract i ++ compile-trace is)
  (mfetch      : List Instr → ℕ → Maybe Instr)
  (mfetch-nil  : ∀ n → mfetch [] n ≡ nothing)
  (mfetch-zero : ∀ x xs → mfetch (x ∷ xs) zero ≡ just x)
  (mfetch-suc  : ∀ x xs n → mfetch (x ∷ xs) (suc n) ≡ mfetch xs n)
  (is-label?     : Instr → Bool)
  (mk-label      : Label → Instr)
  (find-label-go : Label → List Instr → ℕ → Maybe ℕ)
  (find-label-nil : ∀ (t : Label) (xi : ℕ) → find-label-go t [] xi ≡ nothing)
  (skip-law : ∀ (t : Label) (i : Instr) (rest : List Instr) (xi : ℕ)
            → is-label? i ≡ false
            → find-label-go t (i ∷ rest) xi ≡ find-label-go t rest (suc xi))
  (label-hit : ∀ (ℓ t : Label) (rest : List Instr) (xi : ℕ)
             → (ℓ ≡ᵇᴸ t) ≡ true
             → find-label-go t (mk-label ℓ ∷ rest) xi ≡ just xi)
  (label-miss : ∀ (ℓ t : Label) (rest : List Instr) (xi : ℕ)
              → (ℓ ≡ᵇᴸ t) ≡ false
              → find-label-go t (mk-label ℓ ∷ rest) xi ≡ find-label-go t rest (suc xi))
  (headView : ∀ i → HV.HeadView FS Instr compile-abstract is-label? mk-label i)
  -- …and the label scan as the CORRESPONDENCE names it (`code-eq`). Taken
  -- rather than defined from `find-label-go`, so the arch passes the very term
  -- its own `CompiledCorr` instance was built with.
  (find-label : List Instr → Label → Maybe ℕ)
  ------------------------------------------------------------------
  -- THE MACHINE'S STEP, single and fuel-bounded.
  ------------------------------------------------------------------
  (mexecInstr : List Instr → State → Instr → Maybe State)
  (exec : ℕ → List Instr → State → Maybe State)
  -- …and HOW FUEL PEELS, as six premise-free readouts. This is the only thing
  -- the block backbone needs from `exec`'s definition, and stating it this way
  -- keeps the proof `with`-free: an opaque parameter does not reduce, so the
  -- equations have to be handed over rather than computed. Each is one line at
  -- an arch (`refl` after a rewrite of the boolean).
  (exec-zero      : ∀ prog s → exec 0 prog s ≡ just s)
  (exec-halted    : ∀ n prog s → xhalted s ≡ true → exec (suc n) prog s ≡ just s)
  (exec-end       : ∀ n prog s {s'} → xhalted s ≡ false
                  → mfetch prog (xpc s) ≡ nothing
                  → exec (suc n) prog s ≡ just s' → xhalted s' ≡ true)
  (exec-stuck     : ∀ n prog s j → xhalted s ≡ false → mfetch prog (xpc s) ≡ just j
                  → mexecInstr prog s j ≡ nothing → exec (suc n) prog s ≡ nothing)
  (exec-step-halt : ∀ n prog s j s₁ → xhalted s ≡ false → mfetch prog (xpc s) ≡ just j
                  → mexecInstr prog s j ≡ just s₁ → xhalted s₁ ≡ true
                  → exec (suc n) prog s ≡ just s₁)
  (exec-step-run  : ∀ n prog s j s₁ → xhalted s ≡ false → mfetch prog (xpc s) ≡ just j
                  → mexecInstr prog s j ≡ just s₁ → xhalted s₁ ≡ false
                  → exec (suc n) prog s ≡ exec n prog s₁)
  ------------------------------------------------------------------
  -- THE TRACE LOOP's telescope — `RunTraceCore.RunTrace`'s, which is where
  -- the event layer already lived. `Payload` is the arch's arith-block
  -- representation, with its value function baked into `dispatchArith`.
  ------------------------------------------------------------------
  (Payload : Set)
  (matchCall : Instr → Maybe String)
  (ret-past : State → State)
  (dispatchArith : Payload → State → State)
  -- the REAL extractor and env this arch runs with. Pinned, not quantified:
  -- the SigOp contracts are false over an arbitrary `ev`/`env` (2026-07-30).
  (ev-arch : String → State → List SigOpEvent)
  (arith-env : List Instr → String → Maybe Payload)
  -- HOW A SIGOP IS LOWERED, which is the same on every target: to ONE call by
  -- symbol. Three lines, and they are what let the SigOp reductions below be
  -- written once — `matchCall` recognising exactly the instruction the emitter
  -- produced is the whole content of the arith/external dispatch.
  (sigop-call : String → Instr)
  (sigop-lowering : ∀ {A B} (si : SigOpInfo A B)
                  → compile-abstract (instr-sigop si)
                    ≡ sigop-call (once-symbol-path (SigOpInfo.name si)) ∷ [])
  (sigop-matchCall : ∀ lbl → matchCall (sigop-call lbl) ≡ just lbl)
  ------------------------------------------------------------------
  -- THE ONE ISA ENUMERATION the trace backbone needs. A step that leaves the
  -- machine RUNNING was not a `call-sym`: `execInstr (call-sym _)` always
  -- halts. Proven per arch by one clause per instruction — the only place the
  -- engine would otherwise have to know the instruction set.
  ------------------------------------------------------------------
  (nonhalt-noncall : ∀ prog s j {s₁} → mexecInstr prog s j ≡ just s₁
                   → xhalted s₁ ≡ false → matchCall j ≡ nothing)
  where

open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (maybe′)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong)

------------------------------------------------------------------------
-- THE THREE LAYERS THIS SITS ON, instantiated here rather than passed in.
-- Module application is by alias, so every one of these IS the arch's own
-- instance whenever the arch applies this engine to the same arguments.
------------------------------------------------------------------------
open import Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition FS Instr
       compile-abstract compile-trace ct-nil ct-cons
       mfetch mfetch-nil mfetch-zero mfetch-suc
       is-label? mk-label find-label-go find-label-nil skip-law
       label-hit label-miss headView
  public

open import Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence
       FS slot-size word-eq Reg roles State rreg memory xhalted
       xpc (List Instr) compile-trace find-label blk-off blk-len exec modulus
  public

open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq
  public

-- …and the data correspondence itself, which `CompiledCorrespondence` keeps
-- private (an instance re-opened publicly would clash with the `C` every arch
-- already binds). Same application, hence the same types.
import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted
open CFC using (HeapView; HDom)

------------------------------------------------------------------------
-- THE TRACE LOOP. `RT.run-events` here IS the arch's `run-events`: both are
-- the same application of `RunTraceCore.RunTrace`.
------------------------------------------------------------------------
open RegRoles roles using (in1-reg)
import Once.Arith.Backend.RunTraceCore as Core
module RT = Core.RunTrace State (List Instr) Instr Payload
                          xhalted xpc mfetch mexecInstr matchCall ret-past dispatchArith

-- unqualified, as `CompiledCorrespondence` imports it: `halted`/`regs`/… are
-- `LocState` fields that `Machine.Flat` itself picks up this way.
-- (`hiding (Instr)`: the abstract machine has an `Instr` of its own, and this
-- module's `Instr` is the CONCRETE one.)
open import Once.CCC.Machine.SMCore hiding (Instr)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fpc; falloc; floc; fclosure; fetch; flat-exec-instr)
open MemOps {FS} using (readLoc)
open import Once.CCC.Machine.FlatStoreWF FS using (FlatWF; flat-wf-step; cl-step; sv-below)
open import Once.CCC.Machine.FlatRegTagWF FS using (FlatRegTag; flat-regtag-step)

------------------------------------------------------------------------
-- THE FLAT-MACHINE INVARIANT carried through the event-trace induction.
--
-- Two arch-neutral state invariants of the abstract machine, bundled so the
-- ~19 mutually recursive members carry ONE hypothesis rather than two, plus
-- the run context that makes the residuals TRUE rather than merely unproved.
--
-- `ev`/`env` are pinned because the SigOp contracts speak about them:
-- quantified over an arbitrary `env`, `arith-sigop-contract` asserts
-- `env sym ≡ just pl`, which `env := λ _ → nothing` refutes.
------------------------------------------------------------------------
record FlatInv (ev : RT.EvExtractor) (env : RT.ArithEnv)
               (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkFlatInv
  field
    inv-wf      : FlatWF fs
    -- D097: the CLOSURE REGISTER is below the frontier too. `FlatWF` is indexed
    -- by the `LocState` and `fclosure` is a `FlatState` field, so it needs
    -- saying separately — load-bearing because the closure register's encoding
    -- must survive an allocation extending the heap view.
    inv-closure : sv-below (next-heap-ref (falloc fs)) (fclosure fs)
    inv-regtag  : FlatRegTag fs
    inv-ev      : ev ≡ ev-arch
    inv-env     : env ≡ arith-env (compile-trace prog)
    inv-run     : RunAt prog fs
open FlatInv public

-- One flat step preserves it: each component by its own flat-machine theorem
-- (no per-block-step obligation), and the run context by `reach-step`.
flat-inv-step : ∀ {ev env} (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
              → fetch prog (fpc fs) ≡ just i → halted (floc fs) ≡ false
              → FlatInv ev env prog fs → FlatInv ev env prog (flat-exec-instr i prog fs)
flat-inv-step i prog fs ftq h inv = record
  { inv-wf      = flat-wf-step i prog fs (inv-wf inv)
  ; inv-closure = cl-step i prog fs (inv-wf inv) (inv-closure inv)
  ; inv-regtag  = flat-regtag-step i prog fs (inv-regtag inv)
  ; inv-ev      = inv-ev inv
  ; inv-env     = inv-env inv
  ; inv-run     = mkRunAt (run-ir (inv-run inv)) (run-emit (inv-run inv))
                          (run-heap (inv-run inv))
                          (reach-step i fs (run-reach (inv-run inv)) ftq h)
  }

------------------------------------------------------------------------
-- WITNESS-FREE BLOCK CHAINING: if `exec L` reaches a NON-halted `s'`, then
-- every one of the L steps was non-halting (else `exec` would have stopped at
-- a halted state ≠ s'), hence non-call — so `run-events` mirrors it, emitting
-- [] and landing on `s'`. The concrete-side backbone of the whole dispatch,
-- derived purely from `exec L ≡ just s'` + `halted s' ≡ false`.
--
-- Key mechanism: in each branch the `with … in` abstraction has ALREADY
-- reduced `exec (suc L)` inside `eq`'s type, so we USE that rather than fight
-- it. Every early stop leaves `eq : just <a halted state> ≡ just s'`, whose
-- `halted = true` clashes with `hs'` (`maybe′ halted`-cong avoids
-- `just-injective`'s eta-expansion of `s'`).
------------------------------------------------------------------------
private
  t≢f : true ≡ false → ⊥
  t≢f ()
  n≢j : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  n≢j ()

block-run-exec : ∀ (ev : RT.EvExtractor) (env : RT.ArithEnv)
                   L rest cprog s {s'} → exec L cprog s ≡ just s' → xhalted s' ≡ false
               → RT.run-events ev env (L + rest) cprog s
                   ≡ RT.run-events ev env rest cprog s'
block-run-exec ev env zero rest cprog s eq hs' =
  cong (RT.run-events ev env rest cprog)
       (just-injective (trans (sym (exec-zero cprog s)) eq))
block-run-exec ev env (suc L) rest cprog s {s'} eq hs' = go-h (xhalted s) refl
  where
    go-h : ∀ (b : Bool) → xhalted s ≡ b
         → RT.run-events ev env (suc L + rest) cprog s
             ≡ RT.run-events ev env rest cprog s'
    -- HALTED ALREADY: `exec` returns `s` itself, so `s ≡ s'` and `s'` is halted
    -- too — which `hs'` denies.
    go-h true  hs = ⊥-elim (t≢f (trans (sym hs)
                      (trans (cong xhalted (just-injective
                               (trans (sym (exec-halted L cprog s hs)) eq))) hs')))
    go-h false hs = go-f (mfetch cprog (xpc s)) refl
      where
        go-f : ∀ (mi : Maybe Instr) → mfetch cprog (xpc s) ≡ mi
             → RT.run-events ev env (suc L + rest) cprog s
                 ≡ RT.run-events ev env rest cprog s'
        -- PAST THE END: `exec` halts, `s'` is halted, same clash.
        go-f nothing  ftn = ⊥-elim (t≢f (trans (sym (exec-end L cprog s hs ftn eq)) hs'))
        go-f (just j) ftq = go-e (mexecInstr cprog s j) refl
          where
            go-e : ∀ (ms : Maybe State) → mexecInstr cprog s j ≡ ms
                 → RT.run-events ev env (suc L + rest) cprog s
                     ≡ RT.run-events ev env rest cprog s'
            -- STUCK: `exec` returns nothing, but it reached `just s'`.
            go-e nothing   exn =
              ⊥-elim (n≢j (trans (sym (exec-stuck L cprog s j hs ftq exn)) eq))
            go-e (just s₁) exq = go-h1 (xhalted s₁) refl
              where
                go-h1 : ∀ (b : Bool) → xhalted s₁ ≡ b
                      → RT.run-events ev env (suc L + rest) cprog s
                          ≡ RT.run-events ev env rest cprog s'
                -- the step HALTS: `exec` stops at `s₁ ≡ s'`, halted — clash again.
                go-h1 true  h1 = ⊥-elim (t≢f (trans (sym h1)
                                   (trans (cong xhalted (just-injective
                                     (trans (sym (exec-step-halt L cprog s j s₁ hs ftq exq h1)) eq)))
                                     hs')))
                -- THE ONE REAL STEP: still running, hence not a `call-sym`, so
                -- `run-events` mirrors it with no event and we recurse.
                go-h1 false h1 =
                  trans (RT.run-events-noncall ev env (L + rest) cprog s j hs ftq
                           (nonhalt-noncall cprog s j exq h1) exq)
                        (block-run-exec ev env L rest cprog s₁
                           (trans (sym (exec-step-run L cprog s j s₁ hs ftq exq h1)) eq) hs')

------------------------------------------------------------------------
-- THE PROGRAM-END BOUNDARY, and the two SIGOP REDUCTIONS.
------------------------------------------------------------------------
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch
                              ; event-of; flat-events-halted)

-- PROGRAM END: the abstract fetch runs out, so the concrete pc — which `pc-off`
-- pins to `blk-off prog (fpc fs)` — sits past the compiled program, where the
-- fetch is `nothing` and `run-events` emits [].
events-running-end : ∀ {hv : HeapView} (n : ℕ) (ev : RT.EvExtractor) (env : RT.ArithEnv)
                       prog fs s → CompiledCorr hv prog fs s → FlatInv ev env prog fs
                   → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ nothing
                   → Σ ℕ (λ M → RT.run-events ev env M (compile-trace prog) s ≡ [])
events-running-end {hv} n ev env prog fs s cc wf h ftq =
  1 , RT.run-events-fetch-none ev env 0 (compile-trace prog) s cfetch-nothing
  where cfetch-nothing : mfetch (compile-trace prog) (xpc s) ≡ nothing
        cfetch-nothing =
          trans (cong (mfetch (compile-trace prog)) (pc-off cc))
          (trans (fetch-drop (compile-trace prog) (blk-off prog (fpc fs)))
          (trans (cong (λ z → mfetch z 0) (drop-compile prog (fpc fs)))
          (trans (cong (λ z → mfetch (compile-trace z) 0)
                       (fetch-nothing-drop prog (fpc fs) ftq))
                 (trans (cong (λ z → mfetch z 0) ct-nil) (mfetch-nil 0)))))

-- PC-ALIGNMENT AT A SIGOP: the concrete pc fetches the compiled head of
-- `instr-sigop si`, which is exactly its one call-by-symbol.
sigop-concrete-fetch : ∀ {hv : HeapView} prog fs s {A B} (si : SigOpInfo A B)
                     → CompiledCorr hv prog fs s
                     → fetch prog (fpc fs) ≡ just (instr-sigop si)
                     → mfetch (compile-trace prog) (xpc s)
                         ≡ just (sigop-call (once-symbol-path (SigOpInfo.name si)))
sigop-concrete-fetch prog fs s si cc ftq =
  trans (cong (mfetch (compile-trace prog)) (pc-off cc))
  (trans (fetch-drop (compile-trace prog) (blk-off prog (fpc fs)))
  (trans (cong (λ z → mfetch z 0) (drop-compile prog (fpc fs)))
  (trans (cong (λ z → mfetch (compile-trace z) 0)
               (fetch-just-drop prog (fpc fs) (instr-sigop si) ftq))
  (trans (cong (λ z → mfetch z 0) (ct-cons (instr-sigop si) (drop (suc (fpc fs)) prog)))
  (trans (cong (λ z → mfetch (z ++ compile-trace (drop (suc (fpc fs)) prog)) 0)
               (sigop-lowering si))
         (mfetch-zero (sigop-call (once-symbol-path (SigOpInfo.name si)))
                      (compile-trace (drop (suc (fpc fs)) prog))))))))

-- ARITH (Pure) SigOp: the emitted call is fetched, matched, and dispatched to
-- the arith block with NO event — mirroring `flat-events`' [] for a Pure SigOp.
sigop-run-arith : ∀ {hv : HeapView} ev env n prog fs s {A B} (si : SigOpInfo A B) (pl : Payload)
                → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
                → fetch prog (fpc fs) ≡ just (instr-sigop si)
                → env (once-symbol-path (SigOpInfo.name si)) ≡ just pl
                → RT.run-events ev env (suc n) (compile-trace prog) s
                    ≡ RT.run-events ev env n (compile-trace prog) (dispatchArith pl s)
sigop-run-arith ev env n prog fs s si pl cc h ftq env-eq =
  RT.run-events-arith ev env n (compile-trace prog) s
    (sigop-call (once-symbol-path (SigOpInfo.name si)))
    (once-symbol-path (SigOpInfo.name si)) pl
    (trans (CFC.halt-eq (dataCorr cc)) h)
    (sigop-concrete-fetch prog fs s si cc ftq)
    (sigop-matchCall (once-symbol-path (SigOpInfo.name si)))
    env-eq

-- EXTERNAL (Emits/Halts) SigOp: the same fetch and match, but the env has no
-- block for the symbol, so the loop EMITS `ev lbl s` and continues past the
-- call. This is the value-carrying observable emission.
sigop-run-external : ∀ {hv : HeapView} ev env n prog fs s {A B} (si : SigOpInfo A B)
                   → CompiledCorr hv prog fs s → halted (floc fs) ≡ false
                   → fetch prog (fpc fs) ≡ just (instr-sigop si)
                   → env (once-symbol-path (SigOpInfo.name si)) ≡ nothing
                   → RT.run-events ev env (suc n) (compile-trace prog) s
                       ≡ ev (once-symbol-path (SigOpInfo.name si)) s
                         ++ RT.run-events ev env n (compile-trace prog) (ret-past s)
sigop-run-external ev env n prog fs s si cc h ftq env-eq =
  RT.run-events-external ev env n (compile-trace prog) s
    (sigop-call (once-symbol-path (SigOpInfo.name si)))
    (once-symbol-path (SigOpInfo.name si))
    (trans (CFC.halt-eq (dataCorr cc)) h)
    (sigop-concrete-fetch prog fs s si cc ftq)
    (sigop-matchCall (once-symbol-path (SigOpInfo.name si)))
    env-eq

-- A Pure SigOp emits no event (the extractor's Pure branch is []).
event-of-pure : ∀ {A B} (si : SigOpInfo A B) fs → effect si ≡ Pure
              → event-of (instr-sigop si) fs ≡ []
event-of-pure si fs eqe rewrite eqe = refl

------------------------------------------------------------------------
-- THE STUCK ROUTES — the engine's SECOND per-arch supply (slice 3).
--
-- Slice 2's `BlockSteps` covers every branch where the abstract machine
-- STEPS. These are the branches where it does not: an empty heap cell, a jump
-- to a label that is not there. Neither is a `BlockStep` — nothing steps — and
-- neither can be folded into that record: what an arch owes here is a
-- run-events EQUATION, not a `BlockStep`.
--
-- WHY THEY ARE PER-ARCH AT ALL. "Both machines stop" is half generic and half
-- not. The ABSTRACT half — the flat machine halts, so `flat-events` is [] — is
-- the engine's, and `stuck-result` below discharges it once. The CONCRETE half
-- is the claim that the emitted block gets stuck or halts too, and stating it
-- means naming the instruction: `mov rax, [rdi]` faulting on an unmapped
-- address, a `jmp` to a missing label setting `halted`. That is the arch's.
--
-- The engine therefore asks for exactly the concrete half, and no ISA detail
-- crosses the boundary. It also absorbs what would otherwise have been engine
-- parameters: `execInstr-cmp-mi` is used only inside the tag-branch's stuck
-- route, so with this record `nonhalt-noncall` is the ONE ISA enumeration the
-- engine still needs.
------------------------------------------------------------------------

-- what an arch owes: the concrete machine emits nothing from here on.
StuckAt : RT.EvExtractor → RT.ArithEnv → List Instr → State → Set
StuckAt ev env cprog s = Σ ℕ (λ M → RT.run-events ev env M cprog s ≡ [])

record StuckSteps : Set₁ where
  field
    -- an indirect load through a pointer to an UNWRITTEN heap cell
    st-load-indirect :
      ∀ {hv : HeapView} ev env prog fs s hl → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just load-indirect
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
      → HDom hv hl
      → heapMem (floc fs) hl ≡ nothing
      → StuckAt ev env (compile-trace prog) s
    st-load-indirect-suc :
      ∀ {hv : HeapView} ev env prog fs s hl → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just load-indirect-suc
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr (AtDynamic hl)
      → HDom hv (sucHL hl)
      → heapMem (floc fs) (sucHL hl) ≡ nothing
      → StuckAt ev env (compile-trace prog) s
    -- …and the three control routes whose label is MISSING. Only the TAKEN
    -- ones are here: a not-taken branch never consults the label and is an
    -- ordinary block step (`bs-c-branch-nz`, `bs-c-branch-tag-nz`).
    st-c-jmp :
      ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-jmp m))
      → FlatMachine.find-label {FS} prog m ≡ nothing
      → StuckAt ev env (compile-trace prog) s
    st-c-branch-scratch-zero :
      ∀ {hv : HeapView} ev env prog fs s m → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-scratch-zero m))
      → readReg (regs (floc fs)) Scratch ≡ SV-Tag 0
      → FlatMachine.find-label {FS} prog m ≡ nothing
      → StuckAt ev env (compile-trace prog) s
    st-c-branch-tag-zero :
      ∀ {hv : HeapView} ev env prog fs s m loc → CompiledCorr hv prog fs s
      → halted (floc fs) ≡ false
      → fetch prog (fpc fs) ≡ just (instr-ctrl (c-branch-tag-zero m))
      → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
      → readLoc (floc fs) loc ≡ just (SV-Tag 0)
      → memory s (rreg s in1-reg + 0) ≡ just 0
      → FlatMachine.find-label {FS} prog m ≡ nothing
      → StuckAt ev env (compile-trace prog) s
open StuckSteps public

-- THE GENERIC HALF, discharged once: if the flat machine has halted at the
-- post-state and the instruction emits no event, then the arch's "nothing more
-- comes out of the concrete machine" IS the correspondence at this branch.
stuck-result : ∀ ev env n prog fs s (i : AbstractInstr)
             → halted (floc (flat-exec-instr i prog fs)) ≡ true
             → event-of i fs ≡ []
             → StuckAt ev env (compile-trace prog) s
             → Σ ℕ (λ M → RT.run-events ev env M (compile-trace prog) s
                   ≡ event-of i fs ++ flat-events n prog (flat-exec-instr i prog fs))
stuck-result ev env n prog fs s i hpost ev-eq (M , eq) =
  M , trans eq (sym (trans (cong (_++ flat-events n prog (flat-exec-instr i prog fs)) ev-eq)
                           (flat-events-halted n prog (flat-exec-instr i prog fs) hpost)))
