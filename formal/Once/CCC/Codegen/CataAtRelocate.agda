-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.CataAtRelocate — per-instruction RELOCATION for the
-- flat machine (Plan 0.36 task #8, the at-algebra correspondence).
--
-- The algebra trace `at = ir-to-trace alg` is embedded at an offset `k`
-- inside the cata program, but `alg`'s correctness (`IRObsCorrectF`) is
-- stated for `at` run STANDALONE from pc 0. Relocation bridges them:
-- running an instruction in the big program `prog` from a pc shifted by
-- `k` equals running it standalone in `seg` and shifting the result pc.
--
-- The invariant is `shift-pc k` — and the KEY design choice is that it
-- shifts on the RIGHT (`fpc fs + k`). Then every case is `refl` or
-- definitional, with NO arithmetic lemmas: a straight step gives
-- `suc (fpc fs) + k = suc (fpc fs + k)` definitionally, and a jump lands
-- at `q + k` matching `find-label-distrib`'s `p + length pre` form.
-- Branches reduce to the jump case (`do-branch true = do-jump`).
--
-- Jumps/branches carry the per-target relocation as a hypothesis
-- `find-label prog n ≡ map (_+ k) (find-label seg n)` (discharged at the
-- concrete-program assembly via `find-label-distrib`); straight steps via
-- the `StraightStep` classifier (so the ~16 non-ctrl constructors need no
-- enumeration).
------------------------------------------------------------------------

module Once.CCC.Codegen.CataAtRelocate where

open import Once.CCC.Label using (LabelId)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; map; just; nothing)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Denotation.Trace using (SigOpEvent)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open import Once.CCC.Machine.SMCore
  using (halted; regs; readReg; Scratch; AbstractInstr; AbstractTrace;
         instr-ctrl; c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero;
         c-thunk; c-ret;
         -- the non-ctrl constructors (each relocates by `refl` via the
         -- `flat-step-straight` catch-all) — enumerated for `instr-reloc`.
         mov-to-output; mov-to-input; load-indirect; load-indirect-suc; load-from-slot; store-at-slot;
         store-indirect; store-indirect-suc; lea-slot; restore-input;
         instr-alloc-stack; instr-dealloc-stack; instr-reclaim-to; instr-push-frame;
         instr-pop-frame; instr-call-closure; worklist-init; worklist-push;
         worklist-pop; worklist-check; instr-sigop; instr-load-const;
         instr-load-code-addr; instr-save-closure-reg; instr-load-tag-lit;
         instr-case-on-tag; instr-alloc-heap; instr-loop; instr-reg-op; lea-indexed;
         -- D092: the call reads the closure register and the heap cell it
         -- points at, so its relocation lemma has to case on both.
         StoredValue; SV-Tag; SV-Lit; SV-Code; SV-Ptr; AtDynamic; AtStack; heapMem)
open import Once.Memory.HeapAddress using (sucHL)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module CataAtRelocate {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open FlatEventTrace {FS}

  -- Plan 0.63: a PENDING RETURN ADDRESS IS A CODE ADDRESS, so it relocates
  -- exactly like the pc. Written as an explicit recursion (not `map`) so it
  -- reduces on the cons pattern and `flat-relocate-ret` stays `refl`.
  shift-rets : ℕ → List ℕ → List ℕ
  shift-rets k []       = []
  shift-rets k (p ∷ ps) = (p + k) ∷ shift-rets k ps

  -- The relocation invariant: same state, pc — and every pending return
  -- address — shifted RIGHT by `k`.
  shift-pc : ℕ → FlatState → FlatState
  shift-pc k fs = record fs { fpc = fpc fs + k ; fret = shift-rets k (fret fs) }

  -- Straight step relocates: it ignores `prog` (no `find-label`) and only
  -- bumps the pc, so running in `prog` from the shifted pc = shifting the
  -- standalone result. Via the `StraightStep` classifier — covers every
  -- non-ctrl instruction without enumerating constructors. After rewriting
  -- both sides to `flat-step-straight`, the pcs agree definitionally
  -- (`suc (fpc fs) + k = suc (fpc fs + k)`) and `floc`/`falloc` are
  -- computed from `floc fs`/`falloc fs` (preserved by `shift-pc`).
  flat-relocate-straight : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState)
                             (i : AbstractInstr)
                         → StraightStep i
                         → flat-exec-instr i prog (shift-pc k fs)
                             ≡ shift-pc k (flat-exec-instr i seg fs)
  flat-relocate-straight prog seg k fs i ss
    rewrite ss prog (shift-pc k fs) | ss seg fs = refl

  -- Label relocates trivially (pc bump, `prog`-independent).
  flat-relocate-label : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : LabelId)
    → flat-exec-instr (instr-ctrl (c-label n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-label n)) seg fs)
  flat-relocate-label prog seg k fs n = refl

  -- Plan 0.63: a body-entry marker relocates like a label — it reserves the
  -- body's frame and bumps the pc, neither of which consults `prog` — and a
  -- RETURN relocates because `shift-pc` shifts the pending return addresses
  -- too (D083): popping the shifted stack lands at `p + k`, exactly where
  -- shifting the standalone result lands. The frame move is `prog`-blind on
  -- both sides.
  flat-relocate-thunk : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : LabelId) (b : ℕ)
    → flat-exec-instr (instr-ctrl (c-thunk n b)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-thunk n b)) seg fs)
  flat-relocate-thunk prog seg k fs n b = refl

  flat-relocate-ret : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (b : ℕ)
    → flat-exec-instr (instr-ctrl (c-ret b)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-ret b)) seg fs)
  flat-relocate-ret prog seg k fs b with fret fs
  ... | []     = refl
  ... | p ∷ ps = refl

  -- Jump relocates given the target's relocation fact: `find-label prog n
  -- = (find-label seg n) + k`. `just q → q + k` matches `shift-pc`'s
  -- right-add (refl); `nothing → halt` on both sides (refl).
  flat-relocate-jmp : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : LabelId)
    → find-label prog n ≡ map (_+ k) (find-label seg n)
    → flat-exec-instr (instr-ctrl (c-jmp n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-jmp n)) seg fs)
  flat-relocate-jmp prog seg k fs n lr rewrite lr with find-label seg n
  ... | just q  = refl
  ... | nothing = refl

  -- Branches reduce to the jump case: `do-branch true = do-jump =
  -- flat-exec-instr (c-jmp …)`; the not-taken case is a straight pc bump.
  -- The condition reads `floc (shift-pc k fs) = floc fs`, so it matches the
  -- standalone condition.
  flat-relocate-branch-scratch : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : LabelId)
    → find-label prog n ≡ map (_+ k) (find-label seg n)
    → flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) seg fs)
  flat-relocate-branch-scratch prog seg k fs n lr
    with sv-is-zero (readReg (regs (floc fs)) Scratch)
  ... | true  = flat-relocate-jmp prog seg k fs n lr
  ... | false = refl

  flat-relocate-branch-tag : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (n : LabelId)
    → find-label prog n ≡ map (_+ k) (find-label seg n)
    → flat-exec-instr (instr-ctrl (c-branch-tag-zero n)) prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr (instr-ctrl (c-branch-tag-zero n)) seg fs)
  flat-relocate-branch-tag prog seg k fs n lr
    with tag-zf (flat-read-tag (floc fs))
  ... | true  = flat-relocate-jmp prog seg k fs n lr
  ... | false = refl

  -- THE CALL RELOCATES TOO (D092) — and it is the reason this module now
  -- needs a SECOND embedding fact. Until the call was modelled it was a no-op,
  -- program-independent, and relocated by `refl` with the rest. It now RESOLVES
  -- A LABEL, through the call scan rather than the jump scan (D082), so it
  -- relocates exactly when `find-thunk` does — the mirror of `lr` for `ft-go`.
  --
  -- The `fret` push lines up with no arithmetic: the pushed pc is
  -- `suc (fpc fs) + k` on the relocated side and `shift-rets k` applied to
  -- `suc (fpc fs)` on the other, and `suc n + k` IS `suc (n + k)`.
  reloc-call-at : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (mj : Maybe ℕ)
                → do-call-at (map (_+ k) mj) (shift-pc k fs) ≡ shift-pc k (do-call-at mj fs)
  reloc-call-at prog seg k fs (just q) = refl
  reloc-call-at prog seg k fs nothing  = refl

  reloc-call-code : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState)
                      (mv : Maybe (StoredValue FS))
                  → (∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk seg n))
                  → do-call-code prog mv (shift-pc k fs) ≡ shift-pc k (do-call-code seg mv fs)
  reloc-call-code prog seg k fs (just (SV-Code ℓ)) tr
    rewrite tr ℓ = reloc-call-at prog seg k fs (find-thunk seg ℓ)
  reloc-call-code prog seg k fs (just (SV-Tag _))   tr = refl
  reloc-call-code prog seg k fs (just (SV-Lit _ _)) tr = refl
  reloc-call-code prog seg k fs (just (SV-Ptr _))   tr = refl
  reloc-call-code prog seg k fs nothing             tr = refl

  reloc-call-sv : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (v : StoredValue FS)
                → (∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk seg n))
                → do-call-sv prog v (shift-pc k fs) ≡ shift-pc k (do-call-sv seg v fs)
  reloc-call-sv prog seg k fs (SV-Ptr (AtDynamic hl)) tr =
    reloc-call-code prog seg k fs (heapMem (floc fs) (sucHL hl)) tr
  reloc-call-sv prog seg k fs (SV-Ptr (AtStack _ _)) tr = refl
  reloc-call-sv prog seg k fs (SV-Tag _)             tr = refl
  reloc-call-sv prog seg k fs (SV-Lit _ _)           tr = refl
  reloc-call-sv prog seg k fs (SV-Code _)            tr = refl

  flat-relocate-call : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState)
    → (∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk seg n))
    → flat-exec-instr instr-call-closure prog (shift-pc k fs)
        ≡ shift-pc k (flat-exec-instr instr-call-closure seg fs)
  flat-relocate-call prog seg k fs tr = reloc-call-sv prog seg k fs (fclosure fs) tr

  -- Relocation for an ARBITRARY instruction: dispatch the 4 control forms
  -- to the per-class lemmas (carrying the target's relocation fact `lr n`),
  -- and every non-ctrl instruction to `refl` (`flat-exec-instr` falls
  -- through to `flat-step-straight`, which `shift-pc` commutes with
  -- definitionally — same enumeration style as `straight-trace'` and the
  -- X86 `FlatComposition`). `lr` is the GLOBAL label-relocation fact
  -- (every label of `seg` resolves offset by `k` in `prog`), discharged at
  -- the concrete-program assembly via `find-label-distrib`.
  instr-reloc : ∀ (prog seg : AbstractTrace) (k : ℕ) (fs : FlatState) (i : AbstractInstr)
              → (∀ n → find-label prog n ≡ map (_+ k) (find-label seg n))
              → (∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk seg n))
              → flat-exec-instr i prog (shift-pc k fs) ≡ shift-pc k (flat-exec-instr i seg fs)
  -- control forms → the per-class relocation lemmas
  instr-reloc prog seg k fs (instr-ctrl (c-label n))               lr tr = flat-relocate-label          prog seg k fs n
  instr-reloc prog seg k fs (instr-ctrl (c-thunk n b))             lr tr = flat-relocate-thunk          prog seg k fs n b
  instr-reloc prog seg k fs (instr-ctrl (c-ret b))                 lr tr = flat-relocate-ret            prog seg k fs b
  instr-reloc prog seg k fs (instr-ctrl (c-jmp n))                 lr tr = flat-relocate-jmp            prog seg k fs n (lr n)
  instr-reloc prog seg k fs (instr-ctrl (c-branch-scratch-zero n)) lr tr = flat-relocate-branch-scratch prog seg k fs n (lr n)
  instr-reloc prog seg k fs (instr-ctrl (c-branch-tag-zero n))     lr tr = flat-relocate-branch-tag     prog seg k fs n (lr n)
  -- every non-ctrl instruction relocates by `refl`
  instr-reloc prog seg k fs mov-to-output           lr tr = refl
  instr-reloc prog seg k fs mov-to-input            lr tr = refl
  instr-reloc prog seg k fs load-indirect           lr tr = refl
  instr-reloc prog seg k fs load-indirect-suc       lr tr = refl
  instr-reloc prog seg k fs (load-from-slot _)      lr tr = refl
  instr-reloc prog seg k fs (store-at-slot _)       lr tr = refl
  instr-reloc prog seg k fs store-indirect          lr tr = refl
  instr-reloc prog seg k fs store-indirect-suc      lr tr = refl
  instr-reloc prog seg k fs (lea-slot _)            lr tr = refl
  instr-reloc prog seg k fs (restore-input _)       lr tr = refl
  instr-reloc prog seg k fs (instr-alloc-stack _)   lr tr = refl
  instr-reloc prog seg k fs (instr-dealloc-stack _) lr tr = refl
  instr-reloc prog seg k fs (instr-reclaim-to _)    lr tr = refl
  instr-reloc prog seg k fs (instr-push-frame _)    lr tr = refl
  instr-reloc prog seg k fs instr-pop-frame         lr tr = refl
  instr-reloc prog seg k fs instr-call-closure      lr tr = flat-relocate-call prog seg k fs tr
  instr-reloc prog seg k fs (worklist-init _)       lr tr = refl
  instr-reloc prog seg k fs (worklist-push _)       lr tr = refl
  instr-reloc prog seg k fs (worklist-pop _)        lr tr = refl
  instr-reloc prog seg k fs (worklist-check _)      lr tr = refl
  instr-reloc prog seg k fs (instr-sigop _)         lr tr = refl
  instr-reloc prog seg k fs (instr-load-const _ _)  lr tr = refl
  instr-reloc prog seg k fs (instr-load-code-addr _) lr tr = refl
  instr-reloc prog seg k fs instr-save-closure-reg  lr tr = refl
  instr-reloc prog seg k fs (instr-load-tag-lit _)  lr tr = refl
  instr-reloc prog seg k fs (instr-case-on-tag _ _) lr tr = refl
  instr-reloc prog seg k fs (instr-alloc-heap _)    lr tr = refl
  instr-reloc prog seg k fs (instr-loop _)          lr tr = refl
  instr-reloc prog seg k fs (instr-reg-op _)        lr tr = refl
  instr-reloc prog seg k fs (lea-indexed _)         lr tr = refl

  -- RELOCATE A WHOLE STEP-CHAIN: a standalone run of `seg` (a `FlatSteps`
  -- chain from `fs₀` to `fs₁`) lifts to a run of the big program `prog`
  -- from the offset-shifted states, given the two embedding facts —
  -- labels relocate (`lr`, for jumps/branches) and fetch relocates
  -- (`fe`, every fetched instruction sits `k` higher in `prog`). Each link
  -- relocates by `instr-reloc`; the `subst` realigns the chain tail's start
  -- state (`flat-exec-instr i prog (shift-pc k fs₀)` ≡ the shifted
  -- standalone next state). `halted` transfers (shift-pc preserves `floc`),
  -- `fetch` via `fe` (`fpc (shift-pc k fs₀) = fpc fs₀ + k`).
  relocate-steps : ∀ {N : ℕ} {fs₀ fs₁ : FlatState} (prog seg : AbstractTrace) (k : ℕ)
                 → (∀ n → find-label prog n ≡ map (_+ k) (find-label seg n))
                 → (∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk seg n))
                 → (∀ pc i → fetch seg pc ≡ just i → fetch prog (pc + k) ≡ just i)
                 → FlatSteps seg N fs₀ fs₁
                 → FlatSteps prog N (shift-pc k fs₀) (shift-pc k fs₁)
  relocate-steps prog seg k lr tr fe []                                = []
  relocate-steps prog seg k lr tr fe (_∷_ {fs = fs₀} {i = i} (h , f) rest) =
    (h , fe (fpc fs₀) i f)
      ∷ subst (λ s → FlatSteps prog _ s (shift-pc k _))
              (sym (instr-reloc prog seg k fs₀ i lr tr))
              (relocate-steps prog seg k lr tr fe rest)

  -- The relocated chain emits exactly the same SigOp events as the
  -- standalone one: `event-of` reads the instruction + `Input1` (off
  -- `floc`), and `shift-pc` preserves `floc`, so each link's events are
  -- definitionally unchanged; the tail's start-state `subst` is invisible
  -- to `chain-events` (`chain-events-subst-start`). This is the
  -- trace-side of relocation — what carries `at`'s `traces-agree` from
  -- standalone into the embedded cata run.
  chain-events-relocate : ∀ {N : ℕ} {fs₀ fs₁ : FlatState} (prog seg : AbstractTrace) (k : ℕ)
                            (lr : ∀ n → find-label prog n ≡ map (_+ k) (find-label seg n))
                            (tr : ∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk seg n))
                            (fe : ∀ pc i → fetch seg pc ≡ just i → fetch prog (pc + k) ≡ just i)
                            (steps : FlatSteps seg N fs₀ fs₁)
                        → chain-events (relocate-steps prog seg k lr tr fe steps) ≡ chain-events steps
  chain-events-relocate prog seg k lr tr fe []                                = refl
  chain-events-relocate prog seg k lr tr fe (_∷_ {fs = fs₀} {i = i} (h , f) rest) =
    cong (event-of i (shift-pc k fs₀) ++_)
         (trans (chain-events-subst-start (sym (instr-reloc prog seg k fs₀ i lr tr))
                                          (relocate-steps prog seg k lr tr fe rest))
                (chain-events-relocate prog seg k lr tr fe rest))

  -- CAPSTONE (trace side of the at-algebra correspondence): the relocated
  -- `at`-chain emits exactly `alg`'s source events `E`. Combines the whole
  -- bridge — `alg`'s standalone halting run reifies to a chain
  -- (`reify-run`), whose events are `alg`'s trace (`flat-events-reify` +
  -- `alg`'s `traces-agree`, here `at-traces`), preserved under embedding
  -- (`chain-events-relocate`). The embedding facts `lr`/`fe` (labels +
  -- fetch relocate by `k`) are discharged at the concrete cata-program
  -- assembly (`find-label-distrib` + `fetch-++`). So splicing `at` into the
  -- cata loop contributes precisely `alg`'s events to `traces-agree`.
  at-relocated-emits : ∀ (prog at : AbstractTrace) (k F : ℕ) (init : FlatState)
                         (E : List SigOpEvent)
                         (at-halts : halted (floc (exec-flat F at init)) ≡ true)
                         (lr : ∀ n → find-label prog n ≡ map (_+ k) (find-label at n))
                         (tr : ∀ n → find-thunk prog n ≡ map (_+ k) (find-thunk at n))
                         (fe : ∀ pc i → fetch at pc ≡ just i → fetch prog (pc + k) ≡ just i)
                     → flat-events F at init ≡ E
                     → chain-events (relocate-steps prog at k lr tr fe
                                       (RunReified.chain (reify-run F at init at-halts)))
                         ≡ E
  at-relocated-emits prog at k F init E at-halts lr tr fe at-traces =
    trans (chain-events-relocate prog at k lr tr fe (RunReified.chain (reify-run F at init at-halts)))
          (trans (sym (flat-events-reify F at init (reify-run F at init at-halts))) at-traces)
