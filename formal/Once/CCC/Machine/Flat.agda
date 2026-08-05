-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.Flat
--
-- Plan 0.32 M3 Phase B: the FLAT abstract machine — a pc/fuel executor
-- over the UNIFIED `AbstractInstr` (Phase A added `instr-ctrl`), mirroring
-- the target `Semantics.exec`. Straight-line instructions reuse the
-- existing `exec-abstract` effect (no duplication); `instr-ctrl` is the
-- flat control (label/jump/test on a pc + zero-flag).
--
-- This is the machine the real correctness chain runs over: abstract↔
-- target becomes a 1-to-1 instruction relabel (Phase A's
-- `compile-abstract (instr-ctrl c)`) + the value encoding.
--
-- DESIGN RULE (Plan 0.32): `exec` is `with`-FREE — every decision (halted,
-- fetch, find-label, zf, indirect read) routes through a top-level helper
-- taking the decision value explicitly, so correspondence proofs reduce
-- under hypotheses.
------------------------------------------------------------------------

module Once.CCC.Machine.Flat where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _+_)
-- Plan 0.63 (D089): the scans key on the STRUCTURED identity.
open import Once.CCC.Label using (LabelId; _≡ᵇᴵ_; ≡ᵇᴵ-true)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore

module FlatMachine {FS : FrameSemantics} where
  open MemOps {FS}
  open FrameSemantics FS using (Frame; shift-frame)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
  open AbstractExec {FS} using (exec-abstract; exec-trace; exec-trace-cons)

  -- Flat machine state: the typed LocState + allocator + pc.
  -- Plan 0.34: no zero-flag — a conditional branch is one unit that
  -- computes its condition inline, so there is no persisting flag.
  record FlatState : Set where
    constructor mkFlatFull
    field
      floc   : LocState FS
      falloc : AllocState {FS}
      fpc    : ℕ
      -- Plan 0.63: the call/return state.
      -- `fret` is the return-pc stack — a GHOST list, because the abstract
      -- memory is frame/slot-keyed and has no byte-addressed pushdown; the
      -- addresses the concrete machine pushes below %rsp are modelled here
      -- and related by the correspondence.
      -- `fclosure` mirrors the per-arch closure register (%r12), which the
      -- concrete call dereferences (`call *0x8(%r12)`); `exec-abstract`
      -- treats `instr-save-closure-reg` as the identity precisely because
      -- that register lives at the FLAT level.
      fret     : List ℕ
      fclosure : StoredValue FS
  open FlatState public

  -- The 3-field constructor every existing site uses: no pending returns,
  -- filler closure register (D074's tag filler). Keeping it means the two
  -- new fields cost no edit at the ~37 construction sites, all of which
  -- build exactly such a state.
  mkFlat : LocState FS → AllocState {FS} → ℕ → FlatState
  mkFlat loc alloc pc = mkFlatFull loc alloc pc [] (SV-Tag 0)

  ----------------------------------------------------------------------
  -- `with`-free decision helpers
  ----------------------------------------------------------------------
  sv-is-zero : StoredValue FS → Bool
  sv-is-zero (SV-Tag 0) = true
  sv-is-zero _          = false

  tag-zf : Maybe (StoredValue FS) → Bool
  tag-zf (just v) = sv-is-zero v
  tag-zf nothing  = false

  -- read the tag at *Input1, with-free (route the sv-as-loc result).
  flat-read-at : LocState FS → Maybe (ValueLocation FS) → Maybe (StoredValue FS)
  flat-read-at s (just loc) = readLoc s loc
  flat-read-at s nothing    = nothing

  flat-read-tag : LocState FS → Maybe (StoredValue FS)
  flat-read-tag s = flat-read-at s (sv-as-loc (readReg (regs s) Input1))

  -- find-label: scan the trace for `instr-ctrl (c-label target)`.
  -- Uses the library `_≡ᵇ_` (= the target `Semantics.find-label`'s
  -- comparison) so label resolution is 1-to-1 with x86-64.
  -- Plan 0.36: dispatch label detection through `label-of?` (a `Maybe`,
  -- not a `c-label` pattern in `fl-go`) so proofs that scan PAST an
  -- abstract trace segment (e.g. the cata algebra's trace `at` in the
  -- ascend phase) case on `label-of? x`'s 2-valued result, not
  -- `AbstractInstr`'s ~30 constructors. Behavior-preserving: `label-of?`
  -- is `just m` exactly on `instr-ctrl (c-label m)`, `nothing` elsewhere.
  label-of? : AbstractInstr → Maybe LabelId
  label-of? (instr-ctrl (c-label m)) = just m
  label-of? _                        = nothing

  fl-go          : AbstractTrace → LabelId → ℕ → Maybe ℕ
  fl-label-match : Bool → AbstractTrace → LabelId → ℕ → Maybe ℕ
  fl-go []       _      _ = nothing
  fl-go (x ∷ is) target i with label-of? x
  ... | just m  = fl-label-match (m ≡ᵇᴵ target) is target i
  ... | nothing = fl-go is target (suc i)
  fl-label-match true  _  _      i = just i
  fl-label-match false is target i = fl-go is target (suc i)

  find-label : AbstractTrace → LabelId → Maybe ℕ
  find-label prog target = fl-go prog target 0

  -- D082: the CALL's scan. Separate from `find-label` because a body entry
  -- (`c-thunk`) and a jump target (`c-label`) are different provenances —
  -- a call can never land on a jump label, definitionally.
  thunk-of? : AbstractInstr → Maybe LabelId
  thunk-of? (instr-ctrl (c-thunk m _)) = just m
  thunk-of? _                        = nothing

  ft-go    : AbstractTrace → LabelId → ℕ → Maybe ℕ
  ft-match : Bool → AbstractTrace → LabelId → ℕ → Maybe ℕ
  ft-go []       _      _ = nothing
  ft-go (x ∷ is) target i with thunk-of? x
  ... | just m  = ft-match (m ≡ᵇᴵ target) is target i
  ... | nothing = ft-go is target (suc i)
  ft-match true  _  _      i = just i
  ft-match false is target i = ft-go is target (suc i)

  find-thunk : AbstractTrace → LabelId → Maybe ℕ
  find-thunk prog target = ft-go prog target 0

  fetch : AbstractTrace → ℕ → Maybe AbstractInstr
  fetch []       _       = nothing
  fetch (i ∷ _)  zero    = just i
  fetch (_ ∷ is) (suc n) = fetch is n

  ----------------------------------------------------------------------
  -- Per-instruction effect. `with`-free; control routes through the
  -- explicit find-label / zf decision; straight-line REUSES exec-abstract.
  ----------------------------------------------------------------------
  do-jump : Maybe ℕ → FlatState → FlatState
  do-jump (just pc') fs = record fs { fpc = pc' }
  do-jump nothing    fs = record fs { floc = record (floc fs) { halted = true } }

  -- Conditional branch (Plan 0.34): if the (inline-computed) condition
  -- holds, jump to the target label; else fall through. No flag state.
  do-branch : Bool → LabelId → AbstractTrace → FlatState → FlatState
  do-branch true  target prog fs = do-jump (find-label prog target) fs
  do-branch false _      _    fs = record fs { fpc = suc (fpc fs) }

  -- straight-line: thread the LocState/AllocState through exec-abstract,
  -- advance pc. (Lambda-free read positions: applied to floc fs directly.)
  flat-step-straight : AbstractInstr → FlatState → FlatState
  flat-step-straight i fs =
    record fs { floc   = proj₁ (exec-abstract i (floc fs) (falloc fs))
              ; falloc = proj₂ (exec-abstract i (floc fs) (falloc fs))
              ; fpc    = suc (fpc fs) }

  ----------------------------------------------------------------------
  -- Plan 0.61: FRAMES MOVE WITH THE STACK POINTER.
  --
  -- The flat machine is the semantics of record, so — exactly like control
  -- flow — the frame discipline lives HERE rather than in the structured
  -- `exec-abstract` (which the legacy IR-WF layer still reads with the old,
  -- degenerate "frame never moves" model). Every %rsp-moving instruction
  -- shifts `current-frame` in the growth direction and remembers the caller's
  -- frame; the matching epilogue restores it. This is what makes a callee's
  -- slot `k` a DIFFERENT cell from its caller's slot `k` — without it no stack
  -- address has a meaning, because the abstract state would identify two cells
  -- the hardware keeps apart.
  ----------------------------------------------------------------------
  enter-frame : ℕ → AllocState {FS} → AllocState {FS}
  enter-frame n alloc =
    record alloc { current-frame = shift-frame (current-frame alloc) n
                 -- Plan 0.63: the callee's reserved slot count travels WITH the
                 -- frame, and the caller's is remembered beside its frame. This
                 -- is the whole of the old `Registers.frame-slots` mirror: one
                 -- mechanism, so a call updates the coverage bound and the
                 -- frame in a single step.
                 ; frame-slots   = n
                 ; saved-frames  = (current-frame alloc , frame-slots alloc)
                                     ∷ saved-frames alloc }

  -- Pop the frame stack (identity when empty — a malformed epilogue; the
  -- well-formedness premises pair every prologue with its epilogue).
  -- Aux-style on the frame stack so downstream proofs can reduce it.
  leave-frame-aux : List (Frame × ℕ) → AllocState {FS} → AllocState {FS}
  leave-frame-aux []             alloc = alloc
  leave-frame-aux ((f , b) ∷ fs) alloc =
    record alloc { current-frame = f ; frame-slots = b ; saved-frames = fs }

  leave-frame : AllocState {FS} → AllocState {FS}
  leave-frame alloc = leave-frame-aux (saved-frames alloc) alloc

  -- Plan 0.63: READ-BACK for the epilogue, per shape of the frame stack. These
  -- exist because `rewrite` on `saved-frames alloc ≡ …` does not reach the
  -- occurrence buried in `leave-frame`'s unfolding at a use site — the
  -- equation has to be consumed where `leave-frame-aux` is still exposed.
  leave-frame-slots-[] : ∀ (alloc : AllocState {FS}) → saved-frames alloc ≡ []
                       → frame-slots (leave-frame alloc) ≡ frame-slots alloc
  leave-frame-slots-[] alloc e rewrite e = refl

  leave-frame-slots-∷ : ∀ (alloc : AllocState {FS}) (f : Frame) (b : ℕ) (frs : List (Frame × ℕ))
                      → saved-frames alloc ≡ (f , b) ∷ frs
                      → frame-slots (leave-frame alloc) ≡ b
  leave-frame-slots-∷ alloc f b frs e rewrite e = refl

  leave-frame-saved-[] : ∀ (alloc : AllocState {FS}) → saved-frames alloc ≡ []
                       → saved-frames (leave-frame alloc) ≡ []
  leave-frame-saved-[] alloc e = go (saved-frames alloc) refl
    where go : ∀ (fl : List (Frame × ℕ)) → saved-frames alloc ≡ fl
             → saved-frames (leave-frame-aux fl alloc) ≡ []
          go []             _  = e
          go ((f , b) ∷ fs) eq = absurd (trans (sym e) eq)
            where absurd : ∀ {A : Set} → [] ≡ (f , b) ∷ fs → A
                  absurd ()

  leave-frame-saved-∷ : ∀ (alloc : AllocState {FS}) (f : Frame) (b : ℕ) (frs : List (Frame × ℕ))
                      → saved-frames alloc ≡ (f , b) ∷ frs
                      → saved-frames (leave-frame alloc) ≡ frs
  leave-frame-saved-∷ alloc f b frs e rewrite e = refl

  -- The frame move touches ONLY the frame fields.
  leave-frame-next-slot : ∀ (alloc : AllocState {FS})
                        → next-slot (leave-frame alloc) ≡ next-slot alloc
  leave-frame-next-slot alloc = go (saved-frames alloc)
    where go : ∀ (fl : List (Frame × ℕ)) → next-slot (leave-frame-aux fl alloc) ≡ next-slot alloc
          go []             = refl
          go ((f , b) ∷ fs) = refl

  leave-frame-heap-ref : ∀ (alloc : AllocState {FS})
                       → next-heap-ref (leave-frame alloc) ≡ next-heap-ref alloc
  leave-frame-heap-ref alloc = go (saved-frames alloc)
    where go : ∀ (fl : List (Frame × ℕ)) → next-heap-ref (leave-frame-aux fl alloc) ≡ next-heap-ref alloc
          go []             = refl
          go ((f , b) ∷ fs) = refl

  -- …and the BLOCK SIZES survive a frame move too (the heap is shared across
  -- frames): the sibling of `leave-frame-heap-ref`, needed by the correspondence's
  -- in-bounds coverage field (`dom-sized`).
  leave-frame-block-size : ∀ (alloc : AllocState {FS})
                         → block-size (leave-frame alloc) ≡ block-size alloc
  leave-frame-block-size alloc = go (saved-frames alloc)
    where go : ∀ (fl : List (Frame × ℕ)) → block-size (leave-frame-aux fl alloc) ≡ block-size alloc
          go []             = refl
          go ((f , b) ∷ fs) = refl

  -- straight-line step whose AllocState is post-processed by the frame move.
  flat-step-frame : AbstractInstr → (AllocState {FS} → AllocState {FS})
                  → FlatState → FlatState
  flat-step-frame i g fs =
    record fs { floc   = proj₁ (exec-abstract i (floc fs) (falloc fs))
              ; falloc = g (proj₂ (exec-abstract i (floc fs) (falloc fs)))
              ; fpc    = suc (fpc fs) }

  -- Plan 0.63: RETURN. Release the body's frame, then pop the return-pc
  -- stack and continue there; an empty stack halts (returning from the
  -- outermost frame). Aux-style on the list so downstream proofs rewrite
  -- with the pop equation. `leave-frame` is applied FIRST and
  -- unconditionally, mirroring the concrete `addq $b*8,%rsp ; ret`: the
  -- reservation is released whether or not there is a caller to return to.
  do-ret : List ℕ → FlatState → FlatState
  do-ret []           fs = record fs { falloc = leave-frame (falloc fs)
                                     ; floc   = record (floc fs) { halted = true } }
  do-ret (pc' ∷ rest) fs = record fs { falloc = leave-frame (falloc fs)
                                     ; fpc = pc' ; fret = rest }

  -- THE BODY'S RESERVATION GROWS THE FRAME THE CALL ALREADY ENTERED
  -- (Plan 0.63, D086) — it does NOT push one.
  --
  -- The concrete `call` decrements %rsp by one slot and stores the return
  -- address there (`execInstr … (call …)`: `newSp = sp ∸ slot-size`); only
  -- THEN does the body's `sub rsp, 8b` run. So a body's frame sits `b + 1`
  -- slots below its caller's, not `b`, and step 2a's `enter-frame b` was off
  -- by exactly the return-address slot — which is not a slot the abstract
  -- machine can address at all: it holds a code address, and those live in
  -- the ghost `fret`.
  --
  -- Hence the split. The CALL enters the frame (shifting by the one slot its
  -- own %rsp arithmetic consumes, reserving nothing) and pushes the return pc;
  -- this marker only DEEPENS that frame. One push per call is also what keeps
  -- `saved-frames` and `fret` the same length, which is the invariant a return
  -- needs (`ConcFlatSim.RetMatch`) — the alternative, pushing the frame here,
  -- makes the two stacks differ in length between a call and its body.
  --
  -- The return-address cell then lies in the gap between the callee's window
  -- END and the caller's BASE, inside no window at all. That gap is exactly
  -- the slack D085's floor leaves (it is a `≤`, not an equality).
  -- …and the same read-backs for the RETURN itself. `do-ret` matches on the
  -- return stack, so a use site has to consume the shape equation here rather
  -- than rewrite through it.
  do-ret-pc-[] : ∀ (fs : FlatState) → fret fs ≡ []
               → fpc (do-ret (fret fs) fs) ≡ fpc fs
  do-ret-pc-[] fs e = go (fret fs) refl
    where go : ∀ (rl : List ℕ) → fret fs ≡ rl → fpc (do-ret rl fs) ≡ fpc fs
          go []       _  = refl
          go (x ∷ xs) eq = absurd (trans (sym e) eq)
            where absurd : ∀ {A : Set} → [] ≡ x ∷ xs → A
                  absurd ()

  do-ret-pc-∷ : ∀ (fs : FlatState) (rpc : ℕ) (rs : List ℕ) → fret fs ≡ rpc ∷ rs
              → fpc (do-ret (fret fs) fs) ≡ rpc
  do-ret-pc-∷ fs rpc rs e rewrite e = refl

  do-ret-fret-[] : ∀ (fs : FlatState) → fret fs ≡ []
                 → fret (do-ret (fret fs) fs) ≡ []
  do-ret-fret-[] fs e = go (fret fs) refl
    where go : ∀ (rl : List ℕ) → fret fs ≡ rl → fret (do-ret rl fs) ≡ []
          go []       _  = e
          go (x ∷ xs) eq = absurd (trans (sym e) eq)
            where absurd : ∀ {A : Set} → [] ≡ x ∷ xs → A
                  absurd ()

  do-ret-fret-∷ : ∀ (fs : FlatState) (rpc : ℕ) (rs : List ℕ) → fret fs ≡ rpc ∷ rs
                → fret (do-ret (fret fs) fs) ≡ rs
  do-ret-fret-∷ fs rpc rs e rewrite e = refl

  do-ret-alloc : ∀ (fs : FlatState) → falloc (do-ret (fret fs) fs) ≡ leave-frame (falloc fs)
  do-ret-alloc fs = go (fret fs)
    where go : ∀ (rl : List ℕ) → falloc (do-ret rl fs) ≡ leave-frame (falloc fs)
          go []       = refl
          go (x ∷ xs) = refl

  grow-frame : ℕ → AllocState {FS} → AllocState {FS}
  grow-frame n alloc =
    record alloc { current-frame = shift-frame (current-frame alloc) n
                 ; frame-slots   = n }

  do-thunk : ℕ → FlatState → FlatState
  do-thunk b fs = record fs { falloc = grow-frame b (falloc fs)
                            ; fpc    = suc (fpc fs) }

  flat-exec-instr : AbstractInstr → AbstractTrace → FlatState → FlatState
  flat-exec-instr (instr-ctrl (c-label _))               _    fs = record fs { fpc = suc (fpc fs) }
  flat-exec-instr (instr-ctrl (c-thunk _ b))             _    fs = do-thunk b fs
  flat-exec-instr (instr-ctrl (c-ret b))                 _    fs = do-ret (fret fs) fs
  flat-exec-instr (instr-ctrl (c-jmp n))                 prog fs = do-jump (find-label prog n) fs
  flat-exec-instr (instr-ctrl (c-branch-scratch-zero n)) prog fs =
    do-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) n prog fs
  flat-exec-instr (instr-ctrl (c-branch-tag-zero n))     prog fs =
    do-branch (tag-zf (flat-read-tag (floc fs))) n prog fs
  -- the four %rsp-moving instructions also MOVE THE FRAME
  flat-exec-instr (instr-alloc-stack n)   _ fs = flat-step-frame (instr-alloc-stack n)   (enter-frame n)         fs
  flat-exec-instr (instr-dealloc-stack n) _ fs = flat-step-frame (instr-dealloc-stack n) leave-frame             fs
  flat-exec-instr (instr-push-frame cap)  _ fs = flat-step-frame (instr-push-frame cap)  (enter-frame (suc cap)) fs
  flat-exec-instr instr-pop-frame         _ fs = flat-step-frame instr-pop-frame         leave-frame             fs
  flat-exec-instr i                                      _    fs = flat-step-straight i fs

  ----------------------------------------------------------------------
  -- Fuel-bounded execution (with-free: dispatch on halted / fetch).
  ----------------------------------------------------------------------
  exec-flat      : ℕ → AbstractTrace → FlatState → FlatState
  step-dispatch  : Bool → ℕ → AbstractTrace → FlatState → FlatState
  fetch-dispatch : Maybe AbstractInstr → ℕ → AbstractTrace → FlatState → FlatState

  exec-flat zero    _    fs = fs
  exec-flat (suc n) prog fs = step-dispatch (halted (floc fs)) n prog fs

  step-dispatch true  _ _    fs = fs
  step-dispatch false n prog fs = fetch-dispatch (fetch prog (fpc fs)) n prog fs

  fetch-dispatch nothing  _ _    fs = record fs { floc = record (floc fs) { halted = true } }
  fetch-dispatch (just i) n prog fs = exec-flat n prog (flat-exec-instr i prog fs)

  ----------------------------------------------------------------------
  -- Plan 0.32 M3 Phase D: with-FREE reduction API over OPAQUE states.
  -- This is the real-path tool the exec-flat ↔ Semantics.exec
  -- correspondence proof uses (mirrors the x86 StepLemmas) — every lemma
  -- takes the decision value (halted / fetched instr) explicitly and is
  -- stated for an arbitrary `fs`, never a concrete construction.
  ----------------------------------------------------------------------
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
  open import Data.Nat.Properties using (+-suc; +-identityʳ)
  open import Data.Product using (Σ; _×_; _,_)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)

  -- A halted state is a fixpoint of exec-flat.
  exec-flat-halted : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → halted (floc fs) ≡ true
    → exec-flat n prog fs ≡ fs
  exec-flat-halted zero    _    fs _ = refl
  exec-flat-halted (suc n) prog fs h-eq rewrite h-eq = refl

  -- One fuel step: when not halted and the pc fetches `i`, exec-flat peels
  -- the instruction's effect and recurses. (The single reduction lemma the
  -- correspondence inducts on — one decision per rewrite, no `with`.)
  exec-flat-step : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ just i
    → exec-flat (suc n) prog fs ≡ exec-flat n prog (flat-exec-instr i prog fs)
  exec-flat-step n prog fs i h-eq f-eq rewrite h-eq | f-eq = refl

  ----------------------------------------------------------------------
  -- WHERE THE SCAN LANDS (Plan 0.63, obligation (iii)).
  --
  -- `find-label prog m ≡ just j` puts a `c-label m` AT j. Obvious, and the
  -- reason it is worth stating: it is what lets label scoping be proved
  -- WITHOUT label uniqueness. The segment lemma then only has to say "every
  -- position holding `c-label m` has segment X" — a property of all of them —
  -- instead of "the unique such position does", which would need the emitter
  -- to never reuse a label number.
  --
  -- `acc` is an offset, so the induction states the position as a delta.
  ----------------------------------------------------------------------
  -- `(m ≡ᵇ n) ≡ true` gives `m ≡ n` (the stdlib's `≡ᵇ⇒≡` wants `T`, and the
  -- scan hands us the Bool equation).
  ≡ᵇ-true : ∀ (m n : ℕ) → (m ≡ᵇ n) ≡ true → m ≡ n
  ≡ᵇ-true zero    zero    _  = refl
  ≡ᵇ-true (suc m) (suc n) eq = cong suc (≡ᵇ-true m n eq)

  -- `label-of? x ≡ just m` pins the instruction: only `c-label` produces one.
  -- Enumerated, because the catch-all does not invert.
  lab-eq : ∀ (x : AbstractInstr) (m : LabelId) → label-of? x ≡ just m → x ≡ instr-ctrl (c-label m)
  lab-eq (instr-ctrl (c-label m')) m eq = cong (λ z → instr-ctrl (c-label z)) (just-inj eq)
    where just-inj : ∀ {a b : LabelId} → just a ≡ just b → a ≡ b
          just-inj refl = refl

  fl-go-lands : ∀ (t : AbstractTrace) (target : LabelId) (acc j : ℕ)
              → fl-go t target acc ≡ just j
              → Σ ℕ (λ d → (j ≡ acc + d)
                    × (fetch t d ≡ just (instr-ctrl (c-label target))))
  fl-go-lands [] target acc j ()
  fl-go-lands (x ∷ is) target acc j eq = go (label-of? x) refl eq
    where
      step : ∀ (j' : ℕ) → fl-go is target (suc acc) ≡ just j'
           → Σ ℕ (λ d → (j' ≡ acc + d) × (fetch (x ∷ is) d ≡ just (instr-ctrl (c-label target))))
      step j' e with fl-go-lands is target (suc acc) j' e
      ... | d , j'≡ , ft = suc d , trans j'≡ (sym (+-suc acc d)) , ft
      go : ∀ (mlab : Maybe LabelId) → label-of? x ≡ mlab → fl-go (x ∷ is) target acc ≡ just j
         → Σ ℕ (λ d → (j ≡ acc + d) × (fetch (x ∷ is) d ≡ just (instr-ctrl (c-label target))))
      go nothing  le e rewrite le = step j e
      go (just m) le e rewrite le = match (m ≡ᵇᴵ target) refl e
        where
          match : ∀ (b : Bool) → (m ≡ᵇᴵ target) ≡ b → fl-label-match (m ≡ᵇᴵ target) is target acc ≡ just j
                → Σ ℕ (λ d → (j ≡ acc + d) × (fetch (x ∷ is) d ≡ just (instr-ctrl (c-label target))))
          match true  beq e' rewrite beq =
            0 , trans (sym (just-inj e')) (sym (+-identityʳ acc))
              , cong just (trans (lab-eq x m le) (cong (λ z → instr-ctrl (c-label z)) (≡ᵇᴵ-true m target beq)))
            where just-inj : ∀ {a b : ℕ} → just a ≡ just b → a ≡ b
                  just-inj refl = refl
          match false beq e' rewrite beq = step j e'

  find-label-lands : ∀ (prog : AbstractTrace) (target : LabelId) (j : ℕ)
                   → find-label prog target ≡ just j
                   → fetch prog j ≡ just (instr-ctrl (c-label target))
  find-label-lands prog target j eq with fl-go-lands prog target 0 j eq
  ... | d , j≡0+d , ft rewrite j≡0+d = ft

  -- pc past the end halts.
  exec-flat-offend : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ nothing
    → exec-flat (suc n) prog fs ≡ record fs { floc = record (floc fs) { halted = true } }
  exec-flat-offend n prog fs h-eq f-eq rewrite h-eq | f-eq = refl

  ----------------------------------------------------------------------
  -- Plan 0.32 choice (a): the exec-flat ↔ exec-trace bridge (jump-free).
  --
  -- `exec-flat` is THE abstract semantics; `exec-trace` survives only as a
  -- theorem about it on straight-line (jump-free) traces. The atom below:
  -- a "straight" instruction is any non-`instr-ctrl`. Its `flat-exec-instr`
  -- never consults `prog` (no `find-label`), so it equals `flat-step-straight`
  -- — i.e. it threads `exec-abstract` and bumps the pc, exactly as
  -- `exec-trace` threads `exec-abstract` over the suffix.
  --
  -- Evidence is carried per instruction (`λ _ _ → refl` at every concrete
  -- non-ctrl constructor; `instr-ctrl` has none). This sidesteps splitting
  -- the ~20 non-ctrl constructors — `flat-exec-instr`'s catch-all will not
  -- reduce for an abstract `i`.
  ----------------------------------------------------------------------
  StraightStep : AbstractInstr → Set
  StraightStep i = ∀ prog fs → flat-exec-instr i prog fs ≡ flat-step-straight i fs

  -- One straight step under fuel: peel the fetched instruction and advance,
  -- threading `exec-abstract` (built on the with-free `exec-flat-step`).
  exec-flat-straight-step : ∀ (n : ℕ) (prog : AbstractTrace) (fs : FlatState) (i : AbstractInstr)
    → halted (floc fs) ≡ false
    → fetch prog (fpc fs) ≡ just i
    → StraightStep i
    → exec-flat (suc n) prog fs ≡ exec-flat n prog (flat-step-straight i fs)
  exec-flat-straight-step n prog fs i h-eq f-eq straight =
    trans (exec-flat-step n prog fs i h-eq f-eq)
          (cong (exec-flat n prog) (straight prog fs))

  -- A jump-free trace: every instruction is straight.
  Straight : AbstractTrace → Set
  Straight = All StraightStep

  -- `fetch` into a trace all of whose instructions satisfy `P` yields a
  -- `P`-instruction. The general lookup-into-`All`; proven HERE inside
  -- `FlatMachine` where `fetch` reduces on the cons pattern (it refuses to
  -- under a downstream `open FlatMachine {FS}`). Downstream invariants
  -- (e.g. `CataNextSlot`'s next-slot preservation) instantiate `P`.
  fetch-All : ∀ {P : AbstractInstr → Set} {prog k i}
            → All P prog → fetch prog k ≡ just i → P i
  fetch-All {prog = []}             _          ()
  fetch-All {prog = x ∷ xs} {zero}  (px ∷ _)   refl = px
  fetch-All {prog = x ∷ xs} {suc k} (_  ∷ pxs) eq   = fetch-All pxs eq

  -- `fetch` into a straight trace yields a straight instruction.
  fetch-Straight : ∀ {prog k i} → Straight prog → fetch prog k ≡ just i → StraightStep i
  fetch-Straight = fetch-All

  -- A projection `f` invariant under exec-flat, given it is preserved by
  -- every `P`-instruction's step (`pi`) and by the off-end halt (`ph`), on
  -- a trace all of whose instructions satisfy `P`. Proven HERE (where
  -- `exec-flat` reduces; downstream `open FlatMachine {FS}` makes the
  -- recursive `exec-flat`/`fetch` opaque). The frame-discipline invariant
  -- (`next-slot` preserved) is the `f = next-slot ∘ falloc` instance.
  exec-flat-invariant : ∀ {A : Set} (f : FlatState → A) (P : AbstractInstr → Set)
    → (∀ i prog fs → P i → f (flat-exec-instr i prog fs) ≡ f fs)
    → (∀ fs → f (record fs { floc = record (floc fs) { halted = true } }) ≡ f fs)
    → ∀ (prog : AbstractTrace) → All P prog → ∀ (n : ℕ) (fs : FlatState)
    → f (exec-flat n prog fs) ≡ f fs
  exec-flat-invariant f P pi ph prog allp zero    fs = refl
  exec-flat-invariant f P pi ph prog allp (suc n) fs with halted (floc fs)
  ... | true  = refl
  ... | false with fetch prog (fpc fs) in feq
  ...   | nothing = ph fs
  ...   | just i  = trans (exec-flat-invariant f P pi ph prog allp n (flat-exec-instr i prog fs))
                          (pi i prog fs (fetch-All allp feq))

  -- Shift lemma: on a straight tail, exec-flat over `i ∷ rest` from pc
  -- `suc k` agrees with exec-flat over `rest` from pc `k` on the data
  -- (floc/falloc) — the pc differs by 1 throughout but the threaded
  -- LocState/AllocState are identical. By induction on fuel.
  shift-loc : ∀ (fuel : ℕ) (i : AbstractInstr) (rest : AbstractTrace)
                (loc : LocState FS) (alloc : AllocState {FS}) (k : ℕ)
    → Straight rest
    → floc   (exec-flat fuel (i ∷ rest) (mkFlat loc alloc (suc k)))
        ≡ floc   (exec-flat fuel rest (mkFlat loc alloc k))
    × falloc (exec-flat fuel (i ∷ rest) (mkFlat loc alloc (suc k)))
        ≡ falloc (exec-flat fuel rest (mkFlat loc alloc k))
  shift-loc zero    i rest loc alloc k straight = refl , refl
  shift-loc (suc n) i rest loc alloc k straight with halted loc in h-eq
  ... | true  rewrite exec-flat-halted (suc n) (i ∷ rest) (mkFlat loc alloc (suc k)) h-eq
                    | exec-flat-halted (suc n) rest        (mkFlat loc alloc k)       h-eq
                    = refl , refl
  ... | false with fetch rest k in f-eq
  ...   | nothing rewrite exec-flat-offend n (i ∷ rest) (mkFlat loc alloc (suc k)) h-eq f-eq
                        | exec-flat-offend n rest        (mkFlat loc alloc k)       h-eq f-eq
                        = refl , refl
  ...   | just j  rewrite fetch-Straight straight f-eq (i ∷ rest) (mkFlat loc alloc (suc k))
                        | fetch-Straight straight f-eq rest        (mkFlat loc alloc k)
                        = shift-loc n i rest
                            (proj₁ (exec-abstract j loc alloc))
                            (proj₂ (exec-abstract j loc alloc))
                            (suc k) straight

  -- A halted state is left at (s , alloc) by exec-trace (no instruction runs).
  exec-trace-halted : ∀ (prog : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS})
    → halted s ≡ true
    → exec-trace prog s alloc ≡ (s , alloc)
  exec-trace-halted []       s alloc _  = refl
  exec-trace-halted (x ∷ xs) s alloc ht rewrite ht = refl

  -- THE BRIDGE (Plan 0.32 choice a): on a jump-free trace, the flat machine's
  -- data output (floc/falloc, up to the terminal `halted` flag) IS exec-trace's
  -- output. `exec-flat` always halts at end-of-program, so we compare both
  -- floc's `forced` to halted=true — making the base + mid-halt cases refl and
  -- isolating the inductive content in the straight-step + shift lemmas.
  forced : LocState FS → LocState FS
  forced x = record x { halted = true }

  exec-trace-is-flat : ∀ (prog : AbstractTrace) (s : LocState FS) (alloc : AllocState {FS})
    → Straight prog
    → forced (floc (exec-flat (suc (length prog)) prog (mkFlat s alloc 0)))
        ≡ forced (proj₁ (exec-trace prog s alloc))
    × falloc (exec-flat (suc (length prog)) prog (mkFlat s alloc 0))
        ≡ proj₂ (exec-trace prog s alloc)
  exec-trace-is-flat prog s alloc straight with halted s in hs
  ... | true
        rewrite exec-flat-halted (suc (length prog)) prog (mkFlat s alloc 0) hs
              | exec-trace-halted prog s alloc hs = refl , refl
  exec-trace-is-flat [] s alloc straight | false
        rewrite exec-flat-offend 0 [] (mkFlat s alloc 0) hs refl = refl , refl
  -- `with halted s | false` already peeled ONE exec-flat step (-> flat-exec-instr i)
  -- and reduced exec-trace (i∷rest) -> exec-trace rest s' alloc'. Convert the
  -- stuck `flat-exec-instr i` to `flat-step-straight i` (= mkFlat s' alloc' 1)
  -- via the StraightStep evidence `pi`; then shift-loc + IH align directly.
  exec-trace-is-flat (i ∷ rest) s alloc (pi ∷ prest) | false
        rewrite pi (i ∷ rest) (mkFlat s alloc 0) =
    let s'     = proj₁ (exec-abstract i s alloc)
        alloc' = proj₂ (exec-abstract i s alloc)
        sl     = shift-loc (suc (length rest)) i rest s' alloc' 0 prest
        ih     = exec-trace-is-flat rest s' alloc' prest
        ctr    = exec-trace-cons i rest s alloc hs
    in trans (cong forced (proj₁ sl))
             (trans (proj₁ ih) (cong (λ p → forced (proj₁ p)) (sym ctr)))
     , trans (proj₂ sl)
             (trans (proj₂ ih) (cong proj₂ (sym ctr)))
