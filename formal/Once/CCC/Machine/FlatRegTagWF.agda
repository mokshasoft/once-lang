-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatRegTagWF
--
-- REGISTER-TAG well-formedness: the two counter registers `Scratch` and
-- `Count` always hold an `SV-Tag`.
--
-- This is what makes the counter instructions correspond to their x86
-- lowerings. Abstractly `sv-succ`/`sv-pred` COERCE a non-tag to a tag
-- (`sv-pred (SV-Ptr p) = SV-Tag 0`) while the concrete `add`/`sub` work on the
-- ENCODING, and `sv-is-zero` recognises only tags while `cmp` compares
-- encodings. So on a non-tag the two machines genuinely disagree, and
-- `branch-scratch-nontag` / `scratch-dec-nontag` / `count-inc-nontag` were
-- postulated to paper over exactly that.
--
-- The invariant is a STATE invariant — local, per instruction, compositional —
-- and NOT a whole-program dataflow fact. That is only true because plan 0.54 D
-- item 4 split the tally off `Input2` into its own `Count` register: the four
-- writers of `Scratch` (`scratch-one`, `scratch-zero`, `scratch-dec`,
-- `scratch-load-count`) and the two writers of `Count` (`count-zero`,
-- `count-inc`) ALL produce a tag unconditionally, the last two by reading a
-- register this very invariant says is a tag. Before the split,
-- `mov-output-to-input2` (`Input2 := Output`) could put an arbitrary value in
-- the tally, so no such invariant existed — and that instruction is documented
-- as intended for future nested-pair codegen, so the property was false by
-- design intent, not merely unproven.
--
-- Proved by induction over `exec-abstract`, mutually with `regtag-trace` /
-- `regtag-case` / `regtag-loop` so the nested `instr-case-on-tag` / `instr-loop`
-- traces are covered (mirroring `FlatStoreWF`). Lifted to `flat-exec-instr` at
-- the end. NO new postulates: `instr-sigop` writes only `Output` and `halted`,
-- so a SigOp cannot disturb a counter.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatRegTagWF (FS : FrameSemantics) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Memory.HeapAddress using (HeapLocation)
open import Once.CCC.Machine.SMCore
open FrameSemantics FS using (Frame)
open MemOps {FS}
open ExecFinal {FS}
open AbstractExec {FS}
open import Once.CCC.Machine.Flat
open FlatMachine {FS}

------------------------------------------------------------------------
-- "Holds a tag". Stated as an existential EQUATION rather than a predicate
-- with a catch-all (`IsTag (SV-Tag _) = ⊤; IsTag _ = ⊥`), because a catch-all
-- does not survive the case-tree translation and would not reduce at the use
-- sites — the same trap as `enc-sv`'s `SV-Lit` clause.
------------------------------------------------------------------------
IsTag : StoredValue FS → Set
IsTag sv = Σ ℕ (λ n → sv ≡ SV-Tag n)

record RegTagWF (ls : LocState FS) : Set where
  constructor mkRegTagWF
  field
    scratch-tag : IsTag (readReg (regs ls) Scratch)
    count-tag   : IsTag (readReg (regs ls) Count)
open RegTagWF public

-- The SHAPE form of the same fact, enumerated so that `IsTagP (SV-Ptr p)`
-- reduces to `⊥`. This is what kills a non-tag route at a use site: the route's
-- own case equation (`readReg … Scratch ≡ SV-Ptr p`) plus the invariant gives
-- an inhabitant of `⊥` directly, with no constructor-clash boilerplate at each
-- of the nine call sites.
IsTagP : StoredValue FS → Set
IsTagP (SV-Ptr _)   = ⊥
IsTagP (SV-Tag _)   = ⊤
IsTagP (SV-Lit _ _) = ⊥
IsTagP (SV-Code _)  = ⊥

is-tag-P : ∀ {sv : StoredValue FS} → IsTag sv → IsTagP sv
is-tag-P (k , refl) = tt

------------------------------------------------------------------------
-- The two coercions land on tags GIVEN a tag (that is the whole content: on a
-- non-tag they also land on a tag, but at a value the concrete machine does
-- not compute).
------------------------------------------------------------------------
sv-succ-tag : ∀ (v : StoredValue FS) → IsTag v → IsTag (sv-succ v)
sv-succ-tag .(SV-Tag n) (n , refl) = suc n , refl

sv-pred-tag : ∀ (v : StoredValue FS) → IsTag v → IsTag (sv-pred v)
sv-pred-tag .(SV-Tag zero)    (zero  , refl) = zero , refl
sv-pred-tag .(SV-Tag (suc n)) (suc n , refl) = n , refl

------------------------------------------------------------------------
-- Register writes. `Scratch`/`Count` are preserved by a write to any OTHER
-- register; the two writes that DO hit them carry a tag.
------------------------------------------------------------------------
regtag-write-other : ∀ {ls} (x : AbstractReg) (v : StoredValue FS)
  → (readReg (writeReg (regs ls) x v) Scratch ≡ readReg (regs ls) Scratch)
  → (readReg (writeReg (regs ls) x v) Count   ≡ readReg (regs ls) Count)
  → RegTagWF ls → RegTagWF (record ls { regs = writeReg (regs ls) x v })
regtag-write-other {ls} x v sc-p ct-p wf = record
  { scratch-tag = (proj₁ (scratch-tag wf)) , trans sc-p (proj₂ (scratch-tag wf))
  ; count-tag   = (proj₁ (count-tag wf))   , trans ct-p (proj₂ (count-tag wf)) }

-- Input1 / Input2 / Output writes: both counters untouched (definitional).
regtag-write-in1 : ∀ {ls} (v : StoredValue FS) → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Input1 v })
regtag-write-in1 {ls} v wf = regtag-write-other {ls} Input1 v refl refl wf

regtag-write-in2 : ∀ {ls} (v : StoredValue FS) → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Input2 v })
regtag-write-in2 {ls} v wf = regtag-write-other {ls} Input2 v refl refl wf

regtag-write-out : ∀ {ls} (v : StoredValue FS) → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Output v })
regtag-write-out {ls} v wf = regtag-write-other {ls} Output v refl refl wf

------------------------------------------------------------------------
-- The generic TRANSPORT: any state whose two counter cells read back
-- unchanged inherits the invariant. Every "this instruction does not touch a
-- counter" case is this lemma at `refl refl` — the equations hold
-- DEFINITIONALLY (record update on a field the reads don't mention), so the
-- clauses below carry no proof burden at all.
------------------------------------------------------------------------
regtag-transport : ∀ {ls'} (ls : LocState FS)
                 → readReg (regs ls') Scratch ≡ readReg (regs ls) Scratch
                 → readReg (regs ls') Count   ≡ readReg (regs ls) Count
                 → RegTagWF ls → RegTagWF ls'
regtag-transport ls sc ct wf = record
  { scratch-tag = (proj₁ (scratch-tag wf)) , trans sc (proj₂ (scratch-tag wf))
  ; count-tag   = (proj₁ (count-tag wf))   , trans ct (proj₂ (count-tag wf)) }

-- halting touches only the `halted` flag.
regtag-halt : ∀ {ls} → RegTagWF ls → RegTagWF (record ls { halted = true })
regtag-halt {ls} wf = regtag-transport ls refl refl wf

------------------------------------------------------------------------
-- "not one of the two counters". ENUMERATED (no catch-all), so
-- `NonCounter Output` reduces to `⊤` at the call sites — the load/store
-- helpers below are generic in their destination register, and this is what
-- lets them be applied at `Output` / `Input1` with `tt`.
------------------------------------------------------------------------
NonCounter : AbstractReg → Set
NonCounter Input1  = ⊤
NonCounter Input2  = ⊤
NonCounter Output  = ⊤
NonCounter Scratch = ⊥
NonCounter Count   = ⊥

regtag-write-nc : ∀ {ls} (x : AbstractReg) → NonCounter x → (v : StoredValue FS)
                → RegTagWF ls → RegTagWF (record ls { regs = writeReg (regs ls) x v })
regtag-write-nc {ls} Input1 _ v wf = regtag-transport ls refl refl wf
regtag-write-nc {ls} Input2 _ v wf = regtag-transport ls refl refl wf
regtag-write-nc {ls} Output _ v wf = regtag-transport ls refl refl wf

-- the SigOp shape: one non-counter register write AND a halt-flag update.
regtag-write-nc-halt : ∀ {ls} (x : AbstractReg) → NonCounter x
                     → (v : StoredValue FS) (b : Bool)
                     → RegTagWF ls
                     → RegTagWF (record ls { regs = writeReg (regs ls) x v ; halted = b })
regtag-write-nc-halt {ls} Input1 _ v b wf = regtag-transport ls refl refl wf
regtag-write-nc-halt {ls} Input2 _ v b wf = regtag-transport ls refl refl wf
regtag-write-nc-halt {ls} Output _ v b wf = regtag-transport ls refl refl wf

------------------------------------------------------------------------
-- The two writes that DO hit a counter. Both are unconditional tag producers
-- — that is the whole theorem, and the reason it is a LOCAL invariant.
------------------------------------------------------------------------
regtag-set-scratch : ∀ {ls} (v : StoredValue FS) → IsTag v → RegTagWF ls
                   → RegTagWF (record ls { regs = writeReg (regs ls) Scratch v })
regtag-set-scratch {ls} v tv wf = record { scratch-tag = tv ; count-tag = count-tag wf }

regtag-set-count : ∀ {ls} (v : StoredValue FS) → IsTag v → RegTagWF ls
                 → RegTagWF (record ls { regs = writeReg (regs ls) Count v })
regtag-set-count {ls} v tv wf = record { scratch-tag = scratch-tag wf ; count-tag = tv }

------------------------------------------------------------------------
-- The stack-slot counter is not a stored value: a `stackSlot`-only register
-- update leaves every register's CONTENT alone.
------------------------------------------------------------------------
regtag-stack-slot : ∀ {ls} (m : ℕ) → RegTagWF ls
                  → RegTagWF (record ls { regs = record (regs ls) { stackSlot = m } })
regtag-stack-slot {ls} m wf = regtag-transport ls refl refl wf

------------------------------------------------------------------------
-- Memory writes: `writeLoc` never touches `regs` (enumerated, because the
-- function itself dispatches on the location AND the value).
------------------------------------------------------------------------
regtag-write-loc : ∀ {ls} (loc : ValueLocation FS) (v : StoredValue FS)
                 → RegTagWF ls → RegTagWF (writeLoc ls loc v)
regtag-write-loc {ls} (AtStack f k)  v                        wf = regtag-transport ls refl refl wf
regtag-write-loc {ls} (AtDynamic hl) (SV-Ptr (AtStack f k))   wf = regtag-transport ls refl refl wf
regtag-write-loc {ls} (AtDynamic hl) (SV-Ptr (AtDynamic hl')) wf = regtag-transport ls refl refl wf
regtag-write-loc {ls} (AtDynamic hl) (SV-Tag t)               wf = regtag-transport ls refl refl wf
regtag-write-loc {ls} (AtDynamic hl) (SV-Lit p x)             wf = regtag-transport ls refl refl wf
regtag-write-loc {ls} (AtDynamic hl) (SV-Code c)              wf = regtag-transport ls refl refl wf

------------------------------------------------------------------------
-- The resolved load/store helpers (all of them target `Output` / `Input1`).
------------------------------------------------------------------------
regtag-load-value : ∀ {ls} (dst : AbstractReg) → NonCounter dst
                  → (mv : Maybe (StoredValue FS))
                  → RegTagWF ls → RegTagWF (exec-load-with-value dst mv ls)
regtag-load-value dst nc (just v) wf = regtag-write-nc dst nc v wf
regtag-load-value dst nc nothing  wf = regtag-halt wf

regtag-load-resolved : ∀ {ls} (dst : AbstractReg) → NonCounter dst
                     → (mloc : Maybe (ValueLocation FS))
                     → RegTagWF ls → RegTagWF (exec-load-via-resolved dst mloc ls)
regtag-load-resolved {ls} dst nc (just loc) wf = regtag-load-value dst nc (readLoc ls loc) wf
regtag-load-resolved      dst nc nothing    wf = regtag-halt wf

regtag-load-suc-resolved : ∀ {ls} (dst : AbstractReg) → NonCounter dst
                         → (mloc : Maybe (ValueLocation FS))
                         → RegTagWF ls → RegTagWF (exec-load-suc-via-resolved dst mloc ls)
regtag-load-suc-resolved {ls} dst nc (just loc) wf =
  regtag-load-value dst nc (readLoc ls (sucLoc loc)) wf
regtag-load-suc-resolved      dst nc nothing    wf = regtag-halt wf

regtag-store-resolved : ∀ {ls} (mloc : Maybe (ValueLocation FS)) (v : StoredValue FS)
                      → RegTagWF ls → RegTagWF (exec-store-via-resolved mloc v ls)
regtag-store-resolved (just loc) v wf = regtag-write-loc loc v wf
regtag-store-resolved nothing    v wf = regtag-halt wf

regtag-store-suc-resolved : ∀ {ls} (mloc : Maybe (ValueLocation FS)) (v : StoredValue FS)
                          → RegTagWF ls → RegTagWF (exec-store-suc-via-resolved mloc v ls)
regtag-store-suc-resolved (just loc) v wf = regtag-write-loc (sucLoc loc) v wf
regtag-store-suc-resolved nothing    v wf = regtag-halt wf

regtag-lea-indexed : ∀ {ls} (mloc : Maybe (ValueLocation FS)) (i : ℕ)
                   → RegTagWF ls → RegTagWF (exec-lea-indexed-via mloc i ls)
regtag-lea-indexed (just loc) i wf = regtag-write-nc Input1 tt (SV-Ptr (offsetLoc loc i)) wf
regtag-lea-indexed nothing    i wf = regtag-halt wf

-- the two slot loads thread `alloc` through, so they need their own shape.
regtag-slot-load-out : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS)
                         (alloc : AllocState {FS})
                     → RegTagWF ls
                     → RegTagWF (proj₁ (exec-load-from-slot-with-value mv ls alloc))
regtag-slot-load-out (just v) ls alloc wf = regtag-write-nc Output tt v wf
regtag-slot-load-out nothing  ls alloc wf = regtag-halt wf

regtag-slot-load-in1 : ∀ (mv : Maybe (StoredValue FS)) (ls : LocState FS)
                         (alloc : AllocState {FS})
                     → RegTagWF ls
                     → RegTagWF (proj₁ (exec-restore-input-with-value mv ls alloc))
regtag-slot-load-in1 (just v) ls alloc wf = regtag-write-nc Input1 tt v wf
regtag-slot-load-in1 nothing  ls alloc wf = regtag-halt wf

------------------------------------------------------------------------
-- THE INVARIANT IS PRESERVED by every abstract instruction.
--
-- Unlike `FlatStoreWF`, nothing has to be bundled with it: the predicate
-- mentions the `LocState` only (no allocation frontier), so there is no index
-- to transport and no monotonicity side-condition — the loop case re-anchors
-- the stack, which `RegTagWF` cannot see.
------------------------------------------------------------------------
-- THE LOOP, as a plain FUEL induction over the reified `exec-loop-run`
-- (2026-07-31). It takes "the body runner preserves the invariant" as a
-- hypothesis and never calls into the mutual block, so it is structural — this
-- is what retired the `{-# TERMINATING #-}` this proof used to carry.
------------------------------------------------------------------------
mutual
  regtag-loop-run : ∀ (run : BodyRunner) (fuel : ℕ) (ls : LocState FS) (alloc : AllocState {FS})
                  → (∀ ls' alloc' → RegTagWF ls' → RegTagWF (proj₁ (run ls' alloc')))
                  → RegTagWF ls → RegTagWF (proj₁ (exec-loop-run run fuel ls alloc))
  regtag-loop-run run zero    ls alloc h wf = regtag-halt wf
  regtag-loop-run run (suc n) ls alloc h wf with halted ls
  ... | true  = wf
  ... | false with readReg (regs ls) Scratch
  ...   | SV-Tag zero    = wf
  ...   | SV-Tag (suc m) = regtag-loop-run-go run n ls alloc h wf
  ...   | SV-Ptr _       = regtag-loop-run-go run n ls alloc h wf
  ...   | SV-Lit _ _     = regtag-loop-run-go run n ls alloc h wf
  ...   | SV-Code _      = regtag-loop-run-go run n ls alloc h wf

  -- one iteration: run the body, RE-ANCHOR the stack/frame, recurse on fuel.
  -- The re-anchoring is invisible to this invariant (it touches `stackMem` and
  -- the frame fields, not `regs`), so the body's witness transports by `refl`.
  regtag-loop-run-go : ∀ (run : BodyRunner) (n : ℕ) (ls : LocState FS) (alloc : AllocState {FS})
                     → (∀ ls' alloc' → RegTagWF ls' → RegTagWF (proj₁ (run ls' alloc')))
                     → RegTagWF ls
                     → RegTagWF (proj₁ (exec-loop-run run n
                         (loop-reanchor-loc ls (proj₁ (run ls alloc)))
                         (loop-reanchor-alloc alloc (proj₂ (run ls alloc)))))
  regtag-loop-run-go run n ls alloc h wf =
    regtag-loop-run run n _ _ h
      (regtag-transport (proj₁ (run ls alloc)) refl refl (h ls alloc wf))

------------------------------------------------------------------------
mutual
  regtag-abstract : ∀ (i : AbstractInstr) (ls : LocState FS) (alloc : AllocState {FS})
                  → RegTagWF ls → RegTagWF (proj₁ (exec-abstract i ls alloc))
  regtag-abstract mov-to-output ls alloc wf =
    regtag-write-nc Output tt (readReg (regs ls) Input1) wf
  regtag-abstract mov-to-input ls alloc wf =
    regtag-write-nc Input1 tt (readReg (regs ls) Output) wf
  regtag-abstract mov-output-to-input2 ls alloc wf =
    regtag-write-nc Input2 tt (readReg (regs ls) Output) wf
  regtag-abstract mov-input2-to-output ls alloc wf =
    regtag-write-nc Output tt (readReg (regs ls) Input2) wf
  regtag-abstract load-indirect ls alloc wf =
    regtag-load-resolved Output tt (sv-as-loc (readReg (regs ls) Input1)) wf
  regtag-abstract load-indirect-suc ls alloc wf =
    regtag-load-suc-resolved Output tt (sv-as-loc (readReg (regs ls) Input1)) wf
  regtag-abstract (load-from-slot slot) ls alloc wf =
    regtag-slot-load-out (readLoc ls (AtStack (current-frame alloc) slot)) ls alloc wf
  regtag-abstract (store-at-slot slot) ls alloc wf =
    regtag-write-loc (AtStack (current-frame alloc) slot) (readReg (regs ls) Output) wf
  regtag-abstract store-indirect ls alloc wf =
    regtag-store-resolved (sv-as-loc (readReg (regs ls) Input1)) (readReg (regs ls) Output) wf
  regtag-abstract store-indirect-suc ls alloc wf =
    regtag-store-suc-resolved (sv-as-loc (readReg (regs ls) Input1)) (readReg (regs ls) Output) wf
  regtag-abstract (lea-slot slot) ls alloc wf =
    regtag-write-nc Output tt (SV-Ptr (AtStack (current-frame alloc) slot)) wf
  regtag-abstract (restore-input slot) ls alloc wf =
    regtag-slot-load-in1 (readLoc ls (AtStack (current-frame alloc) slot)) ls alloc wf
  regtag-abstract (lea-indexed slot) ls alloc wf =
    regtag-lea-indexed (slot-base (readLoc ls (AtStack (current-frame alloc) slot)))
      (sv-tag-val (readReg (regs ls) Scratch)) wf
  regtag-abstract (instr-alloc-stack n) ls alloc wf = regtag-stack-slot _ wf
  regtag-abstract (instr-dealloc-stack n) ls alloc wf = regtag-stack-slot _ wf
  regtag-abstract (instr-reclaim-to n) ls alloc wf = wf
  regtag-abstract (instr-push-frame cap) ls alloc wf = regtag-stack-slot 0 wf
  regtag-abstract instr-pop-frame ls alloc wf = wf
  regtag-abstract instr-call-closure ls alloc wf = wf
  regtag-abstract (worklist-init slot) ls alloc wf = wf
  regtag-abstract (worklist-push slot) ls alloc wf =
    regtag-write-loc (AtStack (current-frame alloc) slot) (readReg (regs ls) Output) wf
  regtag-abstract (worklist-pop slot) ls alloc wf =
    regtag-slot-load-out (readLoc ls (AtStack (current-frame alloc) slot)) ls alloc wf
  regtag-abstract (worklist-check slot) ls alloc wf = wf
  -- A SigOp writes ONLY `Output` and `halted` — it cannot disturb a counter,
  -- so no SigOp-side axiom is needed here (contrast `FlatStoreWF`, whose value
  -- claim needs `structured-pure-sigop-below`).
  regtag-abstract (instr-sigop si) ls alloc wf =
    regtag-write-nc-halt Output tt (exec-sigop-output si ls) (exec-sigop-halts si ls) wf
  regtag-abstract (instr-load-const p v) ls alloc wf = regtag-write-nc Output tt (SV-Lit p v) wf
  regtag-abstract (instr-load-code-addr n) ls alloc wf = regtag-write-nc Output tt (SV-Code n) wf
  regtag-abstract instr-save-closure-reg ls alloc wf = wf
  regtag-abstract (instr-load-tag-lit n) ls alloc wf = regtag-write-nc Output tt (SV-Tag n) wf
  regtag-abstract (instr-case-on-tag f g) ls alloc wf = regtag-case (case-tag-at ls) f g ls alloc wf
  regtag-abstract (instr-alloc-heap n) ls alloc wf =
    regtag-write-nc Output tt _ wf
  regtag-abstract (instr-loop body) ls alloc wf =
    regtag-loop-run (exec-trace body) 1000000 ls alloc
      (λ ls' alloc' → regtag-trace body ls' alloc') wf
  -- THE COUNTER WRITES. All six produce a tag unconditionally; `scratch-dec`
  -- and `count-inc` do so BY THE INVARIANT (`sv-pred`/`sv-succ` of a tag),
  -- `scratch-load-count` by the other half of it.
  regtag-abstract (instr-reg-op scratch-one) ls alloc wf =
    regtag-set-scratch (SV-Tag 1) (1 , refl) wf
  regtag-abstract (instr-reg-op scratch-zero) ls alloc wf =
    regtag-set-scratch (SV-Tag 0) (0 , refl) wf
  regtag-abstract (instr-reg-op scratch-dec) ls alloc wf =
    regtag-set-scratch (sv-pred (readReg (regs ls) Scratch))
      (sv-pred-tag (readReg (regs ls) Scratch) (scratch-tag wf)) wf
  regtag-abstract (instr-reg-op scratch-load-count) ls alloc wf =
    regtag-set-scratch (readReg (regs ls) Count) (count-tag wf) wf
  regtag-abstract (instr-reg-op count-zero) ls alloc wf =
    regtag-set-count (SV-Tag 0) (0 , refl) wf
  regtag-abstract (instr-reg-op count-inc) ls alloc wf =
    regtag-set-count (sv-succ (readReg (regs ls) Count))
      (sv-succ-tag (readReg (regs ls) Count) (count-tag wf)) wf
  regtag-abstract (instr-ctrl c) ls alloc wf = wf

  regtag-trace : ∀ (t : AbstractTrace) (ls : LocState FS) (alloc : AllocState {FS})
               → RegTagWF ls → RegTagWF (proj₁ (exec-trace t ls alloc))
  regtag-trace [] ls alloc wf = wf
  regtag-trace (i ∷ is) ls alloc wf with halted ls
  ... | true  = wf
  ... | false = regtag-trace is (proj₁ (exec-abstract i ls alloc))
                                (proj₂ (exec-abstract i ls alloc))
                                (regtag-abstract i ls alloc wf)

  regtag-case : ∀ (mv : Maybe (StoredValue FS)) (f g : AbstractTrace)
                  (ls : LocState FS) (alloc : AllocState {FS})
              → RegTagWF ls → RegTagWF (proj₁ (exec-case-dispatch mv f g ls alloc))
  regtag-case (just (SV-Tag zero))    f g ls alloc wf = regtag-trace f ls alloc wf
  regtag-case (just (SV-Tag (suc _))) f g ls alloc wf = regtag-trace g ls alloc wf
  regtag-case (just (SV-Ptr _))       f g ls alloc wf = regtag-halt wf
  regtag-case (just (SV-Lit _ _))     f g ls alloc wf = regtag-halt wf
  regtag-case (just (SV-Code _))      f g ls alloc wf = regtag-halt wf
  regtag-case nothing                 f g ls alloc wf = regtag-halt wf

------------------------------------------------------------------------
-- Lifted to the FLAT machine.
------------------------------------------------------------------------
FlatRegTag : FlatState → Set
FlatRegTag fs = RegTagWF (floc fs)

-- The two USE-SITE forms: "the value the case split says the counter holds is a
-- tag". At a non-tag route the codomain reduces to `⊥`.
flat-scratch-is-tag : ∀ (fs : FlatState) (sv : StoredValue FS) → FlatRegTag fs
                    → readReg (regs (floc fs)) Scratch ≡ sv → IsTagP sv
flat-scratch-is-tag fs sv wf eq =
  is-tag-P ((proj₁ (scratch-tag wf)) , trans (sym eq) (proj₂ (scratch-tag wf)))

flat-count-is-tag : ∀ (fs : FlatState) (sv : StoredValue FS) → FlatRegTag fs
                  → readReg (regs (floc fs)) Count ≡ sv → IsTagP sv
flat-count-is-tag fs sv wf eq =
  is-tag-P ((proj₁ (count-tag wf)) , trans (sym eq) (proj₂ (count-tag wf)))

regtag-jump : ∀ (mpc : Maybe ℕ) (fs : FlatState) → FlatRegTag fs → FlatRegTag (do-jump mpc fs)
regtag-jump (just pc') fs wf = wf
regtag-jump nothing    fs wf = regtag-halt wf

regtag-branch : ∀ (b : Bool) (m : ℕ) (prog : AbstractTrace) (fs : FlatState)
              → FlatRegTag fs → FlatRegTag (do-branch b m prog fs)
regtag-branch true  m prog fs wf = regtag-jump (find-label prog m) fs wf
regtag-branch false m prog fs wf = wf

-- Plan 0.63: a return releases the frame and moves `fpc`/`fret`, or halts
-- on an empty return stack. `FlatRegTag` is a claim about the REGISTER
-- FILE and does not mention the AllocState, so both the frame move and the
-- pop are invisible to it (contrast `flat-wf-step`, which transports the
-- frontier through `leave-frame`).
regtag-ret : ∀ (r : List ℕ) (fs : FlatState) → FlatRegTag fs → FlatRegTag (do-ret r fs)
regtag-ret []           fs wf = regtag-halt wf
regtag-ret (pc' ∷ rest) fs wf = wf

-- ONE flat step preserves the counter-tag invariant. The straight-line cases
-- are ENUMERATED (a catch-all would not reduce `flat-exec-instr`'s own
-- catch-all in the case tree); each is `regtag-abstract`. The four frame-moving
-- instructions need NOTHING extra — `RegTagWF` is not indexed by the
-- AllocState, so `enter-frame`/`leave-frame` are invisible to it (contrast
-- `flat-wf-step`, which has to transport the frontier through `leave-frame`).
flat-regtag-step : ∀ (i : AbstractInstr) (prog : AbstractTrace) (fs : FlatState)
                 → FlatRegTag fs → FlatRegTag (flat-exec-instr i prog fs)
flat-regtag-step (instr-ctrl (c-label m))               prog fs wf = wf
flat-regtag-step (instr-ctrl (c-thunk m b))             prog fs wf = wf
flat-regtag-step (instr-ctrl (c-ret b))                 prog fs wf = regtag-ret (fret fs) fs wf
flat-regtag-step (instr-ctrl (c-jmp m))                 prog fs wf = regtag-jump (find-label prog m) fs wf
flat-regtag-step (instr-ctrl (c-branch-scratch-zero m)) prog fs wf =
  regtag-branch (sv-is-zero (readReg (regs (floc fs)) Scratch)) m prog fs wf
flat-regtag-step (instr-ctrl (c-branch-tag-zero m))     prog fs wf =
  regtag-branch (tag-zf (flat-read-tag (floc fs))) m prog fs wf
flat-regtag-step mov-to-output            prog fs wf = regtag-abstract mov-to-output (floc fs) (falloc fs) wf
flat-regtag-step mov-to-input             prog fs wf = regtag-abstract mov-to-input (floc fs) (falloc fs) wf
flat-regtag-step mov-output-to-input2     prog fs wf = regtag-abstract mov-output-to-input2 (floc fs) (falloc fs) wf
flat-regtag-step mov-input2-to-output     prog fs wf = regtag-abstract mov-input2-to-output (floc fs) (falloc fs) wf
flat-regtag-step load-indirect            prog fs wf = regtag-abstract load-indirect (floc fs) (falloc fs) wf
flat-regtag-step load-indirect-suc        prog fs wf = regtag-abstract load-indirect-suc (floc fs) (falloc fs) wf
flat-regtag-step (load-from-slot k)       prog fs wf = regtag-abstract (load-from-slot k) (floc fs) (falloc fs) wf
flat-regtag-step (store-at-slot k)        prog fs wf = regtag-abstract (store-at-slot k) (floc fs) (falloc fs) wf
flat-regtag-step store-indirect           prog fs wf = regtag-abstract store-indirect (floc fs) (falloc fs) wf
flat-regtag-step store-indirect-suc       prog fs wf = regtag-abstract store-indirect-suc (floc fs) (falloc fs) wf
flat-regtag-step (lea-slot k)             prog fs wf = regtag-abstract (lea-slot k) (floc fs) (falloc fs) wf
flat-regtag-step (restore-input k)        prog fs wf = regtag-abstract (restore-input k) (floc fs) (falloc fs) wf
flat-regtag-step (lea-indexed k)          prog fs wf = regtag-abstract (lea-indexed k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-alloc-stack k)    prog fs wf = regtag-abstract (instr-alloc-stack k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-dealloc-stack k)  prog fs wf = regtag-abstract (instr-dealloc-stack k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-reclaim-to k)     prog fs wf = regtag-abstract (instr-reclaim-to k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-push-frame k)     prog fs wf = regtag-abstract (instr-push-frame k) (floc fs) (falloc fs) wf
flat-regtag-step instr-pop-frame          prog fs wf = regtag-abstract instr-pop-frame (floc fs) (falloc fs) wf
flat-regtag-step instr-call-closure       prog fs wf = regtag-abstract instr-call-closure (floc fs) (falloc fs) wf
flat-regtag-step (worklist-init k)        prog fs wf = regtag-abstract (worklist-init k) (floc fs) (falloc fs) wf
flat-regtag-step (worklist-push k)        prog fs wf = regtag-abstract (worklist-push k) (floc fs) (falloc fs) wf
flat-regtag-step (worklist-pop k)         prog fs wf = regtag-abstract (worklist-pop k) (floc fs) (falloc fs) wf
flat-regtag-step (worklist-check k)       prog fs wf = regtag-abstract (worklist-check k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-sigop si)         prog fs wf = regtag-abstract (instr-sigop si) (floc fs) (falloc fs) wf
flat-regtag-step (instr-load-const p v)   prog fs wf = regtag-abstract (instr-load-const p v) (floc fs) (falloc fs) wf
flat-regtag-step (instr-load-code-addr k) prog fs wf = regtag-abstract (instr-load-code-addr k) (floc fs) (falloc fs) wf
flat-regtag-step instr-save-closure-reg   prog fs wf = regtag-abstract instr-save-closure-reg (floc fs) (falloc fs) wf
flat-regtag-step (instr-load-tag-lit k)   prog fs wf = regtag-abstract (instr-load-tag-lit k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-case-on-tag f g)  prog fs wf = regtag-abstract (instr-case-on-tag f g) (floc fs) (falloc fs) wf
flat-regtag-step (instr-alloc-heap k)     prog fs wf = regtag-abstract (instr-alloc-heap k) (floc fs) (falloc fs) wf
flat-regtag-step (instr-loop body)        prog fs wf = regtag-abstract (instr-loop body) (floc fs) (falloc fs) wf
flat-regtag-step (instr-reg-op op)        prog fs wf = regtag-abstract (instr-reg-op op) (floc fs) (falloc fs) wf
