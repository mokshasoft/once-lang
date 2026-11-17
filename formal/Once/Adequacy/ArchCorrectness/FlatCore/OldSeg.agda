-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.OldSeg
--
-- MASTER'S POSITIONAL SCAN, and the old image's `Emitted` bundle built on it
-- (D452, plan 0.146 B1.6).
--
-- The arch layer reads one slot fact: a slot an instruction of the run
-- addresses is inside the current frame (`Emitted.em-slots`). Master's image
-- proves it by a scan of the code (`seg-at`: an entry pushes a reservation, a
-- `c-ret` pops one), which fits its layout of one entry and one return per
-- unit: the reservation in force at each pc is the current frame's
-- (`SegCur`), and a saved frame's is the one in force where it returns
-- (`RetSeg`). The scan is master's proof device; another image (the linear
-- core's, whose blocks copy their return into every branch) proves the same
-- run fact its own way, so the scan lives here, beside the one image it fits,
-- and not in the shared invariant (`RunWF.FrameWF`).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Once.Spec.Name using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.OldSeg
  (o : CanonicalName)
  (FS : FrameSemantics)
  (slot-size : ℕ)
  (word-eq : frame-word FS ≡ slot-size)
  where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)

open import Once.CCC.Machine.SMCore
open AllocState using (frame-slots; saved-frames)
open import Once.CCC.Machine.Locations using (Slot)
open import Once.CCC.Machine.InstrSlot using (slot-of)
open import Once.CCC.Machine.FrameFree using (ImageI; FrameFreeI)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open import Once.CCC.Machine.FlatStackSlot FS using (flat-same-frames; module SameFrames)
open SameFrames using (sf-slots; sf-saved; sf-ret)
open import Once.CCC.Codegen.SlotSeg
open SegState using (cur; saved)
open SlotBelow using (below)
open import Once.CCC.Codegen.LabelSeg using (mention-at; mention-of; once-label-of)
open import Once.CCC.Label using (LabelId; EntryId)
open import Once.CCC.Codegen.IRToTrace o using (ir-stack-budget)
open import Once.CCC.Codegen.ProgramImage using (program-image)
open import Once.CCC.Codegen.ProgramImageFacts o using (image-frame-free; image-alloc-min; image-slots; image-jump-in-segment)
open import Once.Denotation.Program using (IRFun; irProgram)
open import Once.IR using (IR)
open import Once.IRTy using (Unit)
open FrameSemantics FS using (Frame)

open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq
open import Once.Adequacy.ArchCorrectness.FlatCore.RunWF o FS slot-size word-eq
  using (PcView; pv-suc; pv-jump; pv-thunk; pv-ret; pv-start; pv-leave; pv-call; pv-call-fn; pcView;
         JumpPost; jp-suc; jp-halt; jp-to;
         old-start; old-calls; emitted-code-addr-has-body; emitted-thunk-guarded;
         call-site-shapeᴼ; ret-site-owesᴼ; ret-budget-matchesᴼ)

------------------------------------------------------------------------
-- THE SCAN'S STATIC FACTS: what master's image proves of its code.
------------------------------------------------------------------------

-- `fetch` is the frame-semantics-parameterised copy of the codegen layer's
-- `trace-lookup`; they bridge by an induction on the trace.
fetch≡lookup : ∀ (t : AbstractTrace) (k : ℕ) → fetch t k ≡ trace-lookup t k
fetch≡lookup []       _       = refl
fetch≡lookup (i ∷ is) zero    = refl
fetch≡lookup (i ∷ is) (suc k) = fetch≡lookup is k

record ScanFacts (prog : AbstractTrace) : Set where
  field
    sc-image : All ImageI prog
    sc-guard : GuardAt prog
    -- a slot an instruction addresses is below the segment in force
    sc-slots : ∀ k (i : AbstractInstr) (slot : Slot) → fetch prog k ≡ just i → slot-of i ≡ just slot
             → slot < cur (seg-at prog k (mkSeg 0 []))
    -- a jump stays in its segment (label scoping)
    sc-jump  : ∀ p q (m : LabelId) (st : SegState) → mention-at prog p ≡ just m → find-label prog m ≡ just q
             → seg-at prog q st ≡ seg-at prog p st
open ScanFacts

-- the old image's slots, below the reservation in force at their position
-- (`SlotBudget.SegOK`, through `ProgramImageFacts.image-slots`)
emitted-slot-below-budget : ∀ (tbl : List IRFun) (ir : IR Unit Unit) (k : ℕ) (i : AbstractInstr) (slot : Slot)
                          → fetch (program-image o (irProgram tbl ir)) k ≡ just i → slot-of i ≡ just slot
                          → slot < cur (seg-at (program-image o (irProgram tbl ir)) k (mkSeg 0 []))
emitted-slot-below-budget tbl ir k i slot ftq soq =
  below (allseg-at (program-image o (irProgram tbl ir)) k (image-slots tbl ir)
           (trans (sym (fetch≡lookup (program-image o (irProgram tbl ir)) k)) ftq)) slot soq

-- A frame-free instruction leaves the segment where it is. ENUMERATED: a
-- catchall would leave `seg-action i` stuck on the variable.
ff→seg-id : ∀ (i : AbstractInstr) → FrameFreeI i → is-id? (seg-action i) ≡ true
ff→seg-id (instr-ctrl (c-thunk _ _))          ()
ff→seg-id (instr-ctrl (c-ret _))              ()
ff→seg-id (instr-ctrl (c-label _))            _ = refl
ff→seg-id (instr-ctrl c-leave)                _ = refl
ff→seg-id (instr-ctrl (c-jmp _))              _ = refl
ff→seg-id (instr-ctrl (c-branch-tag-zero _))  _ = refl
ff→seg-id mov-to-output                       _ = refl
ff→seg-id mov-to-input                        _ = refl
ff→seg-id load-indirect                       _ = refl
ff→seg-id load-indirect-suc                   _ = refl
ff→seg-id (load-from-slot _)                  _ = refl
ff→seg-id (store-at-slot _)                   _ = refl
ff→seg-id store-indirect                      _ = refl
ff→seg-id store-indirect-suc                  _ = refl
ff→seg-id (lea-slot _)                        _ = refl
ff→seg-id (restore-input _)                   _ = refl
ff→seg-id (instr-alloc-stack _)               _ = refl
ff→seg-id (instr-dealloc-stack _)             _ = refl
ff→seg-id (instr-free-heap _)                 _ = refl
ff→seg-id (load-at _)                         _ = refl
ff→seg-id (store-at _)                        _ = refl
ff→seg-id (addr-at _)                         _ = refl
ff→seg-id (instr-room _)                      _ = refl
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
ff→seg-id (instr-alloc-heap _)                _ = refl
ff→seg-id (instr-reg-op _)                    _ = refl

-- The static segment does NOT move at a call: the reservation belongs to the
-- body's own entry (D086), the next instruction the callee runs.
call-seg-id : is-id? (seg-action instr-call-closure) ≡ true
call-seg-id = refl

------------------------------------------------------------------------
-- THE SCAN'S RUN INVARIANT.
------------------------------------------------------------------------

-- THE RESERVATION IN FORCE, and its ONE EXCEPTION (D092): the instant a call
-- has landed on an entry, the frame it entered reserves nothing while the scan
-- still reads the caller's segment. The pc then holds the entry, which
-- addresses no slot, so every consumer refutes the row from its instruction.
SegCur : AbstractTrace → FlatState → Set
SegCur prog fs =
  (frame-slots (falloc fs) ≡ cur (seg-at prog (fpc fs) (mkSeg 0 [])))
  ⊎ (Σ EntryId (λ ℓ → Σ ℕ (λ bb →
       (fetch prog (fpc fs) ≡ just (instr-ctrl (c-entry ℓ bb)))
       × (frame-slots (falloc fs) ≡ 0))))

-- each saved frame's reservation is the segment in force at the pc it returns
-- to; the frame stack and the return stack have one length
data RetSeg (prog : AbstractTrace) : List (Frame × ℕ) → List ℕ → Set where
  rs-[] : RetSeg prog [] []
  rs-∷  : ∀ {f b rpc frs rs}
        → b ≡ cur (seg-at prog rpc (mkSeg 0 []))
        → RetSeg prog frs rs
        → RetSeg prog ((f , b) ∷ frs) (rpc ∷ rs)

record SegWF (prog : AbstractTrace) (fs : FlatState) : Set where
  constructor mkSegWF
  field
    seg-cur   : SegCur prog fs
    seg-stack : RetSeg prog (saved-frames (falloc fs)) (fret fs)
open SegWF

run-seg-wf : ∀ prog → ScanFacts prog → ∀ (fs : FlatState) → Reachable prog 0 fs → SegWF prog fs
run-seg-wf prog sc = go
  where
    B₀ = mkSeg 0 []
    just-injI : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
    just-injI refl = refl
    go : ∀ (fs' : FlatState) → Reachable prog 0 fs' → SegWF prog fs'
    -- AT ENTRY the pc is 0 and `seg-at _ zero` is the starting state outright.
    go fs' (reach-start .fs' el eqB _) =
      mkSegWF (inj₁ (subst (λ z → frame-slots (falloc fs') ≡ cur (seg-at prog z B₀))
                           (sym (proj₁ el)) eqB))
              (subst₂ (RetSeg prog)
                      (sym (proj₁ (proj₂ (proj₂ (proj₂ el)))))
                      (sym (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ el))))))
                      rs-[])
    go .(flat-exec-instr i prog fs'') (reach-step i fs'' r' ftq h) =
      step (pcView i (fetch-All {prog = prog} {k = fpc fs''} (sc-image sc) ftq))
      where
        ih  = go fs'' r'
        lk : trace-lookup prog (fpc fs'') ≡ just i
        lk = trans (sym (fetch≡lookup prog (fpc fs''))) ftq
        seg-suc : seg-at prog (suc (fpc fs'')) B₀ ≡ seg-step i (seg-at prog (fpc fs'') B₀)
        seg-suc = seg-at-suc prog (fpc fs'') B₀ lk
        -- the pre-state's equation, at an instruction that is not an entry
        ih-eq : (∀ ℓ bb → i ≡ instr-ctrl (c-entry ℓ bb) → ⊥)
              → frame-slots (falloc fs'') ≡ cur (seg-at prog (fpc fs'') B₀)
        ih-eq nt = go-eq (seg-cur ih)
          where go-eq : SegCur prog fs''
                      → frame-slots (falloc fs'') ≡ cur (seg-at prog (fpc fs'') B₀)
                go-eq (inj₁ e) = e
                go-eq (inj₂ (ℓ , bb , tq , _)) =
                  ⊥-elim (nt ℓ bb (just-injI (trans (sym ftq) tq)))
        ff-not-thunk : FrameFreeI i → ∀ ℓ bb → i ≡ instr-ctrl (c-entry ℓ bb) → ⊥
        ff-not-thunk ff ℓ bb e = subst FrameFreeI e ff
        step : PcView i → SegWF prog (flat-exec-instr i prog fs'')
        -- FRAME-FREE, FALLING THROUGH: frames untouched, segment unmoved.
        step (pv-suc ff nj adv) =
          mkSegWF
            (inj₁ (trans (sf-slots same) (trans (ih-eq (ff-not-thunk ff)) (sym stable))))
            (subst₂ (RetSeg prog) (sym (sf-saved same)) (sym (sf-ret same)) (seg-stack ih))
          where
            same = flat-same-frames i prog fs'' ff
            stable : cur (seg-at prog (fpc (flat-exec-instr i prog fs'')) B₀)
                   ≡ cur (seg-at prog (fpc fs'') B₀)
            stable = cong cur (trans (cong (λ z → seg-at prog z B₀) (adv prog fs''))
                              (trans seg-suc
                                     (idle-step i (ff→seg-id i ff) (seg-at prog (fpc fs'') B₀))))
        -- FRAME-FREE JUMP: the segment survives by label scoping.
        step (pv-jump ff m mlab jp) =
          mkSegWF
            (inj₁ (trans (sf-slots same)
                         (trans (ih-eq (ff-not-thunk ff)) (sym (jgo (jp prog fs''))))))
            (subst₂ (RetSeg prog) (sym (sf-saved same)) (sym (sf-ret same)) (seg-stack ih))
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
                        (sc-jump sc (fpc fs'') q m B₀ lkm fq))
        -- THE ENTRY: `grow-frame bb` against `seg-push bb`, equal by construction.
        step (pv-thunk ℓ bb ieq) =
          mkSegWF (inj₁ (trans (cong (λ z → frame-slots (falloc (flat-exec-instr z prog fs''))) ieq)
                         (sym (cong cur (trans (cong (λ z → seg-at prog z B₀) (pc-eq ieq))
                                               (trans seg-suc (step-eq ieq)))))))
                  (subst₂ (RetSeg prog)
                          (sym (cong (λ z → saved-frames (falloc (flat-exec-instr z prog fs''))) ieq))
                          (sym (cong (λ z → fret (flat-exec-instr z prog fs'')) ieq))
                          (seg-stack ih))
          where
            pc-eq : i ≡ instr-ctrl (c-entry ℓ bb)
                  → fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')
            pc-eq refl = refl
            step-eq : i ≡ instr-ctrl (c-entry ℓ bb)
                    → seg-step i (seg-at prog (fpc fs'') B₀)
                      ≡ mkSeg bb (cur (seg-at prog (fpc fs'') B₀) ∷ saved (seg-at prog (fpc fs'') B₀))
            step-eq refl = refl
        -- THE START reserves the outermost frame as an entry reserves its own.
        step (pv-start bb ieq) =
          mkSegWF (inj₁ (trans (cong (λ z → frame-slots (falloc (flat-exec-instr z prog fs''))) ieq)
                         (sym (cong cur (trans (cong (λ z → seg-at prog z B₀) (pc-eq′ ieq))
                                               (trans seg-suc (step-eq′ ieq)))))))
                  (subst₂ (RetSeg prog)
                          (sym (cong (λ z → saved-frames (falloc (flat-exec-instr z prog fs''))) ieq))
                          (sym (cong (λ z → fret (flat-exec-instr z prog fs'')) ieq))
                          (seg-stack ih))
          where
            pc-eq′ : i ≡ instr-ctrl (c-start bb)
                   → fpc (flat-exec-instr i prog fs'') ≡ suc (fpc fs'')
            pc-eq′ refl = refl
            step-eq′ : i ≡ instr-ctrl (c-start bb)
                     → seg-step i (seg-at prog (fpc fs'') B₀)
                       ≡ mkSeg bb (cur (seg-at prog (fpc fs'') B₀) ∷ saved (seg-at prog (fpc fs'') B₀))
            step-eq′ refl = refl
        -- D320: THE LEAVE halts where it stands.
        step (pv-leave ieq) = subst (λ z → SegWF prog (flat-exec-instr z prog fs'')) (sym ieq)
                                (mkSegWF (seg-cur ih) (seg-stack ih))
        -- THE RETURN: the caller's reservation and the return pc belong together.
        step (pv-ret bb ieq) = ret-step ieq
          where
            ret-step : i ≡ instr-ctrl (c-ret bb) → SegWF prog (flat-exec-instr i prog fs'')
            ret-step refl = go-rs (fret fs'') (saved-frames (falloc fs'')) refl refl (seg-stack ih)
              where
                go-rs : ∀ (rs : List ℕ) (frs : List (Frame × ℕ))
                      → fret fs'' ≡ rs → saved-frames (falloc fs'') ≡ frs
                      → RetSeg prog frs rs
                      → SegWF prog (flat-exec-instr (instr-ctrl (c-ret bb)) prog fs'')
                -- an empty return stack HALTS with the pc unmoved
                go-rs [] [] req feq rs-[] =
                  mkSegWF (inj₁ (trans (cong frame-slots (do-ret-alloc fs''))
                          (trans (leave-frame-slots-[] (falloc fs'') feq)
                          (trans (ih-eq (λ _ _ ()))
                                 (cong (λ z → cur (seg-at prog z B₀))
                                       (sym (do-ret-pc-[] fs'' req)))))))
                          (subst₂ (RetSeg prog)
                                  (sym (trans (cong saved-frames (do-ret-alloc fs''))
                                              (leave-frame-saved-[] (falloc fs'') feq)))
                                  (sym (do-ret-fret-[] fs'' req)) rs-[])
                go-rs (rpc ∷ rs) ((f , b) ∷ frs) req feq (rs-∷ beq rest) =
                  mkSegWF (inj₁ (trans (cong frame-slots (do-ret-alloc fs''))
                          (trans (leave-frame-slots-∷ (falloc fs'') f b frs feq)
                          (trans beq (cong (λ z → cur (seg-at prog z B₀))
                                           (sym (do-ret-pc-∷ fs'' rpc rs req)))))))
                          (subst₂ (RetSeg prog)
                                  (sym (trans (cong saved-frames (do-ret-alloc fs''))
                                              (leave-frame-saved-∷ (falloc fs'') f b frs feq)))
                                  (sym (do-ret-fret-∷ fs'' rpc rs req)) rest)
                go-rs [] ((f , b) ∷ frs) req feq ()
                go-rs (rpc ∷ rs) [] req feq ()
        -- THE CALL (D092): `seg-cur` takes the exception row, and the caller's
        -- reservation is the segment at its return pc (the call is segment-idle).
        step (pv-call ieq) = call-go ieq
          where
            call-go : i ≡ instr-call-closure → SegWF prog (flat-exec-instr i prog fs'')
            call-go refl = cgo (callView prog fs'')
              where
                beq : frame-slots (falloc fs'') ≡ cur (seg-at prog (suc (fpc fs'')) B₀)
                beq = trans (ih-eq (λ _ _ ()))
                            (sym (cong cur (trans seg-suc
                                   (idle-step instr-call-closure call-seg-id
                                              (seg-at prog (fpc fs'') B₀)))))
                cgo : CallPost prog fs'' → SegWF prog (do-call prog fs'')
                cgo (cp-halt e) rewrite e = mkSegWF (seg-cur ih) (seg-stack ih)
                cgo (cp-enter ℓ j fteq e) rewrite e =
                  mkSegWF (inj₂ (e-thunk ℓ , proj₁ landing , proj₂ landing , refl))
                          (rs-∷ beq (seg-stack ih))
                  where landing = find-entry-sound prog (e-thunk ℓ) j fteq
        -- D245: THE DIRECT CALL, the same transfer to a statically named entry.
        step (pv-call-fn f ieq) = callfn-go ieq
          where
            callfn-go : i ≡ instr-ctrl (c-call-fn f) → SegWF prog (flat-exec-instr i prog fs'')
            callfn-go refl = cfgo (find-fn prog f) refl
              where
                beq : frame-slots (falloc fs'') ≡ cur (seg-at prog (suc (fpc fs'')) B₀)
                beq = trans (ih-eq (λ _ _ ()))
                            (sym (cong cur (trans seg-suc
                                   (idle-step (instr-ctrl (c-call-fn f)) refl
                                              (seg-at prog (fpc fs'') B₀)))))
                cfgo : ∀ (mj : Maybe ℕ) → find-fn prog f ≡ mj
                     → SegWF prog (do-call-at (find-fn prog f) fs'')
                cfgo nothing fe rewrite fe = mkSegWF (seg-cur ih) (seg-stack ih)
                cfgo (just j) fe rewrite fe =
                  mkSegWF (inj₂ (e-fn f , proj₁ landing , proj₂ landing , refl))
                          (rs-∷ beq (seg-stack ih))
                  where landing = find-entry-sound prog (e-fn f) j fe

-- THE RUN FACT: a slot the run addresses is inside the current frame — the
-- scan's positional bound, at the reservation in force (`SegCur`; its
-- exception row is an entry, which addresses no slot).
scan-slots : ∀ prog → ScanFacts prog → ∀ (fs : FlatState) (i : AbstractInstr) (slot : Slot)
           → Reachable prog 0 fs → fetch prog (fpc fs) ≡ just i → slot-of i ≡ just slot
           → slot < frame-slots (falloc fs)
scan-slots prog sc fs i slot r ftq soq =
  subst (slot <_) (sym (seg-eq (seg-cur (run-seg-wf prog sc fs r)))) (sc-slots sc (fpc fs) i slot ftq soq)
  where
    just-injI : ∀ {a b : AbstractInstr} → just a ≡ just b → a ≡ b
    just-injI refl = refl
    -- an entry addresses no slot
    no-slot : nothing ≡ just slot → ⊥
    no-slot ()
    seg-eq : SegCur prog fs → frame-slots (falloc fs) ≡ cur (seg-at prog (fpc fs) (mkSeg 0 []))
    seg-eq (inj₁ e) = e
    seg-eq (inj₂ (ℓ , bb , tq , _)) =
      ⊥-elim (no-slot (subst (λ z → slot-of z ≡ just slot) (just-injI (trans (sym ftq) tq)) soq))

------------------------------------------------------------------------
-- plan 0.146 B1.6: THE OLD IMAGE MEETS THE BUNDLE — its facts as they were (the
-- lowering's theorems, and master's postulates about it, narrowed to it).
------------------------------------------------------------------------
old-scan : ∀ (tbl : List IRFun) (ir : IR Unit Unit) → ScanFacts (program-image o (irProgram tbl ir))
old-scan tbl ir = record
  { sc-image = image-frame-free tbl ir
  ; sc-guard = emitted-thunk-guarded tbl ir
  ; sc-slots = emitted-slot-below-budget tbl ir
  ; sc-jump  = image-jump-in-segment {FS} tbl ir }

old-emitted : ∀ (tbl : List IRFun) (ir : IR Unit Unit) → LinkedImage tbl ir → Emitted (program-image o (irProgram tbl ir))
old-emitted tbl ir lk = record
  { em-budget     = ir-stack-budget ir
  ; em-zero       = refl
  ; em-start      = old-start tbl ir
  ; em-image      = image-frame-free tbl ir
  ; em-alloc      = image-alloc-min tbl ir
  ; em-guard      = emitted-thunk-guarded tbl ir
  ; em-slots      = scan-slots (program-image o (irProgram tbl ir)) (old-scan tbl ir)
  ; em-calls      = old-calls tbl ir lk
  ; em-code       = emitted-code-addr-has-body tbl ir
  ; em-call-site  = call-site-shapeᴼ tbl ir
  ; em-ret-owes   = ret-site-owesᴼ tbl ir
  ; em-ret-budget = ret-budget-matchesᴼ tbl ir }
