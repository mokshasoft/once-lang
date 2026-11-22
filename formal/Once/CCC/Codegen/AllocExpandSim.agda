-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandSim — the expansion's simulation, a step at a time (D468, 3c3b).
--
-- `core-straight`: a step of the primitive program that keeps its allocator
-- and moves to the next instruction, done by the one instruction it expands to,
-- keeps the relation, given the step's memory relation (`LRel`) and that the
-- expanded heap changed only at live blocks' renamed cells (so the record, the
-- sentinel and the free blocks are as they were).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandSim {FS : FrameSemantics} where

open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState)
open FlatState
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rhl; rv; blk; rec-loc)
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel; Live; Chain)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off)

module _ (C : Classes) (P : AbstractTrace) where
  open Rel

  -- a chain read through a heap that agrees on its cells
  chain-frame : ∀ (h h′ : HeapMem FS) σ (bs : List ℕ) v
              → (∀ b → b ∈ bs → h′ (heap-loc (mkHeapRef b) 0) ≡ h (heap-loc (mkHeapRef b) 0))
              → Chain h σ bs v → Chain h′ σ bs v
  chain-frame h h′ σ []       v same c = c
  chain-frame h h′ σ (b ∷ bs) v same (e , w , hw , c) =
    e , w , trans (same b (here refl)) hw , chain-frame h h′ σ bs w (λ b′ m → same b′ (there m)) c

  -- ★ a step that keeps the allocator and moves on
  core-straight : ∀ {fs gs} (R : Rel C P fs gs) (A B : LocState FS)
                → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) A B
                → (∀ q → (∀ r → Live (falloc fs) r → ¬ ρ R r ≡ ref-of q) → LocState.heapMem B q ≡ LocState.heapMem (floc gs) q)
                → off C 0 P (suc (fpc fs)) ≡ suc (fpc gs)
                → Rel C P (record fs { floc = A ; fpc = suc (fpc fs) }) (record gs { floc = B ; fpc = suc (fpc gs) })
  core-straight {fs} {gs} R A B LR frame pc = record
    { ρ = ρ R ; σ = σ R ; lists = lists R
    ; r-pc = sym pc
    ; r-ret = r-ret R ; r-link = r-link R
    ; r-frame = r-frame R ; r-saved = r-saved R ; r-slots = r-slots R ; r-next-slot = r-next-slot R
    ; r-inj = r-inj R
    ; r-loc = LR
    ; r-clo = r-clo R
    ; r-size = r-size R
    ; r-below = r-below R ; r-not-σ = r-not-σ R ; r-not-free = r-not-free R
    ; r-heads = heads′
    ; r-sent = trans (frame (heap-loc (mkHeapRef (σ R)) 0) (λ r lv e → r-not-σ R r lv e)) (r-sent R)
    ; r-nofree = r-nofree R
    ; r-unsized = r-unsized R }
    where
      -- the record's words: no live block is renamed to ref 0
      rec-free : ∀ k → LocState.heapMem B (rec-loc k) ≡ LocState.heapMem (floc gs) (rec-loc k)
      rec-free k = frame (rec-loc k) (λ r lv e → Data.Nat.Properties.<-irrefl (sym e) (proj₁ (r-below R r lv)))
      heads′ : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem B (rec-loc (head-word c)) ≡ just v
                                                         × Chain (LocState.heapMem B) (σ R) (lists R c) v
      heads′ c c< = hd (r-heads R c c<)
        where
          hd : (Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v)
             → Σ (StoredValue FS) λ v → LocState.heapMem B (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem B) (σ R) (lists R c) v
          hd (v , e , ch) = v , trans (rec-free (head-word c)) e
                          , chain-frame (LocState.heapMem (floc gs)) (LocState.heapMem B) (σ R) (lists R c) v
                              (λ b m → frame (heap-loc (mkHeapRef b) 0) (λ r lv e′ → r-not-free R r c b lv m e′)) ch

  ------------------------------------------------------------------------
  -- ★ The register and slot instructions, one by one
  ------------------------------------------------------------------------

  open FlatMachine {FS} using (flat-exec-instr; fetch)
  open import Once.CCC.Codegen.AllocExpandPc {FS} using (off-suc)
  open import Data.Bool using (Bool; true; false)
  import Once.Type

  E = expand C P

  -- the next pc, for an instruction the expansion keeps
  next-pc : ∀ {fs gs} (R : Rel C P fs gs) i → fetch P (fpc fs) ≡ just i → expand-at C (fpc fs + 0) i ≡ i ∷ []
          → off C 0 P (suc (fpc fs)) ≡ suc (fpc gs)
  next-pc {fs} {gs} R i f ex =
    trans (off-suc C 0 P (fpc fs) i f)
      (trans (cong (λ xs → off C 0 P (fpc fs) + length xs) ex)
        (trans (Data.Nat.Properties.+-comm (off C 0 P (fpc fs)) 1) (cong suc (sym (r-pc R)))))

  step-mov-out : ∀ {fs gs} (R : Rel C P fs gs) → fetch P (fpc fs) ≡ just mov-to-output
               → Rel C P (flat-exec-instr mov-to-output P fs) (flat-exec-instr mov-to-output E gs)
  step-mov-out {fs} {gs} R f =
    core-straight R _ _ (L.Slots.mov-out (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) (r-loc R))
      (λ q _ → refl) (next-pc R mov-to-output f refl)

  step-mov-in : ∀ {fs gs} (R : Rel C P fs gs) → fetch P (fpc fs) ≡ just mov-to-input
              → Rel C P (flat-exec-instr mov-to-input P fs) (flat-exec-instr mov-to-input E gs)
  step-mov-in {fs} {gs} R f =
    core-straight R _ _ (L.Slots.mov-in (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) (r-loc R))
      (λ q _ → refl) (next-pc R mov-to-input f refl)

  open FlatMachine {FS} using (straight-at; straight-go)

  -- ★ a gated straight step: the gate is the same on both sides, and when it
  -- fails the primitive faults (which a sound run does not)
  gated-step : ∀ {fs gs} (R : Rel C P fs gs) i (bP bE : Bool) (A B : LocState FS)
             → flat-exec-instr i P fs ≡ straight-at bP i fs → flat-exec-instr i E gs ≡ straight-at bE i gs → bE ≡ bP
             → straight-go i fs ≡ record fs { floc = A ; fpc = suc (fpc fs) }
             → straight-go i gs ≡ record gs { floc = B ; fpc = suc (fpc gs) }
             → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) A B
             → (∀ q → (∀ r → Live (falloc fs) r → ¬ ρ R r ≡ ref-of q) → LocState.heapMem B q ≡ LocState.heapMem (floc gs) q)
             → off C 0 P (suc (fpc fs)) ≡ suc (fpc gs)
             → LocState.faulted (floc (flat-exec-instr i P fs)) ≡ false
             → Rel C P (flat-exec-instr i P fs) (flat-exec-instr i E gs)
  gated-step {fs} {gs} R i true  .true A B eP eE refl gP gE LR frame pc nf =
    subst (λ x → Rel C P x (flat-exec-instr i E gs)) (sym (trans eP gP))
      (subst (λ y → Rel C P (record fs { floc = A ; fpc = suc (fpc fs) }) y) (sym (trans eE gE))
         (core-straight R A B LR frame pc))
  gated-step {fs} {gs} R i false .false A B eP eE refl gP gE LR frame pc nf = absurd (trans (sym (cong (λ x → LocState.faulted (floc x)) eP)) nf)
    where
      absurd : true ≡ false → Rel C P (flat-exec-instr i P fs) (flat-exec-instr i E gs)
      absurd ()

  step-from-slot : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (load-from-slot k)
                 → LocState.faulted (floc (flat-exec-instr (load-from-slot k) P fs)) ≡ false
                 → Rel C P (flat-exec-instr (load-from-slot k) P fs) (flat-exec-instr (load-from-slot k) E gs)
  step-from-slot {fs} {gs} R k f nf =
    gated-step R (load-from-slot k) _ _ _ _ refl refl (cong (k Data.Nat.<ᵇ_) (r-slots R)) (go-al fs) (go-al gs)
      (L.Slots.from-slot (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) k (r-loc R))
      (λ q _ → load-slot-heap (LocState.stackMem (floc gs) (AllocState.current-frame (falloc gs)) k) (floc gs) (falloc gs) q)
      (next-pc R (load-from-slot k) f refl) nf
    where
      open import Once.CCC.Machine.SMCore using (module AbstractExec)
      load-slot-heap : ∀ mv (s : LocState FS) al q → LocState.heapMem (proj₁ (AbstractExec.exec-load-from-slot-with-value {FS} mv s al)) q ≡ LocState.heapMem s q
      load-slot-heap (just _) s al q = refl
      load-slot-heap nothing  s al q = refl
      slot-al : ∀ mv (s : LocState FS) al → proj₂ (AbstractExec.exec-load-from-slot-with-value {FS} mv s al) ≡ al
      slot-al (just _) s al = refl
      slot-al nothing  s al = refl
      go-al : ∀ x → straight-go (load-from-slot k) x ≡ record x { floc = floc (straight-go (load-from-slot k) x) ; fpc = suc (fpc x) }
      go-al x = cong (λ a → record x { floc = floc (straight-go (load-from-slot k) x) ; falloc = a ; fpc = suc (fpc x) })
                     (slot-al (LocState.stackMem (floc x) (AllocState.current-frame (falloc x)) k) (floc x) (falloc x))

  -- the slot instructions with a definite allocator, and the constants
  step-to-slot : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (store-at-slot k)
               → LocState.faulted (floc (flat-exec-instr (store-at-slot k) P fs)) ≡ false
               → Rel C P (flat-exec-instr (store-at-slot k) P fs) (flat-exec-instr (store-at-slot k) E gs)
  step-to-slot {fs} {gs} R k f nf =
    gated-step R (store-at-slot k) _ _ _ _ refl refl (cong (k Data.Nat.<ᵇ_) (r-slots R)) refl refl
      (L.Slots.to-slot (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) k (r-loc R))
      (λ q _ → refl) (next-pc R (store-at-slot k) f refl) nf

  step-lea : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (lea-slot k)
           → LocState.faulted (floc (flat-exec-instr (lea-slot k) P fs)) ≡ false
           → Rel C P (flat-exec-instr (lea-slot k) P fs) (flat-exec-instr (lea-slot k) E gs)
  step-lea {fs} {gs} R k f nf =
    gated-step R (lea-slot k) _ _ _ _ refl refl (cong (k Data.Nat.<ᵇ_) (r-slots R)) refl refl
      (L.Slots.lea (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) k (r-loc R))
      (λ q _ → refl) (next-pc R (lea-slot k) f refl) nf

  step-wl-push : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (worklist-push k)
               → LocState.faulted (floc (flat-exec-instr (worklist-push k) P fs)) ≡ false
               → Rel C P (flat-exec-instr (worklist-push k) P fs) (flat-exec-instr (worklist-push k) E gs)
  step-wl-push {fs} {gs} R k f nf =
    gated-step R (worklist-push k) _ _ _ _ refl refl (cong (k Data.Nat.<ᵇ_) (r-slots R)) refl refl
      (L.Rest.wl-push (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) k (r-loc R))
      (λ q _ → refl) (next-pc R (worklist-push k) f refl) nf

  step-tag : ∀ {fs gs} (R : Rel C P fs gs) n → fetch P (fpc fs) ≡ just (instr-load-tag-lit n)
           → Rel C P (flat-exec-instr (instr-load-tag-lit n) P fs) (flat-exec-instr (instr-load-tag-lit n) E gs)
  step-tag {fs} {gs} R n f =
    core-straight R _ _ (L.Rest.tag-lit (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) n (r-loc R))
      (λ q _ → refl) (next-pc R (instr-load-tag-lit n) f refl)

  step-code : ∀ {fs gs} (R : Rel C P fs gs) l → fetch P (fpc fs) ≡ just (instr-load-code-addr l)
            → Rel C P (flat-exec-instr (instr-load-code-addr l) P fs) (flat-exec-instr (instr-load-code-addr l) E gs)
  step-code {fs} {gs} R l f =
    core-straight R _ _ (L.Rest.code-addr (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) l (r-loc R))
      (λ q _ → refl) (next-pc R (instr-load-code-addr l) f refl)

  step-const : ∀ {fs gs} (R : Rel C P fs gs) {A} (p : Once.Type.FitsInReg A) v → fetch P (fpc fs) ≡ just (instr-load-const p v)
             → Rel C P (flat-exec-instr (instr-load-const p v) P fs) (flat-exec-instr (instr-load-const p v) E gs)
  step-const {fs} {gs} R p v f =
    core-straight R _ _ (L.Rest.load-const (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) p v (r-loc R))
      (λ q _ → refl) (next-pc R (instr-load-const p v) f refl)

  ------------------------------------------------------------------------
  -- The heap instructions
  ------------------------------------------------------------------------

  open ExecFinal {FS} using (frame-gate; heap-gate; live-frames; exec-load-at-resolved; exec-load-with-value
                            ; exec-store-at-resolved; exec-store-in-block; exec-addr-at-resolved; exec-addr-in-block; in-block?; live-size)
  open import Once.CCC.Codegen.AllocExpandRen {FS} using (rloc)
  open import Relation.Binary.PropositionalEquality using (cong₂; subst₂)

  -- the live frames are the same on both sides
  frames-eq : ∀ {fs gs} → Rel C P fs gs → live-frames (falloc gs) ≡ live-frames (falloc fs)
  frames-eq R = cong₂ _∷_ (cong₂ _,_ (r-frame R) (r-slots R)) (r-saved R)

  -- the expanded side's gate, by the primitive's
  gate-is : ∀ {fs gs} (R : Rel C P fs gs) k
          → frame-gate (falloc gs) k (sv-as-loc (readReg (LocState.regs (floc gs)) Input1))
            ≡ Data.Maybe.map (rloc (ρ R)) (frame-gate (falloc fs) k (sv-as-loc (readReg (LocState.regs (floc fs)) Input1)))
  gate-is {fs} {gs} R k =
    trans (cong (λ v → frame-gate (falloc gs) k (sv-as-loc v)) (L.LRel.l-regs (r-loc R) Input1))
      (trans (cong (frame-gate (falloc gs) k) (L.as-loc-rv (ρ R) (Live (falloc fs)) (r-inj R) (readReg (LocState.regs (floc fs)) Input1)))
             (L.frame-gate-rv (ρ R) (Live (falloc fs)) (r-inj R) (falloc fs) (falloc gs) k (frames-eq R)
                (sv-as-loc (readReg (LocState.regs (floc fs)) Input1))))

  -- a load leaves the heap
  la-heap : ∀ k ml (s : LocState FS) q → LocState.heapMem (exec-load-at-resolved k Output ml s) q ≡ LocState.heapMem s q
  la-heap k (just loc) s q = lv-heap (readLoc s (offsetLoc loc k))
    where
      open MemOps {FS} using (readLoc)
      lv-heap : ∀ mv → LocState.heapMem (exec-load-with-value Output mv s) q ≡ LocState.heapMem s q
      lv-heap (just _) = refl
      lv-heap nothing  = refl
  la-heap k nothing s q = refl

  step-load-at : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (load-at k)
               → LocState.faulted (floc (flat-exec-instr (load-at k) P fs)) ≡ false
               → Rel C P (flat-exec-instr (load-at k) P fs) (flat-exec-instr (load-at k) E gs)
  step-load-at {fs} {gs} R k f nf =
    core-straight R _ _
      (subst (λ m → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) (exec-load-at-resolved k Output ml (floc fs)) (exec-load-at-resolved k Output m (floc gs)))
             (sym (gate-is R k))
             (L.load-at-rel (ρ R) (Live (falloc fs)) (r-inj R) k ml (r-loc R) nf))
      (λ q _ → la-heap k (frame-gate (falloc gs) k (sv-as-loc (readReg (LocState.regs (floc gs)) Input1))) (floc gs) q) (next-pc R (load-at k) f refl)
    where
      ml = frame-gate (falloc fs) k (sv-as-loc (readReg (LocState.regs (floc fs)) Input1))

  -- the store gate passed: a live block, inside its renamed block too
  open import Data.Nat using (_<ᵇ_; _≤_; z≤n; s≤s)
  open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; <-≤-trans; ≤-trans; n≮0)
  open import Data.Empty using (⊥-elim)
  open import Data.Bool using (T)

  private
    T-of : ∀ {b : Bool} → b ≡ true → T b
    T-of refl = Data.Unit.tt
      where import Data.Unit
    of-T : ∀ {b : Bool} → T b → b ≡ true
    of-T {true} _ = refl

    -- the store gate's size of a freed block is 0
    live-free : ∀ (al : AllocState {FS}) r → AllocState.freed al r ≡ true → live-size al r ≡ 0
    live-free al r e = cong (λ b → Data.Bool.if b then 0 else AllocState.block-size al r) e
    live-kept : ∀ (al : AllocState {FS}) r → AllocState.freed al r ≡ false → live-size al r ≡ AllocState.block-size al r
    live-kept al r e = cong (λ b → Data.Bool.if b then 0 else AllocState.block-size al r) e

  ib-live : ∀ {fs gs} (R : Rel C P fs gs) hl → in-block? (live-size (falloc fs)) (AtDynamic hl) ≡ true → Live (falloc fs) (ref-of hl)
  ib-live {fs} R hl ib = below , unfreed (AllocState.freed (falloc fs) (ref-of hl)) refl
    where
      lt : HeapLocation.heap-offset hl < live-size (falloc fs) (ref-of hl)
      lt = <ᵇ⇒< _ _ (T-of ib)
      unfreed : ∀ b → AllocState.freed (falloc fs) (ref-of hl) ≡ b → AllocState.freed (falloc fs) (ref-of hl) ≡ false
      unfreed false e = e
      unfreed true  e = ⊥-elim (n≮0 (subst (HeapLocation.heap-offset hl <_) (live-free (falloc fs) (ref-of hl) e) lt))
      below : ref-of hl < AllocState.next-heap-ref (falloc fs)
      below = Data.Nat.Properties.≰⇒> λ ge → n≮0 (subst (HeapLocation.heap-offset hl <_)
                (trans (live-kept (falloc fs) (ref-of hl) (unfreed (AllocState.freed (falloc fs) (ref-of hl)) refl)) (r-unsized R (ref-of hl) ge)) lt)

  ib-mono : ∀ {fs gs} (R : Rel C P fs gs) hl → in-block? (live-size (falloc fs)) (AtDynamic hl) ≡ true
          → in-block? (live-size (falloc gs)) (AtDynamic (rhl (ρ R) hl)) ≡ true
  ib-mono {fs} {gs} R hl ib = of-T (<⇒<ᵇ (<-≤-trans lt sz))
    where
      lv = ib-live R hl ib
      lt : HeapLocation.heap-offset hl < AllocState.block-size (falloc fs) (ref-of hl)
      lt = subst (HeapLocation.heap-offset hl <_) (live-kept (falloc fs) (ref-of hl) (proj₂ lv)) (<ᵇ⇒< _ _ (T-of ib))
      sz : AllocState.block-size (falloc fs) (ref-of hl) ≤ live-size (falloc gs) (ρ R (ref-of hl))
      sz = subst (AllocState.block-size (falloc fs) (ref-of hl) ≤_) (sym (live-kept (falloc gs) (ρ R (ref-of hl)) (r-nofree R _)))
                 (r-size R (ref-of hl) (proj₁ lv))

  open import Once.CCC.Codegen.AllocExpandStep {FS} using (rhl-off; ref-off)
  open MemOps {FS} using (writeHeapMem; writeHeapMem-aux; writeLoc)
  open import Once.Memory.HeapAddress using (offsetHL; _≟HL_)

  -- the store's frame: the expanded write is at a live block's renamed cell
  store-frame : ∀ {fs gs} (R : Rel C P fs gs) k ml v w
              → LocState.faulted (exec-store-at-resolved (live-size (falloc fs)) k ml v (floc fs)) ≡ false
              → ∀ q → (∀ r → Live (falloc fs) r → ¬ ρ R r ≡ ref-of q)
              → LocState.heapMem (exec-store-at-resolved (live-size (falloc gs)) k (Data.Maybe.map (rloc (ρ R)) ml) w (floc gs)) q
                ≡ LocState.heapMem (floc gs) q
  store-frame R k nothing v w () q miss
  store-frame R k (just (AtStack f j)) v w nf q miss = refl
  store-frame {fs} {gs} R k (just (AtDynamic hl)) v w nf q miss =
    go (in-block? (live-size (falloc fs)) (AtDynamic (offsetHL hl k))) refl nf
       (in-block? (live-size (falloc gs)) (AtDynamic (offsetHL (rhl (ρ R) hl) k)))
    where
      go : ∀ b → in-block? (live-size (falloc fs)) (AtDynamic (offsetHL hl k)) ≡ b
         → LocState.faulted (exec-store-in-block b (AtDynamic (offsetHL hl k)) v (floc fs)) ≡ false
         → ∀ b′ → LocState.heapMem (exec-store-in-block b′ (AtDynamic (offsetHL (rhl (ρ R) hl) k)) w (floc gs)) q ≡ LocState.heapMem (floc gs) q
      go false _ () b′
      go true  e _ false = refl
      go true  e _ true  =
        trans (cong (λ s′ → LocState.heapMem s′ q) (L.dyn-write (ρ R) (Live (falloc fs)) (r-inj R) (floc gs) (offsetHL (rhl (ρ R) hl) k) w))
              (other (offsetHL (rhl (ρ R) hl) k ≟HL q))
        where
          lv : Live (falloc fs) (ref-of (offsetHL hl k))
          lv = ib-live R (offsetHL hl k) e
          other : ∀ (d : Relation.Nullary.Dec (offsetHL (rhl (ρ R) hl) k ≡ q))
                → writeHeapMem-aux {hl = offsetHL (rhl (ρ R) hl) k} {hl' = q} d (LocState.heapMem (floc gs) q) w ≡ LocState.heapMem (floc gs) q
          other (Relation.Nullary.yes eq) = ⊥-elim (miss (ref-of hl) (subst (Live (falloc fs)) (ref-off hl k) lv)
                                                     (trans (sym (ref-off (rhl (ρ R) hl) k)) (cong ref-of eq)))
          other (Relation.Nullary.no _)   = refl

  step-store-at : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (store-at k)
                → LocState.faulted (floc (flat-exec-instr (store-at k) P fs)) ≡ false
                → Rel C P (flat-exec-instr (store-at k) P fs) (flat-exec-instr (store-at k) E gs)
  step-store-at {fs} {gs} R k f nf =
    core-straight R _ _
      (subst₂ (λ m w → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) (exec-store-at-resolved (live-size (falloc fs)) k ml v (floc fs))
                                (exec-store-at-resolved (live-size (falloc gs)) k m w (floc gs)))
              (sym (gate-is R k)) (sym (L.LRel.l-regs (r-loc R) Output))
              (L.store-at-rel (ρ R) (Live (falloc fs)) (r-inj R) (live-size (falloc fs)) (live-size (falloc gs)) k ml v (r-loc R)
                 (ib-live R) (ib-mono R) nf))
      (λ q miss → trans (cong (λ m → LocState.heapMem (exec-store-at-resolved (live-size (falloc gs)) k m (readReg (LocState.regs (floc gs)) Output) (floc gs)) q) (gate-is R k))
                        (store-frame R k ml v (readReg (LocState.regs (floc gs)) Output) nf q miss))
      (next-pc R (store-at k) f refl)
    where
      ml = frame-gate (falloc fs) k (sv-as-loc (readReg (LocState.regs (floc fs)) Input1))
      v = readReg (LocState.regs (floc fs)) Output

  -- the address gate passed: a block handed out, inside its renamed block too
  ib-size : ∀ {fs gs} (R : Rel C P fs gs) hl → in-block? (AllocState.block-size (falloc fs)) (AtDynamic hl) ≡ true
          → in-block? (AllocState.block-size (falloc gs)) (AtDynamic (rhl (ρ R) hl)) ≡ true
  ib-size {fs} {gs} R hl ib = of-T (<⇒<ᵇ (<-≤-trans lt (r-size R (ref-of hl) below)))
    where
      lt : HeapLocation.heap-offset hl < AllocState.block-size (falloc fs) (ref-of hl)
      lt = <ᵇ⇒< _ _ (T-of ib)
      below : ref-of hl < AllocState.next-heap-ref (falloc fs)
      below = Data.Nat.Properties.≰⇒> λ ge → n≮0 (subst (HeapLocation.heap-offset hl <_) (r-unsized R (ref-of hl) ge) lt)

  aa-heap : ∀ bs k ml (s : LocState FS) q → LocState.heapMem (exec-addr-at-resolved bs k ml s) q ≡ LocState.heapMem s q
  aa-heap bs k (just loc) s q = ai (in-block? bs (offsetLoc loc k))
    where
      ai : ∀ b → LocState.heapMem (exec-addr-in-block b (offsetLoc loc k) s) q ≡ LocState.heapMem s q
      ai true  = refl
      ai false = refl
  aa-heap bs k nothing s q = refl

  -- the expanded side's address gate, by the primitive's
  hgate-is : ∀ {fs gs} (R : Rel C P fs gs)
           → heap-gate (sv-as-loc (readReg (LocState.regs (floc gs)) Input1))
             ≡ Data.Maybe.map (rloc (ρ R)) (heap-gate (sv-as-loc (readReg (LocState.regs (floc fs)) Input1)))
  hgate-is {fs} {gs} R =
    trans (cong (λ v → heap-gate (sv-as-loc v)) (L.LRel.l-regs (r-loc R) Input1))
      (trans (cong heap-gate (L.as-loc-rv (ρ R) (Live (falloc fs)) (r-inj R) (readReg (LocState.regs (floc fs)) Input1)))
             (L.heap-gate-rv (ρ R) (Live (falloc fs)) (r-inj R) (sv-as-loc (readReg (LocState.regs (floc fs)) Input1))))

  step-addr-at : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (addr-at k)
               → LocState.faulted (floc (flat-exec-instr (addr-at k) P fs)) ≡ false
               → Rel C P (flat-exec-instr (addr-at k) P fs) (flat-exec-instr (addr-at k) E gs)
  step-addr-at {fs} {gs} R k f nf =
    core-straight R _ _
      (subst (λ m → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) (exec-addr-at-resolved (AllocState.block-size (falloc fs)) k ml (floc fs))
                       (exec-addr-at-resolved (AllocState.block-size (falloc gs)) k m (floc gs)))
             (sym (hgate-is R))
             (L.addr-at-rel (ρ R) (Live (falloc fs)) (r-inj R) (AllocState.block-size (falloc fs)) (AllocState.block-size (falloc gs)) k ml (r-loc R)
                (ib-size R) nf))
      (λ q _ → aa-heap (AllocState.block-size (falloc gs)) k (heap-gate (sv-as-loc (readReg (LocState.regs (floc gs)) Input1))) (floc gs) q)
      (next-pc R (addr-at k) f refl)
    where
      ml = heap-gate (sv-as-loc (readReg (LocState.regs (floc fs)) Input1))

  -- the slot reads into Input1 / Output (their allocator is the state's own)
  private
    module AE = Once.CCC.Machine.SMCore.AbstractExec {FS}
    restore-al : ∀ mv (s : LocState FS) al → proj₂ (AE.exec-restore-input-with-value mv s al) ≡ al
    restore-al (just _) s al = refl
    restore-al nothing  s al = refl
    restore-heap : ∀ mv (s : LocState FS) al q → LocState.heapMem (proj₁ (AE.exec-restore-input-with-value mv s al)) q ≡ LocState.heapMem s q
    restore-heap (just _) s al q = refl
    restore-heap nothing  s al q = refl
    slot-al′ : ∀ mv (s : LocState FS) al → proj₂ (AE.exec-load-from-slot-with-value mv s al) ≡ al
    slot-al′ (just _) s al = refl
    slot-al′ nothing  s al = refl
    slot-heap′ : ∀ mv (s : LocState FS) al q → LocState.heapMem (proj₁ (AE.exec-load-from-slot-with-value mv s al)) q ≡ LocState.heapMem s q
    slot-heap′ (just _) s al q = refl
    slot-heap′ nothing  s al q = refl

  step-restore : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (restore-input k)
               → LocState.faulted (floc (flat-exec-instr (restore-input k) P fs)) ≡ false
               → Rel C P (flat-exec-instr (restore-input k) P fs) (flat-exec-instr (restore-input k) E gs)
  step-restore {fs} {gs} R k f nf =
    gated-step R (restore-input k) _ _ _ _ refl refl (cong (k Data.Nat.<ᵇ_) (r-slots R)) (go-al fs) (go-al gs)
      (L.Slots.restore (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) k (r-loc R))
      (λ q _ → restore-heap (LocState.stackMem (floc gs) (AllocState.current-frame (falloc gs)) k) (floc gs) (falloc gs) q)
      (next-pc R (restore-input k) f refl) nf
    where
      go-al : ∀ x → straight-go (restore-input k) x ≡ record x { floc = floc (straight-go (restore-input k) x) ; fpc = suc (fpc x) }
      go-al x = cong (λ a → record x { floc = floc (straight-go (restore-input k) x) ; falloc = a ; fpc = suc (fpc x) })
                     (restore-al (LocState.stackMem (floc x) (AllocState.current-frame (falloc x)) k) (floc x) (falloc x))

  step-wl-pop : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (worklist-pop k)
              → LocState.faulted (floc (flat-exec-instr (worklist-pop k) P fs)) ≡ false
              → Rel C P (flat-exec-instr (worklist-pop k) P fs) (flat-exec-instr (worklist-pop k) E gs)
  step-wl-pop {fs} {gs} R k f nf =
    gated-step R (worklist-pop k) _ _ _ _ refl refl (cong (k Data.Nat.<ᵇ_) (r-slots R)) (go-al fs) (go-al gs)
      (L.Rest.wl-pop (ρ R) (Live (falloc fs)) (r-inj R) {al = falloc fs} {al′ = falloc gs} (r-frame R) k (r-loc R))
      (λ q _ → slot-heap′ (LocState.stackMem (floc gs) (AllocState.current-frame (falloc gs)) k) (floc gs) (falloc gs) q)
      (next-pc R (worklist-pop k) f refl) nf
    where
      go-al : ∀ x → straight-go (worklist-pop k) x ≡ record x { floc = floc (straight-go (worklist-pop k) x) ; fpc = suc (fpc x) }
      go-al x = cong (λ a → record x { floc = floc (straight-go (worklist-pop k) x) ; falloc = a ; fpc = suc (fpc x) })
                     (slot-al′ (LocState.stackMem (floc x) (AllocState.current-frame (falloc x)) k) (floc x) (falloc x))

  -- the instructions that change nothing but the pc
  step-id : ∀ {fs gs} (R : Rel C P fs gs) i → fetch P (fpc fs) ≡ just i → expand-at C (fpc fs + 0) i ≡ i ∷ []
          → flat-exec-instr i P fs ≡ record fs { fpc = suc (fpc fs) } → flat-exec-instr i E gs ≡ record gs { fpc = suc (fpc gs) }
          → Rel C P (flat-exec-instr i P fs) (flat-exec-instr i E gs)
  step-id {fs} {gs} R i f ex eP eE =
    subst₂ (Rel C P) (sym eP) (sym eE) (core-straight R (floc fs) (floc gs) (r-loc R) (λ q _ → refl) (next-pc R i f ex))

  step-reclaim : ∀ {fs gs} (R : Rel C P fs gs) n → fetch P (fpc fs) ≡ just (instr-reclaim-to n)
               → Rel C P (flat-exec-instr (instr-reclaim-to n) P fs) (flat-exec-instr (instr-reclaim-to n) E gs)
  step-reclaim R n f = step-id R (instr-reclaim-to n) f refl refl refl

  step-wl-init : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (worklist-init k)
               → Rel C P (flat-exec-instr (worklist-init k) P fs) (flat-exec-instr (worklist-init k) E gs)
  step-wl-init R k f = step-id R (worklist-init k) f refl refl refl

  step-wl-check : ∀ {fs gs} (R : Rel C P fs gs) k → fetch P (fpc fs) ≡ just (worklist-check k)
                → Rel C P (flat-exec-instr (worklist-check k) P fs) (flat-exec-instr (worklist-check k) E gs)
  step-wl-check R k f = step-id R (worklist-check k) f refl refl refl

  ------------------------------------------------------------------------
  -- ★ The general step: new states whose control is mapped, frames equal,
  -- heap counters and sizes unchanged
  ------------------------------------------------------------------------

  open import Once.CCC.Codegen.AllocExpandStep {FS} using (lrel-conv)

  record Moves (fs gs fs′ gs′ : FlatState) : Set where
    field
      m-pc    : fpc gs′ ≡ off C 0 P (fpc fs′)
      m-ret   : fret gs′ ≡ map (off C 0 P) (fret fs′)
      m-link  : flink gs′ ≡ Data.Maybe.map (off C 0 P) (flink fs′)
      m-frame : AllocState.current-frame (falloc gs′) ≡ AllocState.current-frame (falloc fs′)
      m-saved : AllocState.saved-frames (falloc gs′) ≡ AllocState.saved-frames (falloc fs′)
      m-slots : AllocState.frame-slots (falloc gs′) ≡ AllocState.frame-slots (falloc fs′)
      m-nslot : AllocState.next-slot (falloc gs′) ≡ AllocState.next-slot (falloc fs′)
      -- the heaps' counters, sizes and frees as they were
      m-nextP : AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs)
      m-freeP : ∀ r → AllocState.freed (falloc fs′) r ≡ AllocState.freed (falloc fs) r
      m-sizeP : ∀ r → AllocState.block-size (falloc fs′) r ≡ AllocState.block-size (falloc fs) r
      m-nextE : AllocState.next-heap-ref (falloc gs′) ≡ AllocState.next-heap-ref (falloc gs)
      m-freeE : ∀ r → AllocState.freed (falloc gs′) r ≡ AllocState.freed (falloc gs) r
      m-sizeE : ∀ r → AllocState.block-size (falloc gs′) r ≡ AllocState.block-size (falloc gs) r
  open Moves

  core-gen : ∀ {fs gs fs′ gs′} (R : Rel C P fs gs) → Moves fs gs fs′ gs′
           → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) (floc fs′) (floc gs′)
           → fclosure gs′ ≡ rv (ρ R) (fclosure fs′)
           → (∀ q → (∀ r → Live (falloc fs) r → ¬ ρ R r ≡ ref-of q) → LocState.heapMem (floc gs′) q ≡ LocState.heapMem (floc gs) q)
           → Rel C P fs′ gs′
  core-gen {fs} {gs} {fs′} {gs′} R M LR clo frame = record
    { ρ = ρ R ; σ = σ R ; lists = lists R
    ; r-pc = m-pc M ; r-ret = m-ret M ; r-link = m-link M
    ; r-frame = m-frame M ; r-saved = m-saved M ; r-slots = m-slots M ; r-next-slot = m-nslot M
    ; r-inj = λ r r′ l l′ → r-inj R r r′ (to r l) (to r′ l′)
    ; r-loc = lrel-conv to fro LR
    ; r-clo = clo
    ; r-size = λ r lt → subst₂ _≤_ (sym (m-sizeP M r)) (sym (m-sizeE M (ρ R r))) (r-size R r (subst (r <_) (m-nextP M) lt))
    ; r-below = λ r l → let b = r-below R r (to r l) in proj₁ b , subst (ρ R r <_) (sym (m-nextE M)) (proj₂ b)
    ; r-not-σ = λ r l → r-not-σ R r (to r l)
    ; r-not-free = λ r c b l → r-not-free R r c b (to r l)
    ; r-heads = heads′
    ; r-sent = trans (frame (heap-loc (mkHeapRef (σ R)) 0) (λ r lv e → r-not-σ R r lv e)) (r-sent R)
    ; r-nofree = λ r → trans (m-freeE M r) (r-nofree R r)
    ; r-unsized = λ r le → trans (m-sizeP M r) (r-unsized R r (subst (_≤ r) (m-nextP M) le)) }
    where
      to : ∀ r → Live (falloc fs′) r → Live (falloc fs) r
      to r (lt , fr) = subst (r <_) (m-nextP M) lt , trans (sym (m-freeP M r)) fr
      fro : ∀ r → Live (falloc fs) r → Live (falloc fs′) r
      fro r (lt , fr) = subst (r <_) (sym (m-nextP M)) lt , trans (m-freeP M r) fr
      rec-free : ∀ k → LocState.heapMem (floc gs′) (rec-loc k) ≡ LocState.heapMem (floc gs) (rec-loc k)
      rec-free k = frame (rec-loc k) (λ r lv e → Data.Nat.Properties.<-irrefl (sym e) (proj₁ (r-below R r lv)))
      heads′ : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem (floc gs′) (rec-loc (head-word c)) ≡ just v
                                                         × Chain (LocState.heapMem (floc gs′)) (σ R) (lists R c) v
      heads′ c c< = hd (r-heads R c c<)
        where
          hd : (Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v)
             → Σ (StoredValue FS) λ v → LocState.heapMem (floc gs′) (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem (floc gs′)) (σ R) (lists R c) v
          hd (v , e , ch) = v , trans (rec-free (head-word c)) e
                          , chain-frame (LocState.heapMem (floc gs)) (LocState.heapMem (floc gs′)) (σ R) (lists R c) v
                              (λ b m → frame (heap-loc (mkHeapRef b) 0) (λ r lv e′ → r-not-free R r c b lv m e′)) ch
