-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.SigOpFrame  (plan 0.123 α′ (e))
--
-- WHAT AN ARITH SIGOP'S RUN MUST DO, arch-free. The abstract step writes the
-- SigOp's result to `Output` and changes nothing else a correspondence reads
-- (`exec-abstract (instr-sigop si)`: alloc, memory, `Input1`, the frames and the
-- link all stand). The concrete run — the block's subroutine (D388) — may write
-- its result to the out register, and memory only inside its own frame
-- `[sp − W, sp)` below the stack pointer. With the room `hfront + W ≤ sp` the
-- room check guarantees (D387), that frame is above every live heap cell and
-- below every live frame, so the whole compiled correspondence carries over.
--
-- The arch owes `ArithRun` of its dispatch (its registers, its frame) and the
-- value (`ar-out`, the block's meaning); everything else is here, once.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; NonZero)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open FrameSemantics using (frame-word)
open import Once.Adequacy.ArchCorrectness.FlatCore.RegRoles using (RegRoles; Role; role-sp; role-clos; role-heap; role-out; role-in1)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (Label)
open import Once.Spec.Name using (CanonicalName)

module Once.Adequacy.ArchCorrectness.FlatCore.SigOpFrame
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
  (link-claim : State → ℕ → ℕ → Set)
  (xpc : State → ℕ)
  (Program : Set)
  (compile-trace : AbstractTrace → Program)
  (find-label : Program → Label → Maybe ℕ)
  (blk-off : AbstractTrace → ℕ → ℕ)
  (blk-len : AbstractInstr → ℕ)
  (exec : ℕ → Program → State → Maybe State)
  (modulus : ℕ)
  where

open import Data.Nat using (suc; _+_; _∸_; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; m≤m+n; m+n≤o⇒m≤o∸n; ≤-reflexive)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; subst)
open import Once.SigOp.Info using (SigOpInfo)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; fpc; fret; falloc; fclosure; flink; floc; flat-exec-instr; fetch)
open AbstractExec {FS} using (exec-sigop-output; exec-sigop-halts; decode-at)
open AllocState using (current-frame; frame-slots; saved-frames)
open LocState using (regs; halted; heapMem; stackMem)
open FrameSemantics FS using (Frame; frame-base)
open RegRoles roles using (reg-of; sp-reg; clos-reg; heap-reg; out-reg; in1-reg)

import Once.Adequacy.ArchCorrectness.FlatCore.FlatCorrespondence as FC
import Once.Adequacy.ArchCorrectness.FlatCore.CompiledCorrespondence as CC
import Once.Adequacy.ArchCorrectness.FlatCore.RunLow as RL
open import Once.SigOp.Info using (effect; Pure; Internal; internal-pure; module SigOpInfo)
open SigOpInfo using (baseA; sem)
open import Data.Bool using (false)
open import Data.Product using (∃)
private
  module CFC = FC FS slot-size word-eq Reg roles State rreg memory xhalted
  module CCC = CC o FS slot-size word-eq Reg roles State rreg memory xhalted link-claim
                 xpc Program compile-trace find-label blk-off blk-len exec modulus
open CFC using (HeapView; FlatCorr; Memory; readMem; StackWindows; RetAddrs; GapNext; frames-of
               ; hfront; lo; amap; haddr; dom-below; front-lo; enc-sv; slots
               ; windows-above; windows-reanchor; windows-lower)
open CCC using (CompiledCorr; dataCorr; pc-off; ret-eq; code-eq)

------------------------------------------------------------------------
-- The concrete run, as seen from the correspondence. `W` is the frame's size
-- in BYTES below the caller's stack pointer.
------------------------------------------------------------------------
record ArithRun (s s′ : State) (W : ℕ) (v : ℕ) : Set where
  field
    ar-out  : rreg s′ out-reg ≡ v
    ar-role : ∀ ρ → ¬ (ρ ≡ role-out) → rreg s′ (reg-of ρ) ≡ rreg s (reg-of ρ)
    ar-mem  : ∀ a → (a < rreg s sp-reg ∸ W) ⊎ (rreg s sp-reg ≤ a)
            → readMem (memory s′) a ≡ readMem (memory s) a
    ar-halt : xhalted s′ ≡ xhalted s
open ArithRun

------------------------------------------------------------------------
-- The pending returns ride across a memory that agrees above the floor, when
-- no link is pending (`ret-agree-above` without its head premise, which the
-- `nothing` row never reads).
------------------------------------------------------------------------
private
  ret-keep : ∀ (xoff : ℕ → ℕ) {am : CFC.AddrMap} (mem mem′ : Memory)
               (LK LK′ : ℕ → ℕ → Set) (stk : StackMem FS)
               (fl : ℕ) (fr : List (Frame × ℕ)) (rs : List ℕ)
           → (∀ (a : ℕ) → fl ≤ a → readMem mem′ a ≡ readMem mem a)
           → StackWindows am mem stk fl fr
           → RetAddrs xoff mem LK nothing fr rs → RetAddrs xoff mem′ LK′ nothing fr rs
  ret-keep xoff mem mem′ LK LK′ stk fl fr             []       ag sw r = _
  ret-keep xoff mem mem′ LK LK′ stk fl []             (x ∷ rs) ag sw ()
  ret-keep xoff mem mem′ LK LK′ stk fl ((f , b) ∷ fr) (x ∷ rs) ag (bd , win , rest) (h , g , t) =
    trans (ag (frame-base f + slots b) up) h
    , g
    , ret-keep xoff mem mem′ LK LK′ stk (frame-base f + slots b) fr rs
        (λ a le → ag a (≤-trans up le)) rest t
    where up = ≤-trans bd (m≤m+n (frame-base f) (slots b))

------------------------------------------------------------------------
-- THE FRAME LEMMA.
------------------------------------------------------------------------
sigop-arith-corr : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s s′ : State)
                     {A B} (si : SigOpInfo A B) {W v : ℕ}
                 → CompiledCorr hv prog fs s
                 → hfront hv + W ≤ rreg s sp-reg
                 → flink fs ≡ nothing
                 → ArithRun s s′ W v
                 → v ≡ enc-sv hv (exec-sigop-output si (floc fs))
                 → exec-sigop-halts si (floc fs) ≡ halted (floc fs)
                 → xpc s′ ≡ blk-off prog (suc (fpc fs))
                 → CompiledCorr hv prog (flat-exec-instr (instr-sigop si) prog fs) s′
sigop-arith-corr {hv} prog fs s s′ si {W} {v} cc room lk ar val hl pc′ = record
  { dataCorr = record
      { in1-eq      = trans (ar-role ar role-in1 (λ ())) (CFC.in1-eq corr)
      ; out-eq      = trans (ar-out ar) val
      ; clos-eq     = trans (ar-role ar role-clos (λ ())) (CFC.clos-eq corr)
      ; halt-eq     = trans (ar-halt ar) (trans (CFC.halt-eq corr) (sym hl))
      ; sp-eq       = trans (ar-role ar role-sp (λ ())) (CFC.sp-eq corr)
      ; frontier-eq = trans (ar-role ar role-heap (λ ())) (CFC.frontier-eq corr)
      ; dom-fresh   = CFC.dom-fresh corr
      ; dom-written = CFC.dom-written corr
      ; dom-sized   = CFC.dom-sized corr
      ; heap-eq     = λ hl′ d → trans (ar-mem ar (haddr hv hl′) (inj₁ (below hl′ d))) (CFC.heap-eq corr hl′ d)
      ; lo-le       = subst (lo hv ≤_) (sym (ar-role ar role-sp (λ ()))) (CFC.lo-le corr)
      ; stack-eq    = stack′
      }
  ; pc-off  = pc′
  ; ret-eq  = subst (λ l → RetAddrs (blk-off prog) (memory s′) (link-claim s′) l
                               (frames-of (falloc fs)) (fret fs)) (sym lk)
                (ret-keep (blk-off prog) (memory s) (memory s′) (link-claim s) (link-claim s′)
                   (stackMem (floc fs)) sp (frames-of (falloc fs)) (fret fs) above sw-sp
                   (subst (λ l → RetAddrs (blk-off prog) (memory s) (link-claim s) l
                                   (frames-of (falloc fs)) (fret fs)) lk (ret-eq cc)))
  ; code-eq = code-eq cc
  }
  where
    corr = dataCorr cc
    sp   = rreg s sp-reg
    -- every live heap cell is below the block's frame
    below : ∀ hl′ {w} → heapMem (floc fs) hl′ ≡ just w → haddr hv hl′ < sp ∸ W
    below hl′ d = <-≤-trans (dom-below hv (CFC.dom-written corr hl′ d))
                            (m+n≤o⇒m≤o∸n (hfront hv) room)
    above : ∀ a → sp ≤ a → readMem (memory s′) a ≡ readMem (memory s) a
    above a le = ar-mem ar a (inj₂ le)
    -- the windows, re-anchored at the stack pointer (the current frame's base)
    sw-sp : StackWindows (amap hv) (memory s) (stackMem (floc fs)) sp (frames-of (falloc fs))
    sw-sp = windows-reanchor (lo hv) sp (current-frame (falloc fs)) (frame-slots (falloc fs))
              (saved-frames (falloc fs)) (≤-reflexive (CFC.sp-eq corr)) (CFC.stack-eq corr)
    stack′ : StackWindows (amap hv) (memory s′) (stackMem (floc fs)) (lo hv) (frames-of (falloc fs))
    stack′ = windows-lower sp (lo hv) (frames-of (falloc fs)) (CFC.lo-le corr)
               (windows-above (memory s) (memory s′) (stackMem (floc fs)) (stackMem (floc fs)) sp
                  (frames-of (falloc fs)) above (λ _ _ _ → refl) sw-sp)

------------------------------------------------------------------------
-- …at a compiler-owned SigOp of a run. What the frame lemma asks of the
-- abstract side, the run supplies: no link is pending there (it is not an
-- entry), and its Pure argument decoded (D386), so it does not halt.
------------------------------------------------------------------------
private
  module CRL = RL o FS slot-size word-eq

sigop-halts-pure : ∀ {A B} (si : SigOpInfo A B) (ls : LocState FS)
                 → effect si ≡ Pure
                 → ∃ (λ a → decode-at (baseA si) (readReg (regs ls) Input1) ls ≡ just a)
                 → exec-sigop-halts si ls ≡ false
sigop-halts-pure si ls pe (a , d) rewrite pe | d = refl

sigop-arith-step : ∀ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s s′ : State)
                     {A B} (si : SigOpInfo A B) {W v : ℕ}
                 → CRL.RunLow prog fs → Internal (sem si)
                 → CompiledCorr hv prog fs s
                 → fetch prog (fpc fs) ≡ just (instr-sigop si)
                 → halted (floc fs) ≡ false
                 → hfront hv + W ≤ rreg s sp-reg
                 → ArithRun s s′ W v
                 → v ≡ enc-sv hv (exec-sigop-output si (floc fs))
                 → xpc s′ ≡ blk-off prog (suc (fpc fs))
                 → CompiledCorr hv prog (flat-exec-instr (instr-sigop si) prog fs) s′
sigop-arith-step prog fs s s′ si r int cc ftq h room ar val pc′ =
  sigop-arith-corr prog fs s s′ si cc room
    (CRL.run-link-nothing prog fs r ftq (λ _ ()) (λ ℓ bb fe → clash (trans (sym ftq) fe)))
    ar val
    (trans (sigop-halts-pure si (floc fs) (internal-pure int)
              (CRL.sigop-decodes prog fs si r h ftq (internal-pure int)))
           (sym h))
    pc′
  where
    clash : ∀ {ℓ bb} → just (instr-sigop si) ≡ just (instr-ctrl (c-entry ℓ bb)) → ⊥
    clash ()
