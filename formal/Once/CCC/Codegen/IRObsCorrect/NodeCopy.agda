-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.NodeCopy   (D398, plan 0.123 β1)
--
-- A FLAT VALUE COPIED INTO A FRESH NODE. `IRToTrace.node-copy-trace L n`:
--
--   mov-to-output ; store-at-slot n            -- the value's address, stashed
--   instr-alloc-heap (2 ⊔ size L) ; store-at-slot (suc n)
--   put L n (suc n) 0                          -- its words, from word 0
--   load-from-slot (suc n)                     -- the node, the result
--
-- `Run` states the segment's effect (`exec-trace`): the node's word 0 holds
-- the value (`FlatPut`), and nothing the caller had live is written. It is
-- `Inj.Run` without the tag and the padding.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.NodeCopy (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; Input1; Output; SV-Ptr; StoredValue;
         mov-to-output; store-at-slot; load-from-slot; instr-alloc-heap; restore-input; load-at; store-at)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref)
open import Once.Memory.HeapAddress using (HeapRef; HeapLocation; heap-loc)
open import Once.IRTy using (IRTy)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (put; put-All)
open import Once.CCC.Codegen.IRToTrace o using (node-copy-trace)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc

open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m; m≤m⊔n)
open import Data.List.Relation.Unary.All using ([]; _∷_)

module NodeCopyC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc; writeLoc-read-same-stack; writeLoc-preserves-other)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons)
  open import Once.CCC.Machine.SMPrimitives using (module TraceComposition)
  open TraceComposition {FS} using (exec-trace-append)

  module Run {prog : AbstractTrace} (L : IRTy) (n : ℕ)
             (s : LocState FS) (alloc : AllocState {FS})
             (h : halted s ≡ false) where

    open FlatPut {FS} {prog} using (Src; src-tr; put-run; PutOut; dst)

    N  = 2 ⊔ size L
    rd = FlatAlloc.fresh-ref {FS} alloc
    A₁ = FlatAlloc.alloc-after {FS} N alloc
    Nd : ValueLocation FS
    Nd = AtDynamic (heap-loc rd 0)
    blk : StoredValue FS
    blk = SV-Ptr Nd
    cf = current-frame alloc
    w  = readReg (regs s) Input1

    s₁ = proj₁ (exec-abstract mov-to-output s alloc)
    s₂ = proj₁ (exec-abstract (store-at-slot n) s₁ alloc)
    s₃ = proj₁ (exec-abstract (instr-alloc-heap N) s₂ alloc)
    s₄ = proj₁ (exec-abstract (store-at-slot (suc n)) s₃ A₁)

    R = put L n (suc n) 0 ++ load-from-slot (suc n) ∷ []

    pre : exec-trace (node-copy-trace L n) s alloc ≡ exec-trace R s₄ A₁
    pre =
      trans (exec-trace-cons mov-to-output _ s alloc h)
     (trans (exec-trace-cons (store-at-slot n) _ s₁ alloc h)
     (trans (exec-trace-cons (instr-alloc-heap N) _ s₂ alloc h)
            (exec-trace-cons (store-at-slot (suc n)) _ s₃ A₁ h)))

    -- the stash slots
    slot-n₄ : readLoc s₄ (AtStack cf n) ≡ just w
    slot-n₄ =
      trans (writeLoc-preserves-other s₃ (AtStack cf (suc n)) (AtStack cf n) (readReg (regs s₃) Output)
               (λ e → <-irrefl (sym (cong slot-of e)) (n<1+n n)))
            (writeLoc-read-same-stack s₁ cf n (readReg (regs s₁) Output))
      where
        slot-of : ValueLocation FS → ℕ
        slot-of (AtStack _ k) = k
        slot-of (AtDynamic _) = 0

    slot-b₄ : readLoc s₄ (AtStack cf (suc n)) ≡ just blk
    slot-b₄ = writeLoc-read-same-stack s₃ cf (suc n) (readReg (regs s₃) Output)

    -- what the caller has live is not in the fresh block
    fresh : ∀ o → Live alloc (AtDynamic (heap-loc rd o)) → ⊥
    fresh o = FlatAlloc.alloc-fresh {FS} alloc o

    not-rd : ∀ hl → Live alloc (AtDynamic hl) → ∀ o → AtDynamic {FS} hl ≢ AtDynamic (heap-loc rd o)
    not-rd hl lv o e = fresh o (subst (Live alloc) e lv)

    keep₄ : ∀ l → Live alloc l → readLoc s₄ l ≡ readLoc s l
    keep₄ (AtDynamic hl) lv = refl

    module _ {x : ⟦ L ⟧} (src : Src alloc s L x w) where
      Pt = put-run L n (suc n) 0 s₄ A₁ alloc w rd N h slot-n₄ slot-b₄
             (FlatAlloc.alloc-bft {FS} N alloc) (FlatAlloc.alloc-bk {FS} N alloc) fresh
             (FlatAlloc.alloc-live {FS} N alloc) (m≤n⊔m 2 (size L)) (FlatAlloc.alloc-in {FS} N alloc)
             (src-tr keep₄ src)
      sp = proj₁ (exec-trace (put L n (suc n) 0) s₄ A₁)
      module Pt = PutOut Pt

      -- the last row: the node is the result
      sfin = record sp { regs = writeReg (regs sp) Output blk }

      slot-bp : readLoc sp (AtStack cf (suc n)) ≡ just blk
      slot-bp = trans (Pt.other (AtStack cf (suc n)) (λ j _ ())) slot-b₄

      last : exec-trace (load-from-slot (suc n) ∷ []) sp A₁ ≡ (sfin , A₁)
      last = trans (exec-trace-cons (load-from-slot (suc n)) [] sp A₁ Pt.live)
                   (cong (λ mv → AbstractExec.exec-load-from-slot-with-value {FS} mv sp A₁) slot-bp)

      whole : exec-trace (node-copy-trace L n) s alloc ≡ (sfin , A₁)
      whole =
        trans pre
       (trans (exec-trace-append (put L n (suc n) 0) (load-from-slot (suc n) ∷ []) s₄ A₁)
       (trans (cong (λ a → exec-trace (load-from-slot (suc n) ∷ []) sp a) Pt.alloc-eq)
              last))

      hfin : halted sfin ≡ false
      hfin = Pt.live

      cell-p : CellAt {prog = prog} A₁ L x Nd sp
      cell-p = Pt.cell

      live-Nd : Live A₁ Nd
      live-Nd = FlatAlloc.alloc-live {FS} N alloc 0

      -- what the run leaves alone: the caller's slots below `n`, its heap
      B = record alloc { next-slot = n }

      keep-bf : ∀ l → BeforeFrontier B l → readLoc sfin l ≡ readLoc s l
      keep-bf (AtDynamic hl) (BeforeFrontier.heap-before p) =
        Pt.other (AtDynamic hl) (λ j _ e → not-rd hl (BeforeFrontier.heap-before p) _ e)
      keep-bf (AtStack fr j) bf =
        trans (Pt.other (AtStack fr j) (λ j _ ()))
       (trans (store-slot-preserves-before (suc n) s₃ B A₁ (AtStack fr j) refl (n≤1+n n) bf)
              (store-slot-preserves-before n s₁ B alloc (AtStack fr j) refl ≤-refl bf))

      bf-mono′ : ∀ m loc → BeforeFrontier (record alloc { next-slot = m }) loc
               → BeforeFrontier (record A₁ { next-slot = m }) loc
      bf-mono′ m _ (BeforeFrontier.stack-before e j<) = BeforeFrontier.stack-before e j<
      bf-mono′ m _ (BeforeFrontier.stack-ancestor a src′) = BeforeFrontier.stack-ancestor a src′
      bf-mono′ m _ (BeforeFrontier.heap-before p) = BeforeFrontier.heap-before (<-trans p (n<1+n _))

  ------------------------------------------------------------------------
  -- The segment is straight, and silent.
  ------------------------------------------------------------------------
  node-copy-straight : ∀ L n → All StraightStep (node-copy-trace L n)
  node-copy-straight L n =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    ++⁺ (put-All {StraightStep} L n (suc n) 0 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
        ((λ _ _ → refl) ∷ [])

  node-copy-silent : ∀ L n → All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (node-copy-trace L n)
  node-copy-silent L n =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} L n (suc n) 0 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
        ((λ _ → refl) ∷ [])
