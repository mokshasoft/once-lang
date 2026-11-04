-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Id
--
-- plan 0.135 S3 / plan 0.123 α2: the re-suspension at a RECURSIVE POSITION
-- (`wf-Id`). Output holds a seed `a′`; the text builds a fresh suspension of
-- the seed pair `(e , a′)`:
--
--   store-at-slot n ; restore-input 0          -- stash a′; Input1 := the forced seed pair
--   get E 0                                     -- its environment `e`
--   store-at-slot (n+1) ; alloc (2 ⊔ |E*A|) ; store-at-slot (n+2)
--   put E (n+1) (n+2) 0 ; put A n (n+2) |E|     -- the pair (e , a′), flat, in a fresh block
--   alloc 2 ; store-at-slot (n+3) ; mov-to-input
--   load-from-slot (n+2) ; store-at 0           -- cell 0: the pair's pointer
--   load-code-addr lbl ; store-at 1             -- cell 1: this block's code
--   load-from-slot (n+3)                        -- Output: the suspension
--
-- Two straight segments around the read; the second is `Pair.Build`'s shape
-- (two `FlatPut` puts into one block) followed by the suspension's cells.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Id (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore using (ending)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; Output; Input1; SV-Ptr; SV-Code; StoredValue; sucLoc; offsetLoc; sv-as-loc;
         store-at-slot; load-from-slot; instr-alloc-heap; restore-input; store-at; mov-to-input; instr-load-code-addr)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref; saved-frames; block-size)
open import Once.Memory.HeapAddress using (heap-loc; HeapLocation)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Id) renaming (_*_ to _*ᵀ_)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (put; put-All; get; get-one)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)

open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; con; _:=_)

module ResuspIdC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack; writeLoc-regs; writeLoc-halted)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value; exec-restore-input-with-value)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; offset-zero; get-len)
  open ResuspBaseC {FS}
  module SR = StraightRunAPI {FS}

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    off-of : ValueLocation FS → ℕ
    off-of (AtDynamic (heap-loc _ o′)) = o′
    off-of (AtStack _ _) = 0

    -- two heap cells of different blocks are different cells
    ref-ne : ∀ {l₁ l₂ : ValueLocation FS} → loc-ref l₁ ≢ loc-ref l₂ → l₁ ≢ l₂
    ref-ne ne e = ne (cong loc-ref e)

  module RId {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
             (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
             (prog : AbstractTrace) (lbl-n : ℕ) (R : VTy (ν-type F))
             (mk-child : ∀ {alloc ν-loc s pl′} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                       → LocMatchesMode Heap ν-loc
                       → readLoc s ν-loc ≡ just (SV-Ptr pl′) → Live alloc pl′
                       → ValidAtWF {prog = prog} Heap alloc {E IRTy′.* A} (e , a′) pl′ s
                       → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                       → Live alloc (sucLoc ν-loc)
                       → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
             (R-tr : ∀ {a a′ : AllocState {FS}} {s s′ : LocState FS}
                   → (∀ l → Live a l → Live a′ l) → (∀ l → Live a l → readLoc s′ l ≡ readLoc s l)
                   → BlocksKept a a′
                   → ∀ {m v l} → R m a v l s → R m a′ v l s′)
             where

    open RBase wf coalg e prog lbl-n R mk-child R-tr
    open FlatPut {FS} {prog} using (Src; src-tr; put-run; PutOut; dst)

    lbl = ℓ o lbl-n

    T1 : ℕ → AbstractTrace
    T1 n = store-at-slot n ∷ restore-input 0 ∷ []

    SUS : ℕ → AbstractTrace
    SUS n = instr-alloc-heap 2 ∷ store-at-slot (suc (suc (suc n))) ∷ mov-to-input ∷ load-from-slot (suc (suc n)) ∷
            store-at 0 ∷ instr-load-code-addr lbl ∷ store-at 1 ∷ load-from-slot (suc (suc (suc n))) ∷ []

    T2 : ℕ → AbstractTrace
    T2 n = store-at-slot (suc n) ∷ instr-alloc-heap (2 ⊔ size (E *ᵀ A)) ∷ store-at-slot (suc (suc n)) ∷
           (put E (suc n) (suc (suc n)) 0 DL.++ put A n (suc (suc n)) (size E) DL.++ SUS n)

    text-eq : ∀ n l → rtrace wf-Id n l ≡ T1 n DL.++ get E 0 DL.++ T2 n
    text-eq n l = refl

    ------------------------------------------------------------------
    -- THE BUILD: from the read's end, the pair and the suspension
    ------------------------------------------------------------------
    module Build (n : ℕ) (gs : FlatState) (at : SR.At prog (fpc gs) (T2 n))
                 (h : halted (floc gs) ≡ false)
                 (b : AllocState {FS}) (bftb : ∀ l → Live b l → Live (falloc gs) l) (bkb : BlocksKept b (falloc gs))
                 {y : ValueDomain.⟦ A ⟧ᴰᴵ} (wA : StoredValue FS)
                 (srcA : Src b (floc gs) A y wA)
                 (rsA : readLoc (floc gs) (AtStack (current-frame (falloc gs)) n) ≡ just wA)
                 (srcE : Src (falloc gs) (floc gs) E e (readReg (regs (floc gs)) Output))
                 where

      s  = floc gs
      a  = falloc gs
      cf = current-frame a
      q  = suc (suc n)
      p  = suc q
      N  = 2 ⊔ size (E *ᵀ A)
      A₁ = FlatAlloc.alloc-after {FS} N a
      rd = FlatAlloc.fresh-ref {FS} a
      Q : ValueLocation FS
      Q  = AtDynamic (heap-loc rd 0)
      blk : StoredValue FS
      blk = SV-Ptr Q
      wE = readReg (regs s) Output

      t₁ = proj₁ (exec-abstract (store-at-slot (suc n)) s a)
      t₂ = proj₁ (exec-abstract (instr-alloc-heap N) t₁ a)
      t₃ = proj₁ (exec-abstract (store-at-slot q) t₂ A₁)

      R0 : AbstractTrace
      R0 = put E (suc n) q 0 DL.++ put A n q (size E) DL.++ SUS n

      prefix : exec-trace (T2 n) s a ≡ exec-trace R0 t₃ A₁
      prefix = trans (exec-trace-cons (store-at-slot (suc n)) _ s a h)
              (trans (exec-trace-cons (instr-alloc-heap N) _ t₁ a h)
                     (exec-trace-cons (store-at-slot q) R0 t₂ A₁ h))

      eSlot₃ : readLoc t₃ (AtStack cf (suc n)) ≡ just wE
      eSlot₃ = trans (writeLoc-preserves-other t₂ (AtStack cf q) (AtStack cf (suc n)) blk
                       (λ e′ → <-irrefl (sym (cong slot-of e′)) (n<1+n (suc n))))
                     (writeLoc-read-same-stack s cf (suc n) wE)

      aSlot₃ : readLoc t₃ (AtStack cf n) ≡ just wA
      aSlot₃ = trans (writeLoc-preserves-other t₂ (AtStack cf q) (AtStack cf n) blk
                       (λ e′ → <-irrefl (sym (cong slot-of e′)) (≤-trans (n<1+n n) (n≤1+n (suc n)))))
              (trans (writeLoc-preserves-other s (AtStack cf (suc n)) (AtStack cf n) wE
                       (λ e′ → <-irrefl (sym (cong slot-of e′)) (n<1+n n)))
                     rsA)

      qSlot₃ : readLoc t₃ (AtStack cf q) ≡ just blk
      qSlot₃ = writeLoc-read-same-stack t₂ cf q blk

      -- the stack writes leave the heap
      keep₃ : ∀ {a′ : AllocState {FS}} l → Live a′ l → readLoc t₃ l ≡ readLoc s l
      keep₃ (AtDynamic hl) _ = refl

      freshA : ∀ o → Live a (AtDynamic (heap-loc rd o)) → ⊥
      freshA o = FlatAlloc.alloc-fresh {FS} a o

      freshB : ∀ o → Live b (AtDynamic (heap-loc rd o)) → ⊥
      freshB o lv = freshA o (bftb _ lv)

      S≤N : size E + size A ≤ N
      S≤N = m≤n⊔m 2 (size E + size A)

      -- the two puts: the environment at word 0, the seed after it
      PE = put-run E (suc n) q 0 t₃ A₁ a wE rd N h eSlot₃ qSlot₃
             (FlatAlloc.alloc-bft {FS} N a) (FlatAlloc.alloc-bk {FS} N a) freshA (FlatAlloc.alloc-live {FS} N a)
             (≤-trans (m≤m+n (size E) (size A)) S≤N) (FlatAlloc.alloc-in {FS} N a) (src-tr (keep₃ {a}) srcE)
      module PE = PutOut PE
      sE = proj₁ (exec-trace (put E (suc n) q 0) t₃ A₁)

      keepE : ∀ l → Live a l → readLoc sE l ≡ readLoc t₃ l
      keepE (AtDynamic hl) lv = PE.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv))

      PA = put-run A n q (size E) sE A₁ b wA rd N PE.live
             (trans (PE.other (AtStack cf n) (λ j _ ())) aSlot₃)
             (trans (PE.other (AtStack cf q) (λ j _ ())) qSlot₃)
             (λ l lv → FlatAlloc.alloc-bft {FS} N a l (bftb l lv))
             (λ l lv ib → FlatAlloc.alloc-bk {FS} N a l (bftb l lv) (bkb l lv ib))
             freshB (FlatAlloc.alloc-live {FS} N a) S≤N (FlatAlloc.alloc-in {FS} N a)
             (src-tr (λ l lv → trans (keepE l (bftb l lv)) (keep₃ {b} l lv)) srcA)
      module PA = PutOut PA
      sA = proj₁ (exec-trace (put A n q (size E)) sE A₁)

      ------------------------------------------------------------------
      -- the suspension: a fresh two-cell block
      ------------------------------------------------------------------
      A₂ = FlatAlloc.alloc-after {FS} 2 A₁
      rd₂ = FlatAlloc.fresh-ref {FS} A₁
      V V1 : ValueLocation FS
      V  = AtDynamic (heap-loc rd₂ 0)
      V1 = AtDynamic (heap-loc rd₂ 1)
      sv : StoredValue FS
      sv = SV-Ptr V
      code : StoredValue FS
      code = SV-Code lbl

      u₁ = proj₁ (exec-abstract (instr-alloc-heap 2) sA A₁)
      u₂ = proj₁ (exec-abstract (store-at-slot p) u₁ A₂)
      u₃ = proj₁ (exec-abstract mov-to-input u₂ A₂)
      u₄ = record u₃ { regs = writeReg (regs u₃) Output blk }
      u₅ = writeLoc u₄ V blk
      u₆ = proj₁ (exec-abstract (instr-load-code-addr lbl) u₅ A₂)
      u₇ = writeLoc u₆ V1 code
      sfin = record u₇ { regs = writeReg (regs u₇) Output sv }

      hA : halted sA ≡ false
      hA = PA.live

      qSlotA : readLoc sA (AtStack cf q) ≡ just blk
      qSlotA = trans (PA.other (AtStack cf q) (λ j _ ())) (trans (PE.other (AtStack cf q) (λ j _ ())) qSlot₃)

      qSlotU₃ : readLoc u₃ (AtStack cf q) ≡ just blk
      qSlotU₃ = trans (writeLoc-preserves-other u₁ (AtStack cf p) (AtStack cf q) sv
                        (λ e′ → <-irrefl (sym (cong slot-of e′)) (n<1+n q)))
                      qSlotA

      pSlotU₇ : readLoc u₇ (AtStack cf p) ≡ just sv
      pSlotU₇ = trans (writeLoc-preserves-other u₆ V1 (AtStack cf p) code (λ ()))
               (trans (writeLoc-preserves-other u₄ V (AtStack cf p) blk (λ ()))
                      (writeLoc-read-same-stack u₁ cf p sv))

      ib₀ : InBlk A₂ V
      ib₀ = FlatAlloc.alloc-in {FS} 2 A₁ 0 (s≤s z≤n)
      ib₁ : InBlk A₂ V1
      ib₁ = FlatAlloc.alloc-in {FS} 2 A₁ 1 (s≤s (s≤s z≤n))

      h₅ : halted u₅ ≡ false
      h₅ = trans (writeLoc-halted u₄ V blk) hA
      h₇ : halted u₇ ≡ false
      h₇ = trans (writeLoc-halted u₆ V1 code) h₅

      in1₆ : readReg (regs u₆) Input1 ≡ sv
      in1₆ = cong (λ r → readReg r Input1) (writeLoc-regs u₄ V blk)

      ld₄ : exec-abstract (load-from-slot q) u₃ A₂ ≡ (u₄ , A₂)
      ld₄ = cong (λ mv → exec-load-from-slot-with-value mv u₃ A₂) qSlotU₃

      st₀ : exec-abstract (store-at 0) u₄ A₂ ≡ (u₅ , A₂)
      st₀ = cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb V blk u₄ , A₂)) ib₀

      st₁ : exec-abstract (store-at 1) u₆ A₂ ≡ (u₇ , A₂)
      st₁ = trans (cong (λ ml → (SMCore.ExecFinal.exec-store-at-resolved {FS} (block-size A₂) 1 ml code u₆ , A₂)) (cong sv-as-loc in1₆))
                  (cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb V1 code u₆ , A₂)) ib₁)

      ld₇ : exec-abstract (load-from-slot p) u₇ A₂ ≡ (sfin , A₂)
      ld₇ = cong (λ mv → exec-load-from-slot-with-value mv u₇ A₂) pSlotU₇

      sus-eq : exec-trace (SUS n) sA A₁ ≡ (sfin , A₂)
      sus-eq =
        trans (exec-trace-cons (instr-alloc-heap 2) _ sA A₁ hA)
       (trans (exec-trace-cons (store-at-slot p) _ u₁ A₂ hA)
       (trans (exec-trace-cons mov-to-input _ u₂ A₂ hA)
       (trans (exec-trace-cons (load-from-slot q) _ u₃ A₂ hA)
       (trans (cong (λ r → exec-trace (store-at 0 ∷ instr-load-code-addr lbl ∷ store-at 1 ∷ load-from-slot p ∷ []) (proj₁ r) (proj₂ r)) ld₄)
       (trans (exec-trace-cons (store-at 0) _ u₄ A₂ hA)
       (trans (cong (λ r → exec-trace (instr-load-code-addr lbl ∷ store-at 1 ∷ load-from-slot p ∷ []) (proj₁ r) (proj₂ r)) st₀)
       (trans (exec-trace-cons (instr-load-code-addr lbl) _ u₅ A₂ h₅)
       (trans (exec-trace-cons (store-at 1) _ u₆ A₂ h₅)
       (trans (cong (λ r → exec-trace (load-from-slot p ∷ []) (proj₁ r) (proj₂ r)) st₁)
       (trans (exec-trace-cons (load-from-slot p) [] u₇ A₂ h₇)
              (cong (λ r → exec-trace [] (proj₁ r) (proj₂ r)) ld₇)))))))))))

      whole : exec-trace (T2 n) s a ≡ (sfin , A₂)
      whole =
        trans prefix
       (trans (exec-trace-append (put E (suc n) q 0) (put A n q (size E) DL.++ SUS n) t₃ A₁)
       (trans (cong (λ x → exec-trace (put A n q (size E) DL.++ SUS n) sE x) PE.alloc-eq)
       (trans (exec-trace-append (put A n q (size E)) (SUS n) sE A₁)
       (trans (cong (λ x → exec-trace (SUS n) sA x) PA.alloc-eq)
              sus-eq))))

      hfin : halted sfin ≡ false
      hfin = h₇

      ------------------------------------------------------------------
      -- what the suspension's writes leave: every heap cell but its two
      ------------------------------------------------------------------
      sus-heap : ∀ hl → V ≢ AtDynamic hl → V1 ≢ AtDynamic hl → readLoc sfin (AtDynamic hl) ≡ readLoc sA (AtDynamic hl)
      sus-heap hl n0 n1 = trans (writeLoc-preserves-other u₆ V1 (AtDynamic hl) code n1)
                                (writeLoc-preserves-other u₄ V (AtDynamic hl) blk n0)

      -- no cell `A₁` holds is one of the suspension's
      notV : ∀ l → Live A₁ l → V ≢ l
      notV l lv e′ = FlatAlloc.alloc-fresh {FS} A₁ 0 (subst (Live A₁) (sym e′) lv)
      notV1 : ∀ l → Live A₁ l → V1 ≢ l
      notV1 l lv e′ = FlatAlloc.alloc-fresh {FS} A₁ 1 (subst (Live A₁) (sym e′) lv)

      -- what `a` held: unchanged from the build's start
      keepS : ∀ l → Live a l → readLoc sfin l ≡ readLoc t₃ l
      keepS (AtDynamic hl) lv =
        trans (sus-heap hl (notV _ lv₁) (notV1 _ lv₁))
       (trans (PA.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv)))
              (PE.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv))))
        where lv₁ = FlatAlloc.alloc-bft {FS} N a _ lv

      -- the pair `(e , a′)`, in its block at the end
      dstV : ∀ off j → V ≢ dst rd off j
      dstV off j = ref-ne (λ e′ → <-irrefl (sym e′) (n<1+n _))
      dstV1 : ∀ off j → V1 ≢ dst rd off j
      dstV1 off j = ref-ne (λ e′ → <-irrefl (sym e′) (n<1+n _))

      cellE : CellAt {prog = prog} A₁ E e Q sfin
      cellE = PE.cell-at sfin
                (λ j j< → trans (sus-heap _ (dstV 0 j) (dstV1 0 j))
                                (PA.other (dst rd 0 j) (λ j′ _ e′ → apart j j′ j< (cong off-of e′))))
                (λ l lv → keepS l lv)
        where
          apart : ∀ j j′ → j < size E → (0 + j) + 0 ≡ (size E + j′) + 0 → ⊥
          apart j j′ j< e′ =
            <-irrefl refl (<-≤-trans j< (≤-trans (m≤m+n (size E) j′)
              (≤-reflexive (sym (trans (sym (+-identityʳ j)) (trans e′ (+-identityʳ (size E + j′))))))))

      cellA : CellAt {prog = prog} A₁ A y (offsetLoc Q (size E)) sfin
      cellA = PA.cell-at sfin (λ j _ → sus-heap _ (dstV (size E) j) (dstV1 (size E) j))
                (λ { (AtDynamic hl) lv →
                       trans (sus-heap hl (notV _ (lvb₁ lv)) (notV1 _ (lvb₁ lv)))
                             (PA.other (AtDynamic hl) (λ j _ e′ → freshB _ (subst (Live b) e′ lv))) })
        where lvb₁ : ∀ {l} → Live b l → Live A₁ l
              lvb₁ lv = FlatAlloc.alloc-bft {FS} N a _ (bftb _ lv)

      valQ₁ : ValidAtWF {prog = prog} Heap A₁ {E *ᵀ A} (e , y) Q sfin
      valQ₁ = valid-pair-wf tt (FlatAlloc.alloc-live {FS} N a 1) cellE cellA

      lvQ : Live A₂ Q
      lvQ = FlatAlloc.alloc-bft {FS} 2 A₁ Q (FlatAlloc.alloc-live {FS} N a 0)

      valQ : ValidAtWF {prog = prog} Heap A₂ {E *ᵀ A} (e , y) Q sfin
      valQ = validityWF-heap-transport (Live A₁) (λ _ x → x) (λ _ _ → refl)
               (FlatAlloc.alloc-bft {FS} 2 A₁) (FlatAlloc.alloc-bk {FS} 2 A₁) (e , y) Q
               (FlatAlloc.alloc-live {FS} N a 0) valQ₁

      cell0 : readLoc sfin V ≡ just blk
      cell0 = trans (writeLoc-preserves-other u₆ V1 V code (λ e′ → <-irrefl (cong off-of (sym e′)) (s≤s z≤n)))
                    (readLoc-writeLoc-same u₄ V blk)

      cell1 : readLoc sfin V1 ≡ just code
      cell1 = readLoc-writeLoc-same u₆ V1 code

      lvV : Live A₂ V
      lvV = FlatAlloc.alloc-live {FS} 2 A₁ 0
      lvV1 : Live A₂ V1
      lvV1 = FlatAlloc.alloc-live {FS} 2 A₁ 1

      -- THE RESULT: a fresh suspension of `(e , a′)`, valid wherever what
      -- was live stays put
      rout : ROut IRTy′.Id Heap A₂ sfin (rsd wf-Id y)
      rout = ro-loc V lvV refl
               (λ {a′} {s′} bft bk keep →
                  mk-child y tt (trans (keep V lvV) cell0) (bft Q lvQ)
                    (validityWF-heap-transport (Live A₂) (λ _ x → x) keep bft bk (e , y) Q lvQ valQ)
                    (trans (keep V1 lvV1) cell1) (bft V1 lvV1))

      ------------------------------------------------------------------
      -- the chain
      ------------------------------------------------------------------
      settle : FlatState
      settle = record gs { floc = sfin ; falloc = A₂ ; fpc = DL.length (T2 n) + fpc gs }

      he : halted (proj₁ (exec-trace (T2 n) s a)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) whole) hfin

      sts : All StraightStep (T2 n)
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            ++⁺ (put-All {StraightStep} E (suc n) q 0 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                (++⁺ (put-All {StraightStep} A n q (size E) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                     ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
                      (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []))

      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (T2 n)
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} E (suc n) q 0 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} A n q (size E) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                     ((λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
                      (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []))

      run₀ = SR.straight-steps {prog} (T2 n) gs sts at h he

      eq : SR.after (T2 n) gs ≡ settle
      eq = cong (λ r → record gs { floc = proj₁ r ; falloc = proj₂ r ; fpc = DL.length (T2 n) + fpc gs }) whole

      run : FlatSteps prog (DL.length (T2 n)) gs settle
      run = subst (FlatSteps prog (DL.length (T2 n)) gs) eq run₀

      silent : chain-events run ≡ []
      silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} (T2 n) gs sts at h he evs)

      -- below the frontier `n` nothing moves
      below : ∀ loc → BeforeFrontier (record a { next-slot = n }) loc → readLoc sfin loc ≡ readLoc s loc
      below (AtDynamic hl) (BeforeFrontier.heap-before p′) =
        trans (keepS (AtDynamic hl) (BeforeFrontier.heap-before p′)) refl
      below (AtStack fr j) bf =
        trans (writeLoc-preserves-other u₆ V1 (AtStack fr j) code (λ ()))
       (trans (writeLoc-preserves-other u₄ V (AtStack fr j) blk (λ ()))
       (trans (store-slot-preserves-before p u₁ (record a { next-slot = n }) A₂ (AtStack fr j) refl
                 (≤-trans (n≤1+n n) (≤-trans (n≤1+n (suc n)) (n≤1+n q))) bf)
       (trans (PA.other (AtStack fr j) (λ _ _ ()))
       (trans (PE.other (AtStack fr j) (λ _ _ ()))
       (trans (store-slot-preserves-before q t₂ (record a { next-slot = n }) A₁ (AtStack fr j) refl
                 (≤-trans (n≤1+n n) (n≤1+n (suc n))) bf)
              (store-slot-preserves-before (suc n) s (record a { next-slot = n }) a (AtStack fr j) refl
                 (n≤1+n n) bf))))))

      bk : BlocksKept a A₂
      bk = bk-trans {a = a} {b = A₁} {c = A₂} (FlatAlloc.alloc-bk {FS} N a) (FlatAlloc.alloc-bk {FS} 2 A₁)
                    (FlatAlloc.alloc-bft {FS} N a)

      href : next-heap-ref a ≤ next-heap-ref A₂
      href = ≤-trans (n≤1+n _) (n≤1+n _)

    ------------------------------------------------------------------
    -- THE CASE
    ------------------------------------------------------------------
    resusp-Id : Resusp′ wf-Id
    resusp-Id n l σ y pl b hb bkb span lab nh lk ns n≥1 sl0 lpl cE oA = record
      { steps    = 2 + (1 + DL.length (T2 n))
      ; settle   = B.settle
      ; run      = run
      ; nh       = B.hfin
      ; pc       = sym (trans (cong (λ z → (2 + z) + fpc σ)
                                    (trans (length-++ (get E 0) {T2 n}) (cong (_+ DL.length (T2 n)) (get-len E 0))))
                              (arith (DL.length (T2 n)) (fpc σ)))
      ; ret      = refl
      ; lnk      = lk
      ; ev       = ev
      ; log      = trans (log-of run ev) (++-identityʳ _)
      ; left     = chain-left run B.hfin
      ; out-mode = Heap
      ; rout     = B.rout
      ; seg      = record { mem = λ loc bf → trans (B.below loc bf) (mem1 loc bf) ; cf = refl ; sf = refl ; ns = refl ; href = B.href }
      ; bk       = B.bk
      }
      where
        s  = floc σ
        a  = falloc σ
        cf = current-frame a
        wA = readReg (regs s) Output

        arith : ∀ t f → (2 + (1 + t)) + f ≡ t + suc (suc (suc f))
        arith = solve 2 (λ t f → (con 2 :+ (con 1 :+ t)) :+ f := t :+ (con 3 :+ f)) refl

        -- the stash and the seed pair's pointer
        s₁ = proj₁ (exec-abstract (store-at-slot n) s a)
        s₂ = record s₁ { regs = writeReg (regs s₁) Input1 (SV-Ptr pl) }

        r0 : readLoc s₁ (AtStack cf 0) ≡ just (SV-Ptr pl)
        r0 = trans (writeLoc-preserves-other s (AtStack cf n) (AtStack cf 0) wA
                     (λ e′ → <-irrefl (sym (cong slot-of e′)) n≥1))
                   sl0

        t1-eq : exec-trace (T1 n) s a ≡ (s₂ , a)
        t1-eq = trans (exec-trace-cons (store-at-slot n) _ s a nh)
               (trans (exec-trace-cons (restore-input 0) [] s₁ a nh)
                      (cong (λ mv → exec-trace [] (proj₁ (exec-restore-input-with-value mv s₁ a))
                                                  (proj₂ (exec-restore-input-with-value mv s₁ a))) r0))

        σ₁ : FlatState
        σ₁ = record σ { floc = s₂ ; falloc = a ; fpc = 2 + fpc σ }

        sts1 : All StraightStep (T1 n)
        sts1 = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
        evs1 : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (T1 n)
        evs1 = (λ _ → refl) ∷ (λ _ → refl) ∷ []

        at1 : SR.At prog (fpc σ) (T1 n)
        at1 = span-take prog (T1 n) {get E 0 DL.++ T2 n} (fpc σ) span

        he1 : halted (proj₁ (exec-trace (T1 n) s a)) ≡ false
        he1 = trans (cong (λ r → halted (proj₁ r)) t1-eq) nh

        run1₀ = SR.straight-steps {prog} (T1 n) σ sts1 at1 nh he1

        eq1 : SR.after (T1 n) σ ≡ σ₁
        eq1 = cong (λ r → record σ { floc = proj₁ r ; falloc = proj₂ r ; fpc = 2 + fpc σ }) t1-eq

        run1 : FlatSteps prog 2 σ σ₁
        run1 = subst (FlatSteps prog 2 σ) eq1 run1₀

        sil1 : chain-events run1 ≡ []
        sil1 = trans (chain-events-subst eq1 run1₀) (SR.straight-silent {prog} (T1 n) σ sts1 at1 nh he1 evs1)

        -- the environment, read
        sp2 : SpanAt prog (2 + fpc σ) (get E 0 DL.++ T2 n)
        sp2 = span-drop prog (T1 n) {get E 0 DL.++ T2 n} (fpc σ) span

        atG : ∀ i → fetch (get E 0) 0 ≡ just i → fetch prog (fpc σ₁) ≡ just i
        atG i e′ = sp2 0 i (fetch-++-left (get E 0) (T2 n) 0 i e′)

        cell1 : CellAt {prog = prog} a E e (offsetLoc pl 0) s₂
        cell1 = subst (λ z → CellAt {prog = prog} a E e z s₂) (sym (offset-zero pl))
                  (cellWF-heap-transport (Live b) (λ _ x → x) (λ { (AtDynamic hl) _ → refl })
                     (live-from b a hb) bkb e pl lpl cE)

        g : GetOut {prog = prog} E e σ₁
        g = get-run E 0 σ₁ pl nh atG refl (live-from b a hb pl lpl) cell1

        gs : FlatState
        gs = setOut σ₁ (GetOut.out g)

        -- the build
        sp3 : SR.At prog (fpc gs) (T2 n)
        sp3 = subst (λ z → SpanAt prog (z + (2 + fpc σ)) (T2 n)) (get-len E 0)
                    (span-drop prog (get E 0) {T2 n} (2 + fpc σ) sp2)

        srcA : Src b (floc gs) A y wA
        srcA = src-tr (λ { (AtDynamic hl) _ → refl }) (out→src oA)

        rsA : readLoc (floc gs) (AtStack cf n) ≡ just wA
        rsA = writeLoc-read-same-stack s cf n wA

        module B = Build n gs sp3 nh b (live-from b a hb) bkb wA srcA rsA (out→src (place→out (GetOut.place g)))

        run : FlatSteps prog (2 + (1 + DL.length (T2 n))) σ B.settle
        run = FlatSteps-++ run1 (FlatSteps-++ (GetOut.step g) B.run)

        ev : chain-events run ≡ []
        ev = trans (chain-events-++ run1 (FlatSteps-++ (GetOut.step g) B.run))
                   (cong₂ DL._++_ sil1 (trans (chain-events-++ (GetOut.step g) B.run)
                                              (cong₂ DL._++_ (GetOut.silent g) B.silent)))

        mem1 : ∀ loc → BeforeFrontier (record a { next-slot = n }) loc → readLoc (floc gs) loc ≡ readLoc s loc
        mem1 loc bf = trans (readLoc-stack-heap-eq (floc gs) s₁ loc refl refl)
                            (store-slot-preserves-before n s (record a { next-slot = n }) a loc refl ≤-refl bf)
