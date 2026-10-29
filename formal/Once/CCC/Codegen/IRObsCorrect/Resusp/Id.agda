-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Resusp.Id
--
-- plan 0.125 S3: THE RECURSIVE POSITION of the re-suspension
-- (`resuspend-layer … wf-Id`, nineteen straight rows). Output holds the
-- seed `a′`; the rows build the pair `(e , a′)` — its first cell copied
-- from the forced suspension's own seed pair (slot 0), its second the seed —
-- and then the two-cell suspension `[pair , code]` of this block, the same
-- nine-row heap build `TwoCell` runs (`NineStepPres`).
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Resusp.Id (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; StoredValue
        ; readReg; Output; Input1; SV-Code; SV-Ptr; sucLoc
        ; store-at-slot; restore-input; load-from-slot; load-indirect; store-indirect
        ; store-indirect-suc; mov-to-input; instr-alloc-heap; instr-load-code-addr; sv-as-loc)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)
open import Once.CCC.Label using (ℓ; LabelId)
open import Once.IRTy using (IRTy; IRFunctor; WellFormedFI; ⟦_⟧TI; ν-type; wf-Id)
import Once.IRTy as IRTy′
import Once.Denotation.ValueDomain as ValueDomain
open import Once.CCC.Machine.SMPrimitives using (nhw-store-at-slot; nhw-restore-input)
open import Once.CCC.Machine.FrameFree using (exec-abstract-preserves-next-slot)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL)
open import Data.Nat using (z≤n; s≤s)
open import Data.Sum using (inj₁; inj₂)

module ResuspIdC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)

  cfx : ∀ i (t : FlatState) → current-frame (falloc (St i t)) ≡ current-frame (falloc t)
  cfx i t = exec-abstract-preserves-frame i (floc t) (falloc t)

  sfx : ∀ i (t : FlatState) → saved-frames (falloc (St i t)) ≡ saved-frames (falloc t)
  sfx i t = exec-abstract-preserves-saved i (floc t) (falloc t)

  module RId {F : IRFunctor} (wf : WellFormedFI F) {E A : IRTy}
             (coalg : IR (E IRTy′.* A) (⟦ F ⟧TI A)) (e : ValueDomain.⟦ E ⟧ᴰᴵ)
             (prog : AbstractTrace) (lbl-n : ℕ)
             (R : VTy (ν-type F))
             (mk-child : ∀ {alloc ν-loc s} (a′ : ValueDomain.⟦ A ⟧ᴰᴵ)
                       → LocMatchesMode Heap ν-loc
                       → readLoc s (sucLoc ν-loc) ≡ just (SV-Code (ℓ o lbl-n))
                       → Live alloc (sucLoc ν-loc)
                       → CellAt {prog = prog} alloc (E IRTy′.* A) (e , a′) ν-loc s
                       → R Heap alloc (retVal (evalᴰ (Ana wf coalg) (e , a′))) ν-loc s)
             where

    open RBase wf coalg e prog lbl-n R mk-child

    module Run (n l : ℕ) (σ : FlatState) (y : ValueDomain.⟦ A ⟧ᴰᴵ) (pl : ValueLocation FS)
               (span : SpanAt prog (fpc σ) (rtrace wf-Id n l))
               (nh0 : halted (floc σ) ≡ false) (lk : flink σ ≡ nothing)
               (ns0 : next-slot (falloc σ) ≡ 0) (n≥1 : 1 ≤ n)
               (sl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) 0) ≡ just (SV-Ptr pl))
               (b : AllocState {FS}) (hb : next-heap-ref b ≤ next-heap-ref (falloc σ))
               (lpl : Live b pl)
               (cE : CellAt {prog = prog} b E e pl (floc σ))
               (oA : OutAt′ {A} b y (floc σ))
               where

      s₀ : LocState FS
      s₀ = floc σ
      a₀ : AllocState {FS}
      a₀ = falloc σ
      f₀ = current-frame a₀
      N : ℕ
      N = suc (suc n)
      lbl : LabelId
      lbl = ℓ o lbl-n

      qhl : HeapLocation
      qhl = heap-loc (mkHeapRef (next-heap-ref a₀)) 0

      av ec : StoredValue FS
      av = readReg (regs s₀) Output
      ec = cell-sv cE

      t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 : FlatState
      t1  = St (store-at-slot n) σ
      t2  = St (instr-alloc-heap 2) t1
      t3  = St (store-at-slot (suc n)) t2
      t4  = St (restore-input 0) t3
      t5  = St load-indirect t4
      t6  = St (restore-input (suc n)) t5
      t7  = St store-indirect t6
      t8  = St (load-from-slot n) t7
      t9  = St store-indirect-suc t8
      t10 = St (load-from-slot (suc n)) t9

      -- ── frames
      cf1 : current-frame (falloc t1) ≡ f₀
      cf1 = cfx (store-at-slot n) σ
      cf2 : current-frame (falloc t2) ≡ f₀
      cf2 = trans (cfx (instr-alloc-heap 2) t1) cf1
      cf3 : current-frame (falloc t3) ≡ f₀
      cf3 = trans (cfx (store-at-slot (suc n)) t2) cf2
      cf4 : current-frame (falloc t4) ≡ f₀
      cf4 = trans (cfx (restore-input 0) t3) cf3
      cf5 : current-frame (falloc t5) ≡ f₀
      cf5 = trans (cfx load-indirect t4) cf4
      cf6 : current-frame (falloc t6) ≡ f₀
      cf6 = trans (cfx (restore-input (suc n)) t5) cf5
      cf7 : current-frame (falloc t7) ≡ f₀
      cf7 = trans (cfx store-indirect t6) cf6
      cf8 : current-frame (falloc t8) ≡ f₀
      cf8 = trans (cfx (load-from-slot n) t7) cf7
      cf9 : current-frame (falloc t9) ≡ f₀
      cf9 = trans (cfx store-indirect-suc t8) cf8
      cf10 : current-frame (falloc t10) ≡ f₀
      cf10 = trans (cfx (load-from-slot (suc n)) t9) cf9

      ne-n : n ≢ suc n
      ne-n eq = <-irrefl eq (n<1+n n)
      ne-0n : 0 ≢ n
      ne-0n eq = <-irrefl eq n≥1
      ne-0sn : 0 ≢ suc n
      ne-0sn eq = <-irrefl eq (s≤s z≤n)

      -- ── slot 0: the forced suspension's seed pair
      s01 : readLoc (floc t1) (AtStack f₀ 0) ≡ just (SV-Ptr pl)
      s01 = trans (sl-other n 0 s₀ a₀ f₀ ne-0n) sl0
      s02 : readLoc (floc t2) (AtStack f₀ 0) ≡ just (SV-Ptr pl)
      s02 = trans (sl-keep (instr-alloc-heap 2) (floc t1) (falloc t1) f₀ 0 nhw-instr-alloc-heap refl) s01
      s03 : readLoc (floc t3) (AtStack f₀ 0) ≡ just (SV-Ptr pl)
      s03 = trans (sl-other (suc n) 0 (floc t2) (falloc t2) f₀ ne-0sn) s02

      -- ── slot n: the seed
      sn1 : readLoc (floc t1) (AtStack f₀ n) ≡ just av
      sn1 = sl-same n s₀ a₀ f₀ refl
      sn2 : readLoc (floc t2) (AtStack f₀ n) ≡ just av
      sn2 = trans (sl-keep (instr-alloc-heap 2) (floc t1) (falloc t1) f₀ n nhw-instr-alloc-heap refl) sn1
      sn3 : readLoc (floc t3) (AtStack f₀ n) ≡ just av
      sn3 = trans (sl-other (suc n) n (floc t2) (falloc t2) f₀ ne-n) sn2
      sn4 : readLoc (floc t4) (AtStack f₀ n) ≡ just av
      sn4 = trans (sl-keep (restore-input 0) (floc t3) (falloc t3) f₀ n nhw-restore-input refl) sn3
      sn5 : readLoc (floc t5) (AtStack f₀ n) ≡ just av
      sn5 = trans (sl-keep load-indirect (floc t4) (falloc t4) f₀ n nhw-load-indirect refl) sn4
      sn6 : readLoc (floc t6) (AtStack f₀ n) ≡ just av
      sn6 = trans (sl-keep (restore-input (suc n)) (floc t5) (falloc t5) f₀ n nhw-restore-input refl) sn5

      -- ── slot suc n: the pair pointer
      out2 : readReg (regs (floc t2)) Output ≡ SV-Ptr (AtDynamic qhl)
      out2 = out-alloc 2 (floc t1) (falloc t1)

      sq3 : readLoc (floc t3) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq3 = trans (sl-same (suc n) (floc t2) (falloc t2) f₀ cf2) (cong just out2)
      sq4 : readLoc (floc t4) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq4 = trans (sl-keep (restore-input 0) (floc t3) (falloc t3) f₀ (suc n) nhw-restore-input refl) sq3
      sq5 : readLoc (floc t5) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq5 = trans (sl-keep load-indirect (floc t4) (falloc t4) f₀ (suc n) nhw-load-indirect refl) sq4

      -- ── the frontier-`n` memory, rows 1–10
      a-n : AllocState {FS}
      a-n = record a₀ { next-slot = n }

      mem1 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t1) loc ≡ readLoc s₀ loc
      mem1 loc bf = store-slot-preserves-before n s₀ a-n a₀ loc refl ≤-refl bf
      mem2 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t2) loc ≡ readLoc s₀ loc
      mem2 loc bf = trans (mem-untouched (instr-alloc-heap 2) (floc t1) (falloc t1) loc nhw-instr-alloc-heap refl) (mem1 loc bf)
      mem3 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t3) loc ≡ readLoc s₀ loc
      mem3 loc bf = trans (store-slot-preserves-before (suc n) (floc t2) a-n (falloc t2) loc cf2 (n≤1+n n) bf) (mem2 loc bf)
      mem4 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t4) loc ≡ readLoc s₀ loc
      mem4 loc bf = trans (mem-untouched (restore-input 0) (floc t3) (falloc t3) loc nhw-restore-input refl) (mem3 loc bf)

      -- ── rows 4–5: the environment cell
      in4 : readReg (regs (floc t4)) Input1 ≡ SV-Ptr pl
      in4 = in-restore 0 (floc t3) (falloc t3) (SV-Ptr pl) (at-cf (floc t3) (falloc t3) cf3 s03)

      rpl4 : readLoc (floc t4) pl ≡ just ec
      rpl4 = trans (mem4 pl (live-ns n (live-from b a₀ hb pl lpl))) (cell-read cE)

      out5 : readReg (regs (floc t5)) Output ≡ ec
      out5 = out-lind (floc t4) (falloc t4) pl ec in4 rpl4

      mem5 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t5) loc ≡ readLoc s₀ loc
      mem5 loc bf = trans (mem-untouched load-indirect (floc t4) (falloc t4) loc nhw-load-indirect refl) (mem4 loc bf)
      mem6 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t6) loc ≡ readLoc s₀ loc
      mem6 loc bf = trans (mem-untouched (restore-input (suc n)) (floc t5) (falloc t5) loc nhw-restore-input refl) (mem5 loc bf)

      -- ── rows 6–7: the env cell, written at the pair's first cell
      in6 : readReg (regs (floc t6)) Input1 ≡ SV-Ptr (AtDynamic qhl)
      in6 = in-restore (suc n) (floc t5) (falloc t5) _ (at-cf (floc t5) (falloc t5) cf5 sq5)

      rdi6 : sv-as-loc (readReg (regs (floc t6)) Input1) ≡ just (AtDynamic qhl)
      rdi6 = cong sv-as-loc in6

      out6 : readReg (regs (floc t6)) Output ≡ ec
      out6 = trans (out-restore (suc n) (floc t5) (falloc t5) _ (at-cf (floc t5) (falloc t5) cf5 sq5)) out5

      hq7 : readLoc (floc t7) (AtDynamic qhl) ≡ just ec
      hq7 = trans (store-ind-result (floc t6) (falloc t6) qhl rdi6) (cong just out6)

      mem7 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t7) loc ≡ readLoc s₀ loc
      mem7 loc bf = trans (store-ind-preserves-before (floc t6) a-n (falloc t6) qhl loc rdi6 ≤-refl bf) (mem6 loc bf)

      in7 : readReg (regs (floc t7)) Input1 ≡ SV-Ptr (AtDynamic qhl)
      in7 = trans (in-sind (floc t6) (falloc t6) _ rdi6) in6

      sn7 : readLoc (floc t7) (AtStack f₀ n) ≡ just av
      sn7 = trans (sl-sind (floc t6) (falloc t6) qhl f₀ n rdi6) sn6
      sq6 : readLoc (floc t6) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq6 = trans (sl-keep (restore-input (suc n)) (floc t5) (falloc t5) f₀ (suc n) nhw-restore-input refl) sq5
      sq7 : readLoc (floc t7) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq7 = trans (sl-sind (floc t6) (falloc t6) qhl f₀ (suc n) rdi6) sq6

      -- ── rows 8–9: the seed, at the pair's second cell
      out8 : readReg (regs (floc t8)) Output ≡ av
      out8 = out-lslot n (floc t7) (falloc t7) av (at-cf (floc t7) (falloc t7) cf7 sn7)

      in8 : readReg (regs (floc t8)) Input1 ≡ SV-Ptr (AtDynamic qhl)
      in8 = trans (in-lslot n (floc t7) (falloc t7) av (at-cf (floc t7) (falloc t7) cf7 sn7)) in7

      rdi8 : sv-as-loc (readReg (regs (floc t8)) Input1) ≡ just (AtDynamic qhl)
      rdi8 = cong sv-as-loc in8

      hs9 : readLoc (floc t9) (AtDynamic (sucHL qhl)) ≡ just av
      hs9 = trans (store-ind-suc-result (floc t8) (falloc t8) qhl rdi8) (cong just out8)

      hq8 : readLoc (floc t8) (AtDynamic qhl) ≡ just ec
      hq8 = trans (hp-keep (load-from-slot n) (floc t7) (falloc t7) qhl nhw-load-from-slot) hq7
      hq9 : readLoc (floc t9) (AtDynamic qhl) ≡ just ec
      hq9 = trans (store-ind-suc-preserves-heap (floc t8) (falloc t8) qhl qhl rdi8 (sucHL-≢ qhl)) hq8

      mem8 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t8) loc ≡ readLoc s₀ loc
      mem8 loc bf = trans (mem-untouched (load-from-slot n) (floc t7) (falloc t7) loc nhw-load-from-slot refl) (mem7 loc bf)
      mem9 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t9) loc ≡ readLoc s₀ loc
      mem9 loc bf = trans (store-ind-suc-preserves-before (floc t8) a-n (falloc t8) qhl loc rdi8 ≤-refl bf) (mem8 loc bf)
      mem10 : ∀ loc → BeforeFrontier a-n loc → readLoc (floc t10) loc ≡ readLoc s₀ loc
      mem10 loc bf = trans (mem-untouched (load-from-slot (suc n)) (floc t9) (falloc t9) loc nhw-load-from-slot refl) (mem9 loc bf)

      sq8 : readLoc (floc t8) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq8 = trans (sl-keep (load-from-slot n) (floc t7) (falloc t7) f₀ (suc n) nhw-load-from-slot refl) sq7
      sq9 : readLoc (floc t9) (AtStack f₀ (suc n)) ≡ just (SV-Ptr (AtDynamic qhl))
      sq9 = trans (sl-sind-suc (floc t8) (falloc t8) qhl f₀ (suc n) rdi8) sq8

      -- ── row 10: the pair pointer back in Output
      out10 : readReg (regs (floc t10)) Output ≡ SV-Ptr (AtDynamic qhl)
      out10 = out-lslot (suc n) (floc t9) (falloc t9) _ (at-cf (floc t9) (falloc t9) cf9 sq9)

      hq10 : readLoc (floc t10) (AtDynamic qhl) ≡ just ec
      hq10 = trans (hp-keep (load-from-slot (suc n)) (floc t9) (falloc t9) qhl nhw-load-from-slot) hq9
      hs10 : readLoc (floc t10) (AtDynamic (sucHL qhl)) ≡ just av
      hs10 = trans (hp-keep (load-from-slot (suc n)) (floc t9) (falloc t9) (sucHL qhl) nhw-load-from-slot) hs9

      -- ── the frontiers after row 10
      hr10 : next-heap-ref (falloc t10) ≡ suc (next-heap-ref a₀)
      hr10 =
        trans (exec-abstract-preserves-heap-ref (load-from-slot (suc n)) (floc t9) (falloc t9) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc t8) (falloc t8) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot n) (floc t7) (falloc t7) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc t6) (falloc t6) tt)
       (trans (exec-abstract-preserves-heap-ref (restore-input (suc n)) (floc t5) (falloc t5) tt)
       (trans (exec-abstract-preserves-heap-ref load-indirect (floc t4) (falloc t4) tt)
       (trans (exec-abstract-preserves-heap-ref (restore-input 0) (floc t3) (falloc t3) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot (suc n)) (floc t2) (falloc t2) tt)))))))

      ns10 : next-slot (falloc t10) ≡ next-slot a₀
      ns10 =
        trans (exec-abstract-preserves-next-slot (load-from-slot (suc n)) (floc t9) (falloc t9) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc t8) (falloc t8) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot n) (floc t7) (falloc t7) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect (floc t6) (falloc t6) tt)
       (trans (exec-abstract-preserves-next-slot (restore-input (suc n)) (floc t5) (falloc t5) tt)
       (trans (exec-abstract-preserves-next-slot load-indirect (floc t4) (falloc t4) tt)
       (trans (exec-abstract-preserves-next-slot (restore-input 0) (floc t3) (falloc t3) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot (suc n)) (floc t2) (falloc t2) tt)
       (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc t1) (falloc t1) tt)
              (exec-abstract-preserves-next-slot (store-at-slot n) s₀ a₀ tt)))))))))

      sf10 : saved-frames (falloc t10) ≡ saved-frames a₀
      sf10 =
        trans (sfx (load-from-slot (suc n)) t9) (trans (sfx store-indirect-suc t8)
       (trans (sfx (load-from-slot n) t7) (trans (sfx store-indirect t6)
       (trans (sfx (restore-input (suc n)) t5) (trans (sfx load-indirect t4)
       (trans (sfx (restore-input 0) t3) (trans (sfx (store-at-slot (suc n)) t2)
       (trans (sfx (instr-alloc-heap 2) t1) (sfx (store-at-slot n) σ)))))))))

      ------------------------------------------------------------------
      -- ROWS 11–19: the suspension `[pair , code]` (`NineStepPres`).
      ------------------------------------------------------------------
      module NSP = NineStepPres N (load-from-slot N) (instr-load-code-addr lbl) t10 (floc t10) (falloc t10) refl refl
      open NSP using (u2; u3; u4; u5; u6; u7; u8; u9; u10)

      shl : HeapLocation
      shl = NSP.hl

      g₀ = current-frame (falloc t10)

      cfu2 : current-frame (falloc u2) ≡ g₀
      cfu2 = cfx (store-at-slot N) t10
      cfu3 : current-frame (falloc u3) ≡ g₀
      cfu3 = NSP.cf-u3
      cfu4 : current-frame (falloc u4) ≡ g₀
      cfu4 = trans (cfx (store-at-slot (suc N)) u3) cfu3
      cfu5 : current-frame (falloc u5) ≡ g₀
      cfu5 = trans (cfx mov-to-input u4) cfu4
      cfu6 : current-frame (falloc u6) ≡ g₀
      cfu6 = trans (cfx (load-from-slot N) u5) cfu5
      cfu7 : current-frame (falloc u7) ≡ g₀
      cfu7 = trans (cfx store-indirect u6) cfu6
      cfu8 : current-frame (falloc u8) ≡ g₀
      cfu8 = trans (cfx (instr-load-code-addr lbl) u7) cfu7
      cfu9 : current-frame (falloc u9) ≡ g₀
      cfu9 = trans (cfx store-indirect-suc u8) cfu8
      cfu10 : current-frame (falloc u10) ≡ g₀
      cfu10 = trans (cfx (load-from-slot (suc N)) u9) cfu9

      neN : N ≢ suc N
      neN eq = <-irrefl eq (n<1+n N)

      sN2 : readLoc (floc u2) (AtStack g₀ N) ≡ just (SV-Ptr (AtDynamic qhl))
      sN2 = trans (sl-same N (floc t10) (falloc t10) g₀ refl) (cong just out10)
      sN3 : readLoc (floc u3) (AtStack g₀ N) ≡ just (SV-Ptr (AtDynamic qhl))
      sN3 = trans (sl-keep (instr-alloc-heap 2) (floc u2) (falloc u2) g₀ N nhw-instr-alloc-heap refl) sN2
      sN4 : readLoc (floc u4) (AtStack g₀ N) ≡ just (SV-Ptr (AtDynamic qhl))
      sN4 = trans (sl-other (suc N) N (floc u3) (falloc u3) g₀ neN) sN3
      sN5 : readLoc (floc u5) (AtStack g₀ N) ≡ just (SV-Ptr (AtDynamic qhl))
      sN5 = trans (sl-keep mov-to-input (floc u4) (falloc u4) g₀ N nhw-mov-to-input refl) sN4

      outu3 : readReg (regs (floc u3)) Output ≡ SV-Ptr (AtDynamic shl)
      outu3 = out-alloc 2 (floc u2) (falloc u2)

      sS4 : readLoc (floc u4) (AtStack g₀ (suc N)) ≡ just (SV-Ptr (AtDynamic shl))
      sS4 = trans (sl-same (suc N) (floc u3) (falloc u3) g₀ cfu3) (cong just outu3)
      sS5 : readLoc (floc u5) (AtStack g₀ (suc N)) ≡ just (SV-Ptr (AtDynamic shl))
      sS5 = trans (sl-keep mov-to-input (floc u4) (falloc u4) g₀ (suc N) nhw-mov-to-input refl) sS4
      sS6 : readLoc (floc u6) (AtStack g₀ (suc N)) ≡ just (SV-Ptr (AtDynamic shl))
      sS6 = trans (sl-keep (load-from-slot N) (floc u5) (falloc u5) g₀ (suc N) nhw-load-from-slot refl) sS5

      inu5 : readReg (regs (floc u5)) Input1 ≡ SV-Ptr (AtDynamic shl)
      inu5 = trans (in-movin (floc u4) (falloc u4))
               (trans (reg-store (suc N) (floc u3) (falloc u3) Output) outu3)

      inu6 : readReg (regs (floc u6)) Input1 ≡ SV-Ptr (AtDynamic shl)
      inu6 = trans (in-lslot N (floc u5) (falloc u5) _ (at-cf (floc u5) (falloc u5) cfu5 sN5)) inu5
      rdiu6 : sv-as-loc (readReg (regs (floc u6)) Input1) ≡ just (AtDynamic shl)
      rdiu6 = cong sv-as-loc inu6

      outu6 : readReg (regs (floc u6)) Output ≡ SV-Ptr (AtDynamic qhl)
      outu6 = out-lslot N (floc u5) (falloc u5) _ (at-cf (floc u5) (falloc u5) cfu5 sN5)

      hsh7 : readLoc (floc u7) (AtDynamic shl) ≡ just (SV-Ptr (AtDynamic qhl))
      hsh7 = trans (store-ind-result (floc u6) (falloc u6) shl rdiu6) (cong just outu6)

      inu7 : readReg (regs (floc u7)) Input1 ≡ SV-Ptr (AtDynamic shl)
      inu7 = trans (in-sind (floc u6) (falloc u6) _ rdiu6) inu6
      inu8 : readReg (regs (floc u8)) Input1 ≡ SV-Ptr (AtDynamic shl)
      inu8 = trans (in-code lbl (floc u7) (falloc u7)) inu7
      rdiu8 : sv-as-loc (readReg (regs (floc u8)) Input1) ≡ just (AtDynamic shl)
      rdiu8 = cong sv-as-loc inu8

      hsh8 : readLoc (floc u8) (AtDynamic shl) ≡ just (SV-Ptr (AtDynamic qhl))
      hsh8 = trans (hp-keep (instr-load-code-addr lbl) (floc u7) (falloc u7) shl nhw-instr-load-code-addr) hsh7
      hsh9 : readLoc (floc u9) (AtDynamic shl) ≡ just (SV-Ptr (AtDynamic qhl))
      hsh9 = trans (store-ind-suc-preserves-heap (floc u8) (falloc u8) shl shl rdiu8 (sucHL-≢ shl)) hsh8
      hsh10 : readLoc (floc u10) (AtDynamic shl) ≡ just (SV-Ptr (AtDynamic qhl))
      hsh10 = trans (hp-keep (load-from-slot (suc N)) (floc u9) (falloc u9) shl nhw-load-from-slot) hsh9

      hcode9 : readLoc (floc u9) (AtDynamic (sucHL shl)) ≡ just (SV-Code lbl)
      hcode9 = trans (store-ind-suc-result (floc u8) (falloc u8) shl rdiu8) (cong just (out-code lbl (floc u7) (falloc u7)))
      hcode10 : readLoc (floc u10) (AtDynamic (sucHL shl)) ≡ just (SV-Code lbl)
      hcode10 = trans (hp-keep (load-from-slot (suc N)) (floc u9) (falloc u9) (sucHL shl) nhw-load-from-slot) hcode9

      sS7 : readLoc (floc u7) (AtStack g₀ (suc N)) ≡ just (SV-Ptr (AtDynamic shl))
      sS7 = trans (sl-sind (floc u6) (falloc u6) shl g₀ (suc N) rdiu6) sS6
      sS8 : readLoc (floc u8) (AtStack g₀ (suc N)) ≡ just (SV-Ptr (AtDynamic shl))
      sS8 = trans (sl-keep (instr-load-code-addr lbl) (floc u7) (falloc u7) g₀ (suc N) nhw-instr-load-code-addr refl) sS7
      sS9 : readLoc (floc u9) (AtStack g₀ (suc N)) ≡ just (SV-Ptr (AtDynamic shl))
      sS9 = trans (sl-sind-suc (floc u8) (falloc u8) shl g₀ (suc N) rdiu8) sS8

      outu10 : readReg (regs (floc u10)) Output ≡ SV-Ptr (AtDynamic shl)
      outu10 = out-lslot (suc N) (floc u9) (falloc u9) _ (at-cf (floc u9) (falloc u9) cfu9 sS9)

      -- ── what the nine rows leave alone
      N≥ : next-slot (falloc t10) ≤ N
      N≥ = subst (_≤ N) (sym (trans ns10 ns0)) z≤n

      memN : ∀ loc → BeforeFrontier (record (falloc t10) { next-slot = N }) loc
           → readLoc (floc u10) loc ≡ readLoc (floc t10) loc
      memN = NSP.mem-pres-from nhw-load-from-slot refl nhw-instr-load-code-addr refl N≥ rdiu6 rdiu8

      q< : next-heap-ref a₀ < next-heap-ref (falloc t10)
      q< = subst (next-heap-ref a₀ <_) (sym hr10) (n<1+n _)

      hqu : readLoc (floc u10) (AtDynamic qhl) ≡ just ec
      hqu = trans (memN (AtDynamic qhl) (BeforeFrontier.heap-before q<)) hq10
      hsu : readLoc (floc u10) (AtDynamic (sucHL qhl)) ≡ just av
      hsu = trans (memN (AtDynamic (sucHL qhl)) (BeforeFrontier.heap-before q<)) hs10

      hru10 : next-heap-ref (falloc u10) ≡ suc (next-heap-ref (falloc u2))
      hru10 =
        trans (exec-abstract-preserves-heap-ref (load-from-slot (suc N)) (floc u9) (falloc u9) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect-suc (floc u8) (falloc u8) tt)
       (trans (exec-abstract-preserves-heap-ref (instr-load-code-addr lbl) (floc u7) (falloc u7) tt)
       (trans (exec-abstract-preserves-heap-ref store-indirect (floc u6) (falloc u6) tt)
       (trans (exec-abstract-preserves-heap-ref (load-from-slot N) (floc u5) (falloc u5) tt)
       (trans (exec-abstract-preserves-heap-ref mov-to-input (floc u4) (falloc u4) tt)
              (exec-abstract-preserves-heap-ref (store-at-slot (suc N)) (floc u3) (falloc u3) tt))))))

      -- the pair was allocated first, the suspension second: both below u10's frontier
      s< : next-heap-ref (falloc u2) < next-heap-ref (falloc u10)
      s< = subst (next-heap-ref (falloc u2) <_) (sym hru10) (n<1+n _)

      q<u : next-heap-ref a₀ < next-heap-ref (falloc u10)
      q<u = <-trans q< (subst (_< next-heap-ref (falloc u10)) NSP.heapref-u2 s<)

      nsu : next-slot (falloc u10) ≡ next-slot (falloc t10)
      nsu =
        trans (exec-abstract-preserves-next-slot (load-from-slot (suc N)) (floc u9) (falloc u9) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect-suc (floc u8) (falloc u8) tt)
       (trans (exec-abstract-preserves-next-slot (instr-load-code-addr lbl) (floc u7) (falloc u7) tt)
       (trans (exec-abstract-preserves-next-slot store-indirect (floc u6) (falloc u6) tt)
       (trans (exec-abstract-preserves-next-slot (load-from-slot N) (floc u5) (falloc u5) tt)
       (trans (exec-abstract-preserves-next-slot mov-to-input (floc u4) (falloc u4) tt)
       (trans (exec-abstract-preserves-next-slot (store-at-slot (suc N)) (floc u3) (falloc u3) tt)
       (trans (exec-abstract-preserves-next-slot (instr-alloc-heap 2) (floc u2) (falloc u2) tt)
              (exec-abstract-preserves-next-slot (store-at-slot N) (floc t10) (falloc t10) tt))))))))

      sfu : saved-frames (falloc u10) ≡ saved-frames (falloc t10)
      sfu =
        trans (sfx (load-from-slot (suc N)) u9) (trans (sfx store-indirect-suc u8)
       (trans (sfx (instr-load-code-addr lbl) u7) (trans (sfx store-indirect u6)
       (trans (sfx (load-from-slot N) u5) (trans (sfx mov-to-input u4)
       (trans (sfx (store-at-slot (suc N)) u3) (trans (sfx (instr-alloc-heap 2) u2)
              (sfx (store-at-slot N) t10))))))))

      seg : Seg n σ u10
      seg = record
        { mem  = λ loc bf → trans (memN loc (bf-step {a₀} {falloc t10} n N cf10 (≤-trans (n≤1+n n) (n≤1+n (suc n)))
                                               (subst (next-heap-ref a₀ ≤_) (sym hr10) (n≤1+n _)) loc bf))
                                  (mem10 loc bf)
        ; cf   = trans cfu10 cf10
        ; sf   = trans sfu sf10
        ; ns   = trans nsu ns10
        ; href = <⇒≤ q<u
        }
        where
          <⇒≤ : ∀ {x z : ℕ} → x < z → x ≤ z
          <⇒≤ p = ≤-trans (n≤1+n _) p

      ------------------------------------------------------------------
      -- THE RESULT: a fresh suspension of `(e , a′)`.
      ------------------------------------------------------------------
      h₀ : ℕ
      h₀ = next-heap-ref a₀

      fresh : ∀ (hl : HeapLocation) → h₀ ≤ loc-ref (AtDynamic hl) → loc-ref (AtDynamic hl) < next-heap-ref (falloc u10)
            → Prot b h₀ (falloc u10) (AtDynamic hl)
      fresh hl le lt = BeforeFrontier.heap-before lt , inj₂ le

      h₀≤u2 : h₀ ≤ next-heap-ref (falloc u2)
      h₀≤u2 = subst (h₀ ≤_) (sym NSP.heapref-u2) (subst (h₀ ≤_) (sym hr10) (n≤1+n _))

      p-q : Prot b h₀ (falloc u10) (AtDynamic qhl)
      p-q = fresh qhl ≤-refl q<u
      p-sq : Prot b h₀ (falloc u10) (AtDynamic (sucHL qhl))
      p-sq = fresh (sucHL qhl) ≤-refl q<u
      p-s : Prot b h₀ (falloc u10) (AtDynamic shl)
      p-s = fresh shl h₀≤u2 s<
      p-ss : Prot b h₀ (falloc u10) (AtDynamic (sucHL shl))
      p-ss = fresh (sucHL shl) h₀≤u2 s<

      b≤u : next-heap-ref b ≤ next-heap-ref (falloc u10)
      b≤u = ≤-trans hb (SegA.href seg)

      -- the suspension, at any later state that keeps the footprint
      child : ∀ {a′ : AllocState {FS}} {s′ : LocState FS}
            → (∀ l → Live (falloc u10) l → Live a′ l)
            → (∀ l → Prot b h₀ (falloc u10) l → readLoc s′ l ≡ readLoc (floc u10) l)
            → R Heap a′ (rsd wf-Id y) (AtDynamic shl) s′
      child {a′} {s′} bft rd = mk-child y tt (trans (rd _ p-ss) hcode10) (bft _ (proj₁ p-ss)) cellP
        where
          kb : Kp b s₀ a′ s′
          kb = (λ l x → bft l (live-from b (falloc u10) b≤u l x))
             , (λ l x → trans (rd l (live-from b (falloc u10) b≤u l x , inj₁ x)) (seg-live-read seg l (live-from b a₀ hb l x)))

          cellE : CellAt {prog = prog} a′ E e (AtDynamic qhl) s′
          cellE = cell-copy kb (trans (rd _ p-q) (trans hqu (sym (cell-read cE)))) cE

          cellA : CellAt {prog = prog} a′ A y (sucLoc (AtDynamic qhl)) s′
          cellA = out→cell kb oA (trans (rd _ p-sq) hsu)

          cellP : CellAt {prog = prog} a′ (E IRTy′.* A) (e , y) (AtDynamic shl) s′
          cellP = cell-ptr {mC = Heap} (trans (rd _ p-s) hsh10) (bft _ (proj₁ p-q))
                    (valid-pair-wf tt (bft _ (proj₁ p-sq)) cellE cellA)

      ------------------------------------------------------------------
      -- THE RUN.
      ------------------------------------------------------------------
      nh1 : halted (floc t1) ≡ false
      nh1 = exec-abstract-preserves-halted-WF (store-at-slot n) s₀ a₀ nh0 tt
      nh2 : halted (floc t2) ≡ false
      nh2 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc t1) (falloc t1) nh1 tt
      nh3 : halted (floc t3) ≡ false
      nh3 = exec-abstract-preserves-halted-WF (store-at-slot (suc n)) (floc t2) (falloc t2) nh2 tt
      nh4 : halted (floc t4) ≡ false
      nh4 = exec-abstract-preserves-halted-WF (restore-input 0) (floc t3) (falloc t3) nh3 (_ , at-cf (floc t3) (falloc t3) cf3 s03)
      nh5 : halted (floc t5) ≡ false
      nh5 = exec-abstract-preserves-halted-WF load-indirect (floc t4) (falloc t4) nh4 (pl , cong sv-as-loc in4 , ec , rpl4)
      nh6 : halted (floc t6) ≡ false
      nh6 = exec-abstract-preserves-halted-WF (restore-input (suc n)) (floc t5) (falloc t5) nh5 (_ , at-cf (floc t5) (falloc t5) cf5 sq5)
      nh7 : halted (floc t7) ≡ false
      nh7 = exec-abstract-preserves-halted-WF store-indirect (floc t6) (falloc t6) nh6 (_ , rdi6)
      nh8 : halted (floc t8) ≡ false
      nh8 = exec-abstract-preserves-halted-WF (load-from-slot n) (floc t7) (falloc t7) nh7 (_ , at-cf (floc t7) (falloc t7) cf7 sn7)
      nh9 : halted (floc t9) ≡ false
      nh9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc t8) (falloc t8) nh8 (_ , rdi8)
      nh10 : halted (floc t10) ≡ false
      nh10 = exec-abstract-preserves-halted-WF (load-from-slot (suc n)) (floc t9) (falloc t9) nh9 (_ , at-cf (floc t9) (falloc t9) cf9 sq9)
      nhu2 : halted (floc u2) ≡ false
      nhu2 = exec-abstract-preserves-halted-WF (store-at-slot N) (floc t10) (falloc t10) nh10 tt
      nhu3 : halted (floc u3) ≡ false
      nhu3 = exec-abstract-preserves-halted-WF (instr-alloc-heap 2) (floc u2) (falloc u2) nhu2 tt
      nhu4 : halted (floc u4) ≡ false
      nhu4 = exec-abstract-preserves-halted-WF (store-at-slot (suc N)) (floc u3) (falloc u3) nhu3 tt
      nhu5 : halted (floc u5) ≡ false
      nhu5 = exec-abstract-preserves-halted-WF mov-to-input (floc u4) (falloc u4) nhu4 tt
      nhu6 : halted (floc u6) ≡ false
      nhu6 = exec-abstract-preserves-halted-WF (load-from-slot N) (floc u5) (falloc u5) nhu5 (_ , at-cf (floc u5) (falloc u5) cfu5 sN5)
      nhu7 : halted (floc u7) ≡ false
      nhu7 = exec-abstract-preserves-halted-WF store-indirect (floc u6) (falloc u6) nhu6 (_ , rdiu6)
      nhu8 : halted (floc u8) ≡ false
      nhu8 = exec-abstract-preserves-halted-WF (instr-load-code-addr lbl) (floc u7) (falloc u7) nhu7 tt
      nhu9 : halted (floc u9) ≡ false
      nhu9 = exec-abstract-preserves-halted-WF store-indirect-suc (floc u8) (falloc u8) nhu8 (_ , rdiu8)
      nhu10 : halted (floc u10) ≡ false
      nhu10 = exec-abstract-preserves-halted-WF (load-from-slot (suc N)) (floc u9) (falloc u9) nhu9 (_ , at-cf (floc u9) (falloc u9) cfu9 sS9)

      -- In three typed pieces: unifying the whole 19-step chain at once cost
      -- ~5 GB (each step's implicit state and instruction).
      srC : SRun prog 5 u5 u10
      srC =
        s-at u6 (nhu5 , span 14 _ refl) refl refl tt (
        s-at u7 (nhu6 , span 15 _ refl) refl refl tt (
        s-at u8 (nhu7 , span 16 _ refl) refl refl tt (
        s-at u9 (nhu8 , span 17 _ refl) refl refl tt (
        s-at u10 (nhu9 , span 18 _ refl) refl refl tt (
        s-nil)))))

      srB : SRun prog 12 t7 u10
      srB =
        s-at t8 (nh7 , span 7 _ refl) refl refl tt (
        s-at t9 (nh8 , span 8 _ refl) refl refl tt (
        s-at t10 (nh9 , span 9 _ refl) refl refl tt (
        s-at u2 (nh10 , span 10 _ refl) refl refl tt (
        s-at u3 (nhu2 , span 11 _ refl) refl refl tt (
        s-at u4 (nhu3 , span 12 _ refl) refl refl tt (
        s-at u5 (nhu4 , span 13 _ refl) refl refl tt srC))))))

      sr : SRun prog 19 σ u10
      sr =
        s-at t1 (nh0 , span 0 _ refl) refl refl tt (
        s-at t2 (nh1 , span 1 _ refl) refl refl tt (
        s-at t3 (nh2 , span 2 _ refl) refl refl tt (
        s-at t4 (nh3 , span 3 _ refl) refl refl tt (
        s-at t5 (nh4 , span 4 _ refl) refl refl tt (
        s-at t6 (nh5 , span 5 _ refl) refl refl tt (
        s-at t7 (nh6 , span 6 _ refl) refl refl tt srB))))))

      run : FlatSteps prog 19 σ u10
      run = proj₁ sr

      result : RRuns′ wf-Id n l σ y b
      result = record
        { steps    = 19
        ; settle   = u10
        ; run      = run
        ; nh       = nhu10
        ; pc       = refl
        ; ret      = refl
        ; lnk      = lk
        ; ev       = proj₁ (proj₂ sr)
        ; log      = proj₂ (proj₂ sr)
        ; left     = chain-left run nhu10
        ; out-mode = Heap
        ; rout     = ro-loc (AtDynamic shl) (proj₁ p-s) outu10 child
        ; seg      = seg
        }

    resusp-Id : Resusp′ wf-Id
    resusp-Id n l σ y pl b hb span _ nh lk ns n≥1 sl0 lpl cE oA =
      Run.result n l σ y pl span nh lk ns n≥1 sl0 b hb lpl cE oA
