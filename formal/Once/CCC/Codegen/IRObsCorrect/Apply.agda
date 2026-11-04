-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Apply
--
-- D200: `apply` — the setup, the call, and the hand-off to the closure's own
-- `runs` (plan 0.135 S1). plan 0.123 B.4 α / D380: the setup builds the call
-- pair `[env-word, arg…]` on the flat layout:
--
--   get A 1 ; store-at-slot n ; load-at 0 ; mov-to-input      -- arg; closure
--   instr-save-closure-reg                                     -- closure-reg
--   load-at 0 ; store-at-slot (n+1)                            -- env word
--   instr-alloc-heap (2 ⊔ suc (size A)) ; store-at-slot (n+2) ; mov-to-input
--   load-from-slot (n+1) ; store-at 0 ; put A n (n+2) 1        -- the pair
--   load-from-slot (n+2) ; mov-to-input ; instr-call-closure
--
-- The read is `Get.get-run`; the two straight segments around the closure
-- register's save are `StraightRun`'s, their effect `exec-trace`'s.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Apply (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; SV-Ptr; sucLoc; offsetLoc; SV-Code; instr-call-closure; StoredValue; LocState; module LocState;
         readReg; writeReg; Input1; Output; AllocState; module AllocState; module ExecFinal;
         store-at-slot; load-from-slot; load-at; store-at; mov-to-input; instr-alloc-heap; instr-save-closure-reg)
open LocState using (halted; regs)
open AllocState using (current-frame; next-slot; saved-frames)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Label using (LabelId)
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack; ValueLocation)
open import Once.Memory.HeapAddress using (heap-loc)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (get; get-one; get-i; put; put-All)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc

import Once.CCC.FrameSemantics
import Once.CCC.Machine.SMPrimitives
import Once.IRTy
import Once.IRTy as IRTy′
import Once.IR
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m)
open import Once.Res using (is-stopped)
import Once.Semantics.Machine as EvV
import Once.CCC.Machine.ReadTypedAdequate as RTA
import Once.Denotation.DenotTrace as DT
import Once.IR.Semantics.Trace as TM
open import Once.Res using (returns)
open import Once.Denotation.Approx using (done; NotCut; budgetLeft)

module ApplyC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open SMCore.AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open SMCore.MemOps {FS} using (writeLoc; writeLoc-halted; writeLoc-regs; writeLoc-preserves-other; writeLoc-read-same-stack)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open FlatEventTrace {FS} using (chain-events-subst)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem)
  module SR = StraightRunAPI {FS}

  -- THE CALL at ANY state: `callView`'s three levels, from the closure
  -- register, the code cell and the thunk scan.
  call-at : ∀ (prog : AbstractTrace) (fs : FlatState) (hl : _) (ℓ : LabelId) (j : ℕ)
          → fclosure fs ≡ SV-Ptr (AtDynamic hl)
          → SMCore.MemOps.readLoc (floc fs) (sucLoc (AtDynamic hl)) ≡ just (SV-Code ℓ)
          → find-thunk prog ℓ ≡ just j
          → flat-exec-instr instr-call-closure prog fs
            ≡ record fs
                { falloc = enter-call (falloc fs)
                ; fret   = suc (fpc fs) ∷ fret fs
                ; flink  = just (suc (fpc fs))
                ; fpc    = j }
  call-at prog fs hl ℓ j reg code feq =
    trans (cong (λ z → do-call-sv prog z fs) reg)
      (trans (cong (λ z → do-call-code prog z fs) code)
             (cong (λ z → do-call-at z fs) feq))

  -- a load at an offset of the block `Input1` points to
  ld : ∀ k (s : LocState FS) (a : AllocState {FS}) (l : ValueLocation FS) (w : StoredValue FS)
     → readReg (regs s) Input1 ≡ SV-Ptr l → readLoc s (offsetLoc l k) ≡ just w
     → exec-abstract (load-at k) s a ≡ (record s { regs = writeReg (regs s) Output w } , a)
  ld k s a l w i1 r =
    trans (cong (λ x → (ExecFinal.exec-load-at-resolved {FS} k Output (SMCore.sv-as-loc x) s , a)) i1)
          (cong (λ m → (ExecFinal.exec-load-with-value {FS} Output m s , a)) r)

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtDynamic _) = 0
    slot-of (AtStack _ j) = j

    sne : ∀ {fr} {a b : ℕ} → a < b → AtStack {FS} fr b ≢ AtStack fr a
    sne a<b e = <-irrefl (sym (cong slot-of e)) a<b

  obs-correct-apply : ∀ {A B} → IRObsCorrectF (apply {A} {B})
  -- A PAIR fits no register and is not `Unit`, so the two off-pointer input
  -- residences are refuted outright; a live location is a heap cell.
  obs-correct-apply n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh (in-reg () _) k rs
  obs-correct-apply n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh (in-unit ()) k rs
  obs-correct-apply n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh (in-loc (AtStack _ _) _ () _) k rs
  obs-correct-apply {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl n≤ nh
    (in-loc (AtDynamic (heap-loc pr po)) valid bf rdi) k rs =
    go (PairValidWF.fst-cell d)
    where
      pair-loc : ValueLocation FS
      pair-loc = AtDynamic (heap-loc pr po)
      d = decomposePairWF valid

      -- A CLOSURE is never inline, and D184 pins it to the HEAP.
      go : CellAt {prog = prog} alloc (A IRTy′.⇛ B) (proj₁ x) pair-loc s
         → MachineRefinesObsF prog base n l (apply {A} {B}) x s alloc cl rs k
      go (cell-inline (rep-prim ()) _)
      go (cell-ptr {comp-loc = AtStack _ _} _ _ _ fv) =
        ⊥-elim (ClosureValidWF.loc-mode (decomposeClosureWF fv))
      go (cell-ptr {comp-loc = AtDynamic (heap-loc cr co)} _ fst-cell fst-bf fst-valid) =
        assemble (ClosureValidWF.env-at cvw)
        where
          fst-loc : ValueLocation FS
          fst-loc = AtDynamic (heap-loc cr co)
          cvw     = decomposeClosureWF fst-valid

          E    = ClosureValidWF.EnvType cvw
          env  = ClosureValidWF.env cvw
          blbl = ClosureValidWF.body-label cvw

          env-sv-of : EnvAt {prog = prog} alloc {E} env fst-loc s → StoredValue FS
          env-sv-of (env-at-loc el _ _) = SV-Ptr el
          env-sv-of (env-in-cell w _) = w

          env-cell-of : (ea : EnvAt {prog = prog} alloc {E} env fst-loc s)
                      → SMCore.MemOps.readLoc s fst-loc ≡ just (env-sv-of ea)
          env-cell-of (env-at-loc _ ep _) = ep
          env-cell-of (env-in-cell _ ep)  = ep

          assemble : EnvAt {prog = prog} alloc {E} env fst-loc s
                   → MachineRefinesObsF prog base n l (apply {A} {B}) x s alloc cl rs k
          assemble ea = result
            where
              ev = env-sv-of ea

              ------------------------------------------------------------------
              -- THE TEXT, with the read as its one instruction (`get-one`)
              ------------------------------------------------------------------
              N = 2 ⊔ suc (size A)
              T2  = load-from-slot (suc (suc n)) ∷ mov-to-input ∷ []
              S2 = load-at 0 ∷ store-at-slot (suc n) ∷ instr-alloc-heap N ∷ store-at-slot (suc (suc n)) ∷
                   mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              T1 = store-at-slot n ∷ load-at 0 ∷ mov-to-input ∷ []
              S2c = load-at 0 ∷ store-at-slot (suc n) ∷ instr-alloc-heap N ∷ store-at-slot (suc (suc n)) ∷
                    mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2 ++ instr-call-closure ∷ [])
              E′ = get-i A 1 ∷ (T1 ++ instr-save-closure-reg ∷ S2c)

              shape : emitted n l (apply {A} {B}) ≡ E′
              shape = cong (_++ (T1 ++ instr-save-closure-reg ∷ S2c)) (get-one A 1)

              span′ : SpanAt prog base E′
              span′ = subst (SpanAt prog base) shape span

              S2-c : S2 ++ instr-call-closure ∷ [] ≡ S2c
              S2-c = cong (λ t → load-at 0 ∷ store-at-slot (suc n) ∷ instr-alloc-heap N ∷ store-at-slot (suc (suc n)) ∷
                                 mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ t)
                          (++-assoc (put A n (suc (suc n)) 1) T2 (instr-call-closure ∷ []))

              ------------------------------------------------------------------
              -- 1. the read: the argument, at word 1 of the input pair
              ------------------------------------------------------------------
              fs0 = entry-flat base s alloc cl rs

              at0 : ∀ i → fetch (get A 1) 0 ≡ just i → fetch prog (fpc fs0) ≡ just i
              at0 i e = span′ 0 i (trans (sym (cong (λ t → fetch t 0) (get-one A 1))) e)

              g : GetOut {prog = prog} A (proj₂ x) fs0
              g = get-run A 1 fs0 pair-loc nh at0 rdi bf (PairValidWF.snd-cell d)
              module G = GetOut g
              g1 = setOut fs0 G.out
              u  = floc g1

              ------------------------------------------------------------------
              -- 2. stash it; the closure, into `Input1`
              ------------------------------------------------------------------
              u₁ = proj₁ (exec-abstract (store-at-slot n) u alloc)
              u₂ = record u₁ { regs = writeReg (regs u₁) Output (SV-Ptr fst-loc) }
              u₃ = proj₁ (exec-abstract mov-to-input u₂ alloc)

              seg1 : exec-trace T1 u alloc ≡ (u₃ , alloc)
              seg1 = trans (exec-trace-cons (store-at-slot n) _ u alloc nh)
                    (trans (exec-trace-cons (load-at 0) (mov-to-input ∷ []) u₁ alloc nh)
                    (trans (cong (λ r → exec-trace (mov-to-input ∷ []) (proj₁ r) (proj₂ r))
                                 (ld 0 u₁ alloc pair-loc (SV-Ptr fst-loc) rdi fst-cell))
                           (exec-trace-cons mov-to-input [] u₂ alloc nh)))

              at1 : SR.At prog (fpc g1) T1
              at1 j i e = subst (λ p → fetch prog p ≡ just i) (sym (+-suc j base))
                                (span′ (suc j) i (fetch-++-left T1 (instr-save-closure-reg ∷ S2c) j i e))

              sts1 : All StraightStep T1
              sts1 = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []

              evs1 : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T1
              evs1 = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []

              he1 : halted (proj₁ (exec-trace T1 u alloc)) ≡ false
              he1 = trans (cong (λ r → halted (proj₁ r)) seg1) nh

              f3 = record g1 { floc = u₃ ; falloc = alloc ; fpc = 3 + fpc g1 }
              eq1 : SR.after T1 g1 ≡ f3
              eq1 = cong (λ r → record g1 { floc = proj₁ r ; falloc = proj₂ r ; fpc = 3 + fpc g1 }) seg1
              run1₀ = SR.straight-steps {prog} T1 g1 sts1 at1 nh he1
              run1 : FlatSteps prog 3 g1 f3
              run1 = subst (FlatSteps prog 3 g1) eq1 run1₀

              ------------------------------------------------------------------
              -- 3. the closure register
              ------------------------------------------------------------------
              f4 = flat-exec-instr instr-save-closure-reg prog f3

              run-save : FlatSteps prog 1 f3 f4
              run-save = (nh , span′ 4 _ refl) ∷ []

              ------------------------------------------------------------------
              -- 4. the call pair `[env-word, arg…]`
              ------------------------------------------------------------------
              cf = current-frame alloc
              A₁ = FlatAlloc.alloc-after {FS} N alloc
              rd = FlatAlloc.fresh-ref {FS} alloc
              L : ValueLocation FS
              L  = AtDynamic (heap-loc rd 0)
              blk : StoredValue FS
              blk = SV-Ptr L

              v₁ = record u₃ { regs = writeReg (regs u₃) Output ev }
              v₂ = proj₁ (exec-abstract (store-at-slot (suc n)) v₁ alloc)
              v₃ = proj₁ (exec-abstract (instr-alloc-heap N) v₂ alloc)
              v₄ = proj₁ (exec-abstract (store-at-slot (suc (suc n))) v₃ A₁)
              v₅ = proj₁ (exec-abstract mov-to-input v₄ A₁)
              v₆ = record v₅ { regs = writeReg (regs v₅) Output ev }
              v₇ = writeLoc v₆ L ev

              slot-ev : readLoc v₅ (AtStack cf (suc n)) ≡ just ev
              slot-ev = trans (writeLoc-preserves-other v₃ (AtStack cf (suc (suc n))) (AtStack cf (suc n)) blk
                                 (sne (n<1+n (suc n))))
                              (writeLoc-read-same-stack v₁ cf (suc n) ev)

              ib0 : InBlk A₁ L
              ib0 = FlatAlloc.alloc-in {FS} N alloc 0 (s≤s z≤n)

              st0 : exec-abstract (store-at 0) v₆ A₁ ≡ (v₇ , A₁)
              st0 = cong (λ b → (ExecFinal.exec-store-in-block {FS} b L ev v₆ , A₁)) ib0

              h₇ : halted v₇ ≡ false
              h₇ = trans (writeLoc-halted v₆ L ev) nh

              slot-arg₇ : readLoc v₇ (AtStack cf n) ≡ just G.out
              slot-arg₇ =
                trans (writeLoc-preserves-other v₆ L (AtStack cf n) ev (λ ()))
               (trans (writeLoc-preserves-other v₃ (AtStack cf (suc (suc n))) (AtStack cf n) blk
                         (sne (≤-trans (n<1+n n) (n≤1+n (suc n)))))
               (trans (writeLoc-preserves-other v₁ (AtStack cf (suc n)) (AtStack cf n) ev (sne (n<1+n n)))
                      (writeLoc-read-same-stack u cf n G.out)))

              slot-blk₇ : readLoc v₇ (AtStack cf (suc (suc n))) ≡ just blk
              slot-blk₇ = trans (writeLoc-preserves-other v₆ L (AtStack cf (suc (suc n))) ev (λ ()))
                                (writeLoc-read-same-stack v₃ cf (suc (suc n)) blk)

              freshA : ∀ o → Live alloc (AtDynamic (heap-loc rd o)) → ⊥
              freshA o = FlatAlloc.alloc-fresh {FS} alloc o

              -- the heap the caller had live, as the read left it, and as the entry had it
              keep₇ : ∀ l → Live alloc l → readLoc v₇ l ≡ readLoc s l
              keep₇ (AtDynamic hl) lv =
                writeLoc-preserves-other v₆ L (AtDynamic hl) ev (λ e → freshA 0 (subst (Live alloc) (sym e) lv))

              src₇ : FlatPut.Src {FS} {prog} alloc v₇ A (proj₂ x) G.out
              src₇ = FlatPut.src-tr {FS} {prog} (λ l lv → trans (keep₇ l lv) (sym (out-mem fs0 G.out l)))
                       (PairBuildC.src-of-place {FS} {prog} G.place)

              PA = FlatPut.put-run {FS} {prog} A n (suc (suc n)) 1 v₇ A₁ alloc G.out rd N h₇ slot-arg₇ slot-blk₇
                     (FlatAlloc.alloc-bft {FS} N alloc) (FlatAlloc.alloc-bk {FS} N alloc) freshA
                     (FlatAlloc.alloc-live {FS} N alloc) (m≤n⊔m 2 (suc (size A)))
                     (FlatAlloc.alloc-in {FS} N alloc) src₇
              module PA = FlatPut.PutOut PA
              vP = proj₁ (exec-trace (put A n (suc (suc n)) 1) v₇ A₁)
              v₈ = record vP { regs = writeReg (regs vP) Output blk }
              v₉ = proj₁ (exec-abstract mov-to-input v₈ A₁)

              R6 = store-at-slot (suc n) ∷ instr-alloc-heap N ∷ store-at-slot (suc (suc n)) ∷
                   mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              R5 = instr-alloc-heap N ∷ store-at-slot (suc (suc n)) ∷ mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              R4 = store-at-slot (suc (suc n)) ∷ mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              R3 = mov-to-input ∷ load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              R2 = load-from-slot (suc n) ∷ store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              R1 = store-at 0 ∷ (put A n (suc (suc n)) 1 ++ T2)
              R0 = put A n (suc (suc n)) 1 ++ T2

              seg2 : exec-trace S2 u₃ alloc ≡ (v₉ , A₁)
              seg2 =
                trans (exec-trace-cons (load-at 0) R6 u₃ alloc nh)
               (trans (cong (λ r → exec-trace R6 (proj₁ r) (proj₂ r)) (ld 0 u₃ alloc fst-loc ev refl (env-cell-of ea)))
               (trans (exec-trace-cons (store-at-slot (suc n)) R5 v₁ alloc nh)
               (trans (exec-trace-cons (instr-alloc-heap N) R4 v₂ alloc nh)
               (trans (exec-trace-cons (store-at-slot (suc (suc n))) R3 v₃ A₁ nh)
               (trans (exec-trace-cons mov-to-input R2 v₄ A₁ nh)
               (trans (exec-trace-cons (load-from-slot (suc n)) R1 v₅ A₁ nh)
               (trans (cong (λ mv → exec-trace R1 (proj₁ (exec-load-from-slot-with-value mv v₅ A₁))
                                                  (proj₂ (exec-load-from-slot-with-value mv v₅ A₁))) slot-ev)
               (trans (exec-trace-cons (store-at 0) R0 v₆ A₁ nh)
               (trans (cong (λ r → exec-trace R0 (proj₁ r) (proj₂ r)) st0)
               (trans (exec-trace-append (put A n (suc (suc n)) 1) T2 v₇ A₁)
               (trans (cong (λ a → exec-trace T2 vP a) PA.alloc-eq)
               (trans (exec-trace-cons (load-from-slot (suc (suc n))) (mov-to-input ∷ []) vP A₁ PA.live)
               (trans (cong (λ mv → exec-trace (mov-to-input ∷ []) (proj₁ (exec-load-from-slot-with-value mv vP A₁))
                                                                 (proj₂ (exec-load-from-slot-with-value mv vP A₁)))
                            (trans (PA.other (AtStack cf (suc (suc n))) (λ _ _ ())) slot-blk₇))
                      (exec-trace-cons mov-to-input [] v₈ A₁ PA.live))))))))))))))

              at2 : SR.At prog (fpc f4) S2
              at2 j i e = subst (λ p → fetch prog p ≡ just i) shift5
                                (span′ (5 + j) i
                                  (subst (λ t → fetch t j ≡ just i) S2-c (fetch-++-left S2 (instr-call-closure ∷ []) j i e)))
                where shift5 : 5 + j + base ≡ j + fpc f4
                      shift5 = sym (trans (+-suc j _) (cong suc (trans (+-suc j _) (cong suc (trans (+-suc j _)
                                 (cong suc (trans (+-suc j _) (cong suc (+-suc j base)))))))))

              sts2 : All StraightStep S2
              sts2 = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
                     (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
                     ++⁺ (put-All {StraightStep} A n (suc (suc n)) 1 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                         ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷ [])

              evs2 : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) S2
              evs2 = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
                     (λ _ → refl) ∷ (λ _ → refl) ∷
                     ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} A n (suc (suc n)) 1 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                         ((λ _ → refl) ∷ (λ _ → refl) ∷ [])

              he2 : halted (proj₁ (exec-trace S2 u₃ alloc)) ≡ false
              he2 = trans (cong (λ r → halted (proj₁ r)) seg2) PA.live

              fsS = record f4 { floc = v₉ ; falloc = A₁ ; fpc = length S2 + fpc f4 }
              eq2 : SR.after S2 f4 ≡ fsS
              eq2 = cong (λ r → record f4 { floc = proj₁ r ; falloc = proj₂ r ; fpc = length S2 + fpc f4 }) seg2
              run2₀ = SR.straight-steps {prog} S2 f4 sts2 at2 nh he2
              run2 : FlatSteps prog (length S2) f4 fsS
              run2 = subst (FlatSteps prog (length S2) f4) eq2 run2₀

              ------------------------------------------------------------------
              -- 5. the call
              ------------------------------------------------------------------
              -- the setup kept every cell the caller had live
              keepS : ∀ l → Live alloc l → readLoc v₉ l ≡ readLoc s l
              keepS (AtDynamic hl) lv =
                trans (PA.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live alloc) e lv))) (keep₇ (AtDynamic hl) lv)

              at-callinstr : fetch prog (fpc fsS) ≡ just instr-call-closure
              at-callinstr =
                subst (λ p → fetch prog p ≡ just instr-call-closure) shiftc
                  (span′ (5 + length S2) instr-call-closure
                    (trans (cong (λ t → fetch t (length S2)) (sym S2-c))
                           (trans (subst (λ z → fetch (S2 ++ instr-call-closure ∷ []) z ≡ fetch (instr-call-closure ∷ []) 0)
                                         (+-identityʳ (length S2)) (fetch-++-right S2 (instr-call-closure ∷ []) 0))
                                  refl)))
                where shiftc : 5 + length S2 + base ≡ fpc fsS
                      shiftc = sym (trans (+-suc (length S2) _) (cong suc (trans (+-suc (length S2) _) (cong suc
                                 (trans (+-suc (length S2) _) (cong suc (trans (+-suc (length S2) _) (cong suc (+-suc (length S2) base)))))))))

              j   = ClosureValidWF.code-j cvw
              feq = ClosureValidWF.code-found cvw

              code-S : readLoc v₉ (sucLoc fst-loc) ≡ just (SV-Code blbl)
              code-S = trans (keepS (sucLoc fst-loc) (live-suc-of fst-bf)) (ClosureValidWF.code-ptr cvw)
                where live-suc-of : Live alloc fst-loc → Live alloc (sucLoc fst-loc)
                      live-suc-of (BeforeFrontier.heap-before p) = BeforeFrontier.heap-before p

              call-eq : flat-exec-instr instr-call-closure prog fsS
                      ≡ record fsS
                          { falloc = enter-call A₁
                          ; fret   = suc (fpc fsS) ∷ fret fsS
                          ; flink  = just (suc (fpc fsS))
                          ; fpc    = j }
              call-eq = call-at prog fsS (heap-loc cr co) blbl j refl code-S feq

              callFs = flat-exec-instr instr-call-closure prog fsS

              at-call : (P : LocState FS → Set) → P v₉ → P (floc callFs)
              at-call P = subst P (sym (cong floc call-eq))

              -- the callee's input: `[env-word, arg]` at the fresh block
              arg-cell : CellAt {prog = prog} A₁ A (proj₂ x) (sucLoc L) v₉
              arg-cell = PA.cell-at v₉ (λ _ _ → refl)
                           (λ { (AtDynamic hl) lv → PA.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live alloc) e lv)) })

              env-cell : readLoc v₉ L ≡ readLoc s fst-loc
              env-cell = trans (PA.other L (λ j _ e → suc≢0 (cong off-of e)))
                               (trans (readLoc-writeLoc-same v₆ L ev) (sym (env-cell-of ea)))
                where off-of : ValueLocation FS → ℕ
                      off-of (AtDynamic (heap-loc _ o′)) = o′
                      off-of (AtStack _ _) = 0
                      suc≢0 : ∀ {m} → 0 ≡ suc (m + 0) → ⊥
                      suc≢0 ()

              crun : CalleeRunP {prog = prog} {B} (ResultPlaceP {B} (VAt {prog = prog} B))
                       callFs (suc (fpc fsS)) rs (proj₁ x (proj₂ x)) k
              crun = ClosureValidWF.runs cvw callFs A₁ (proj₂ x) L (suc (fpc fsS)) k rs
                       (cong fpc call-eq)
                       (trans (cong (λ st → halted (floc st)) call-eq) PA.live)
                       (cong fret call-eq)
                       (cong falloc call-eq)
                       n≤
                       (FlatAlloc.alloc-bft {FS} N alloc)
                       (FlatAlloc.alloc-bk {FS} N alloc)
                       (λ l b → at-call (λ st → readLoc st l ≡ readLoc s l) (keepS l b))
                       (at-call (λ st → readReg (regs st) Input1 ≡ SV-Ptr L) refl)
                       (FlatAlloc.alloc-live {FS} N alloc 0)
                       (FlatAlloc.alloc-live {FS} N alloc 1)
                       (at-call (λ st → readLoc st L ≡ readLoc s fst-loc) env-cell)
                       (at-call (CellAt {prog = prog} A₁ A (proj₂ x) (sucLoc L)) arg-cell)

              ------------------------------------------------------------------
              -- THE RUN, and the record
              ------------------------------------------------------------------
              SETUP = 1 + (3 + (1 + (length S2 + 1)))

              c-call : FlatSteps prog 1 fsS callFs
              c-call = (PA.live , at-callinstr) ∷ []
              c4 = FlatSteps-++ run2 c-call
              c3 = FlatSteps-++ run-save c4
              c2 = FlatSteps-++ run1 c3

              run-setup : FlatSteps prog SETUP fs0 callFs
              run-setup = FlatSteps-++ G.step c2

              s4 : chain-events c4 ≡ []
              s4 = trans (chain-events-++ run2 c-call)
                         (cong (DL._++ chain-events c-call)
                               (trans (chain-events-subst eq2 run2₀) (SR.straight-silent {prog} S2 f4 sts2 at2 nh he2 evs2)))

              s3 : chain-events c3 ≡ []
              s3 = trans (chain-events-++ run-save c4) s4

              s2 : chain-events c2 ≡ []
              s2 = trans (chain-events-++ run1 c3)
                         (cong₂ DL._++_ (trans (chain-events-subst eq1 run1₀) (SR.straight-silent {prog} T1 g1 sts1 at1 nh he1 evs1)) s3)

              silent-setup : chain-events run-setup ≡ []
              silent-setup = trans (chain-events-++ G.step c2) (cong₂ DL._++_ G.silent s2)

              -- the call returns past the text's end
              at-end-eq : suc (fpc fsS) ≡ length (emitted n l (apply {A} {B})) + base
              at-end-eq =
                trans arith
                      (cong (λ t → length t + base)
                            (sym (trans shape (cong (λ t → get-i A 1 ∷ (T1 ++ instr-save-closure-reg ∷ t)) (sym S2-c)))))
                where
                  open import Data.Nat.Solver using (module +-*-Solver)
                  open +-*-Solver using (solve; _:+_; con; _:=_)
                  arith : suc (length S2 + suc (suc (suc (suc (suc base)))))
                        ≡ length (get-i A 1 ∷ (T1 ++ instr-save-closure-reg ∷ (S2 ++ instr-call-closure ∷ []))) + base
                  arith =
                    trans (solve 2 (λ x y → con 1 :+ (x :+ (con 5 :+ y)) := (con 5 :+ (x :+ con 1)) :+ y) refl (length S2) base)
                          (cong (λ z → suc (suc (suc (suc (suc z)))) + base) (sym (length-++ S2 {instr-call-closure ∷ []})))

              run : FlatSteps prog (SETUP + CalleeRun.steps crun) fs0 (CalleeRun.settle crun)
              run = FlatSteps-++ run-setup (CalleeRun.run crun)

              denot-eq : proj₁ x (proj₂ x) ≡ evalᴰ (apply {A} {B}) x
              denot-eq = refl

              h-eq : SMCore.LocState.ev-log (floc callFs) ≡ SMCore.LocState.ev-log s
              h-eq = trans (log-of run-setup silent-setup) (++-identityʳ _)

              RE : runAt (floc callFs) (⟪ proj₁ x (proj₂ x) ⟫ k) ≡ runAt s (⟪ evalᴰ (apply {A} {B}) x ⟫ k)
              RE = runAt-≡ {st = floc callFs} {st′ = s} h-eq (cong (⟪_⟫ k) denot-eq)

              st-eq : stopsAt (floc callFs) (⟪ proj₁ x (proj₂ x) ⟫ k) ≡ stopsAt s (⟪ evalᴰ (apply {A} {B}) x ⟫ k)
              st-eq = cong (λ r → is-stopped (proj₂ r)) RE

              res-eq : resultAt (floc callFs) (⟪ proj₁ x (proj₂ x) ⟫ k) ≡ resultAt s (⟪ evalᴰ (apply {A} {B}) x ⟫ k)
              res-eq = cong proj₂ RE

              nc′ : NotCut (resultAt s (⟪ evalᴰ (apply {A} {B}) x ⟫ k)) → NotCut (resultAt (floc callFs) (⟪ proj₁ x (proj₂ x) ⟫ k))
              nc′ = subst NotCut (sym res-eq)

              place : ∀ {v r} → resultAt s (⟪ evalᴰ (apply {A} {B}) x ⟫ k) ≡ returns (done v r)
                    → ResultPlace B (CalleeRun.out-mode crun)
                        (falloc (CalleeRun.settle crun)) (CalleeRun.cont-alloc crun)
                        v (floc (CalleeRun.settle crun))
              place p = rp→place (CalleeRun.place crun (trans res-eq p))

              -- the setup's own preservation: slots at and above `n`, the fresh block
              B′ = record alloc { next-slot = n }

              setup-keep : ∀ (loc : ValueLocation FS) → BeforeFrontier B′ loc → readLoc v₉ loc ≡ readLoc s loc
              setup-keep (AtDynamic hl) (BeforeFrontier.heap-before p) = keepS (AtDynamic hl) (BeforeFrontier.heap-before p)
              setup-keep (AtStack fr i) bf =
                trans (PA.other (AtStack fr i) (λ _ _ ()))
               (trans (writeLoc-preserves-other v₆ L (AtStack fr i) ev (λ ()))
               (trans (store-slot-preserves-before (suc (suc n)) v₃ B′ A₁ (AtStack fr i) refl
                         (≤-trans (n≤1+n n) (n≤1+n (suc n))) bf)
               (trans (store-slot-preserves-before (suc n) v₁ B′ alloc (AtStack fr i) refl (n≤1+n n) bf)
               (trans (store-slot-preserves-before n u B′ alloc (AtStack fr i) refl ≤-refl bf)
                      (out-mem fs0 G.out (AtStack fr i))))))

              bf-call : ∀ (m : ℕ) (loc : ValueLocation FS)
                      → BeforeFrontier (record alloc { next-slot = m }) loc
                      → BeforeFrontier (record A₁ { next-slot = m }) loc
              bf-call m = frontier-monotone (record alloc { next-slot = m }) (record A₁ { next-slot = m }) refl ≤-refl (n≤1+n _)

              result : MachineRefinesObsF prog base n l (apply {A} {B}) x s alloc cl rs k
              result = record
                { value-realized =
                    realized (SETUP + CalleeRun.steps crun) (CalleeRun.settle crun)
                             (CalleeRun.out-mode crun) (CalleeRun.cont-alloc crun)
                             run (λ p → CalleeRun.live crun (trans st-eq p))
                             (λ p → trans (CalleeRun.returned crun (trans res-eq p)) at-end-eq)
                             (λ p → proj₁ (CalleeRun.stops crun (trans st-eq p))
                                  , trans (proj₂ (CalleeRun.stops crun (trans st-eq p)))
                                          (chain-left run-setup (trans (cong (λ st → halted (floc st)) call-eq) PA.live)))
                             (λ p → CalleeRun.no-ret crun (trans res-eq p))
                             (λ nc → CalleeRun.no-link crun (nc′ nc))
                             (trans (CalleeRun.log crun) (cong₂ DL._++_ h-eq (cong proj₁ RE)))
                             place
                             (progress-≤ (subst (λ ρ → k ≤ budgetLeft k ρ + chain-ctrls (CalleeRun.run crun)) res-eq (CalleeRun.progress crun))
                                         (ctrls-≤ʳ run-setup (CalleeRun.run crun)))
                             (λ nc fr i bf → mem-pres-apply nc (AtStack fr i) bf)
                             (λ nc hl bf → mem-pres-apply nc (AtDynamic hl) bf)
                             (λ p → CalleeRun.frame-pres crun (trans res-eq p) A₁ (cong falloc call-eq))
                             (λ nc m loc b → CalleeRun.bf-mono crun (nc′ nc) A₁ m (cong falloc call-eq) loc (bf-call m loc b))
                             (λ p → CalleeRun.frames-pres crun (trans res-eq p) A₁ (cong falloc call-eq))
                             (λ nc → bk-trans {a = alloc} {b = A₁} {c = falloc (CalleeRun.settle crun)}
                                       (FlatAlloc.alloc-bk {FS} N alloc)
                                       (CalleeRun.blocks-kept crun (nc′ nc) A₁ (cong falloc call-eq))
                                       (FlatAlloc.alloc-bft {FS} N alloc))
                ; traces-agree = trans (chain-events-++ run-setup (CalleeRun.run crun))
                                       (trans (cong (DL._++ chain-events (CalleeRun.run crun)) silent-setup)
                                              (trans (CalleeRun.events crun) (cong proj₁ RE)))
                }
                where
                  mem-pres-apply : NotCut (resultAt s (⟪ evalᴰ (apply {A} {B}) x ⟫ k))
                                 → ∀ (loc : ValueLocation FS)
                                 → BeforeFrontier (record alloc { next-slot = n }) loc
                                 → SMCore.MemOps.readLoc (floc (CalleeRun.settle crun)) loc ≡ SMCore.MemOps.readLoc s loc
                  mem-pres-apply nc loc b =
                    trans (CalleeRun.mem-pres crun (nc′ nc) A₁ n (cong falloc call-eq) loc (bf-call n loc b))
                          (trans (cong (λ st → SMCore.MemOps.readLoc (floc st) loc) call-eq) (setup-keep loc b))
