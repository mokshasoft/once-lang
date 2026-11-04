-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Call   (plan 0.135 S3, cata M1)
--
-- ONE CALL OF THE ALGEBRA, up to its last row (`cata-call-from`, whose last
-- row `instr-call-closure` is `Run`'s), from where the setup (or a fold
-- round) left `Input1` at the μ and the slots `cl`/`ev` filled. Plan 0.123
-- α2: the argument pair `E * L` is flat, in a FRESH block (plan 0.135 D1a):
--
--     head · store k · alloc (2 ⊔ |E * L|) · store pr          the layer kept, the block
--     put E ev pr 0 · put L k pr |E|                           (env , layer)
--     load cl · mov-to-input · save-closure-reg                fclosure := cl
--     load pr · mov-to-input                                   Input1 := pr
--
-- The puts are `FlatPut`'s, so the pair is valid where it was built; what
-- the caller had live is untouched, the record's code cell among it.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Call (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl using (module CataStepsC; Head; head-instr)
import Once.CCC.Codegen.IRObsCorrect.CataConst.Steps o tbl as Steps
open import Once.CCC.Codegen.IRToTrace o using (cata-call-from)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; module MemOps; module AbstractExec;
         StoredValue; readReg; writeReg; Output; Input1; SV-Code; SV-Ptr;
         store-at-slot; load-from-slot; mov-to-input; instr-alloc-heap; instr-save-closure-reg; instr-call-closure; AbstractInstr)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (LabelId)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy) renaming (_*_ to _*ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (Kind; kind; put; put-k; put-All)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.SMPrimitives
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (z≤n; s≤s; _⊔_)
open import Data.Nat.Properties using (m≤n⊔m; m<m+n; +-monoʳ-<)
import Data.Nat as ℕ

module CataCallC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (SegA; SRun; segA-∘; span-take; span-drop)
  open CataStepsC {FS} using (HeadOK; module HeadOK)
  open MemOps {FS} using (writeLoc-preserves-other; writeLoc-read-same-stack)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open FlatEventTrace {FS} using (chain-events-subst)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)
  module SR = StraightRunAPI {FS}

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    off-of : ValueLocation FS → ℕ
    off-of (AtDynamic (heap-loc _ o′)) = o′
    off-of (AtStack _ _) = 0

  -- the head row is straight and silent at either head
  head-st : ∀ (h : Head) → StraightStep (head-instr h)
  head-st Steps.h-mov = λ _ _ → refl
  head-st Steps.h-box = λ _ _ → refl

  head-ev : ∀ (h : Head) → ∀ fs′ → event-of (head-instr h) fs′ ≡ []
  head-ev Steps.h-mov = λ _ → refl
  head-ev Steps.h-box = λ _ → refl

  head-eq : ∀ (h : Head) (s : LocState FS) (a : AllocState {FS})
          → exec-abstract (head-instr h) s a ≡ (proj₁ (exec-abstract (head-instr h) s a) , a)
  head-eq Steps.h-mov s a = refl
  head-eq Steps.h-box s a = refl

  -- the call's rows, with the layer's put at its IR type
  callA : AbstractInstr → IRTy → IRTy → ℕ → AbstractTrace
  callA i0 E L n = i0 ∷ store-at-slot (n ℕ.+ 1) ∷ instr-alloc-heap (2 ⊔ size (E *ᵀ L)) ∷ store-at-slot (n ℕ.+ 3) ∷
                   (put E (n ℕ.+ 2) (n ℕ.+ 3) 0 DL.++ (put L (n ℕ.+ 1) (n ℕ.+ 3) (size E) DL.++ load-from-slot n ∷ mov-to-input ∷ []))

  callB : ℕ → AbstractTrace
  callB n = load-from-slot (n ℕ.+ 3) ∷ mov-to-input ∷ []

  callK : AbstractInstr → IRTy → IRTy → ℕ → AbstractTrace
  callK i0 E L n = callA i0 E L n DL.++ (instr-save-closure-reg ∷ callB n)

  call-shape : ∀ (i0 : AbstractInstr) (E L : IRTy) (lk : Kind) (ls : ℕ) (n : ℕ) → lk ≡ kind L → ls ≡ size L
             → cata-call-from i0 E lk ls n (n ℕ.+ 1) (n ℕ.+ 2) (n ℕ.+ 3) ≡ callK i0 E L n DL.++ (instr-call-closure ∷ [])
  call-shape i0 E L lk ls n refl refl =
    cong (λ t → i0 ∷ store-at-slot (n ℕ.+ 1) ∷ instr-alloc-heap (2 ⊔ size (E *ᵀ L)) ∷ store-at-slot (n ℕ.+ 3) ∷ t)
      (sym (trans (++-assoc (X DL.++ (Y DL.++ Z₁)) W V)
           (trans (++-assoc X (Y DL.++ Z₁) (W DL.++ V))
                  (cong (X DL.++_) (++-assoc Y Z₁ (W DL.++ V))))))
    where X = put E (n ℕ.+ 2) (n ℕ.+ 3) 0
          Y = put L (n ℕ.+ 1) (n ℕ.+ 3) (size E)
          Z₁ = load-from-slot n ∷ mov-to-input ∷ []
          W = instr-save-closure-reg ∷ callB n
          V = instr-call-closure ∷ []

  -- WHAT THE CALL ROWS HAND ON (up to the call itself)
  record CallOut (n : ℕ) (prog : AbstractTrace) (σ : FlatState) (a₀ : AllocState {FS})
                 (hc : HeapLocation) (lbl : LabelId) (E L : IRTy) (env : ⟦ E ⟧) (lay : ⟦ L ⟧) (CK : ℕ) : Set where
    field
      w      : FlatState
      runK   : SRun prog CK σ w
      seg    : SegA a₀ n σ w
      nh     : halted (floc w) ≡ false
      pc     : fpc w ≡ CK ℕ.+ fpc σ
      ret    : fret w ≡ fret σ
      lnk    : flink w ≡ flink σ
      clo    : fclosure w ≡ SV-Ptr (AtDynamic hc)
      hp     : HeapLocation
      ref-hp : ref-id (heap-ref hp) ≡ next-heap-ref (falloc σ)
      hr     : next-heap-ref (falloc w) ≡ suc (next-heap-ref (falloc σ))
      cf     : current-frame (falloc w) ≡ current-frame (falloc σ)
      inp    : readReg (regs (floc w)) Input1 ≡ SV-Ptr (AtDynamic hp)
      -- the argument pair, valid in its fresh block
      pairV  : ValidAtWF {prog = prog} Heap (falloc w) {E *ᵀ L} (env , lay) (AtDynamic hp) (floc w)
      lhp    : Live (falloc w) (AtDynamic hp)
      code   : readLoc (floc w) (AtDynamic (sucHL hc)) ≡ just (SV-Code lbl)
      cl     : readLoc (floc w) (AtStack (current-frame (falloc σ)) n) ≡ just (SV-Ptr (AtDynamic hc))
      bk     : BlocksKept (falloc σ) (falloc w)
      keep   : ∀ l → Live (falloc σ) l → readLoc (floc w) l ≡ readLoc (floc σ) l

  module Call (h : Head) (E L : IRTy) (n : ℕ) (prog : AbstractTrace) (σ : FlatState) (a₀ : AllocState {FS})
              (span : SpanAt prog (fpc σ) (callK (head-instr h) E L n))
              (nh0 : halted (floc σ) ≡ false)
              (hc : HeapLocation) (lbl : LabelId) {env : ⟦ E ⟧} {lay : ⟦ L ⟧} (env-sv lay-sv : StoredValue FS)
              (hd : HeadOK prog σ h lay-sv)
              (cl0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) n) ≡ just (SV-Ptr (AtDynamic hc)))
              (ev0 : readLoc (floc σ) (AtStack (current-frame (falloc σ)) (n ℕ.+ 2)) ≡ just env-sv)
              (code0 : readLoc (floc σ) (AtDynamic (sucHL hc)) ≡ just (SV-Code lbl))
              (lhc : Live (falloc σ) (AtDynamic (sucHL hc)))
              (srcE : FlatPut.Src {FS} {prog} a₀ (floc σ) E env env-sv)
              (srcL : FlatPut.Src {FS} {prog} a₀ (floc σ) L lay lay-sv)
              (bft₀ : ∀ l → Live a₀ l → Live (falloc σ) l) (bk₀ : BlocksKept a₀ (falloc σ))
              (cf0 : current-frame (falloc σ) ≡ current-frame a₀)
              where

    open FlatPut {FS} {prog} using (src-tr; put-run; PutOut; dst)
    module HD = HeadOK hd

    s  = floc σ
    a  = falloc σ
    cf = current-frame a
    k  = n ℕ.+ 1
    ev = n ℕ.+ 2
    pr = n ℕ.+ 3
    i0 = head-instr h
    N  = 2 ⊔ size (E *ᵀ L)
    A₁ = FlatAlloc.alloc-after {FS} N a
    rd = FlatAlloc.fresh-ref {FS} a
    hp : HeapLocation
    hp = heap-loc rd 0
    P : ValueLocation FS
    P = AtDynamic hp
    blk : StoredValue FS
    blk = SV-Ptr P
    tag-hc : StoredValue FS
    tag-hc = SV-Ptr (AtDynamic hc)

    -- (1) the rows before the puts
    x₀ = proj₁ (exec-abstract i0 s a)
    x₁ = proj₁ (exec-abstract (store-at-slot k) x₀ a)
    x₂ = proj₁ (exec-abstract (instr-alloc-heap N) x₁ a)
    x₃ = proj₁ (exec-abstract (store-at-slot pr) x₂ A₁)

    h₀ : halted x₀ ≡ false
    h₀ = HD.nh1 nh0

    lay-out : readReg (regs x₀) Output ≡ lay-sv
    lay-out = HD.out1

    keep₀ : ∀ l → readLoc x₀ l ≡ readLoc s l
    keep₀ l = mem-untouched i0 s a l HD.nhw HD.nws

    R0 : AbstractTrace
    R0 = put E ev pr 0 DL.++ (put L k pr (size E) DL.++ load-from-slot n ∷ mov-to-input ∷ [])

    prefix : exec-trace (callA i0 E L n) s a ≡ exec-trace R0 x₃ A₁
    prefix = trans (exec-trace-cons i0 _ s a nh0)
            (trans (cong (λ r → exec-trace (store-at-slot k ∷ instr-alloc-heap N ∷ store-at-slot pr ∷ R0) (proj₁ r) (proj₂ r)) (head-eq h s a))
            (trans (exec-trace-cons (store-at-slot k) _ x₀ a h₀)
            (trans (exec-trace-cons (instr-alloc-heap N) _ x₁ a h₀)
                   (exec-trace-cons (store-at-slot pr) R0 x₂ A₁ h₀))))

    ne-k-ev : AtStack cf k ≢ AtStack cf ev
    ne-k-ev e′ = <-irrefl (cong slot-of e′) (+-monoʳ-< n (s≤s (s≤s z≤n)))
    ne-pr-ev : AtStack cf pr ≢ AtStack cf ev
    ne-pr-ev e′ = <-irrefl (sym (cong slot-of e′)) (+-monoʳ-< n (s≤s (s≤s (s≤s z≤n))))
    ne-pr-k : AtStack cf pr ≢ AtStack cf k
    ne-pr-k e′ = <-irrefl (sym (cong slot-of e′)) (+-monoʳ-< n (s≤s (s≤s z≤n)))
    ne-k-n : AtStack cf k ≢ AtStack cf n
    ne-k-n e′ = <-irrefl (sym (cong slot-of e′)) (m<m+n n (s≤s z≤n))
    ne-pr-n : AtStack cf pr ≢ AtStack cf n
    ne-pr-n e′ = <-irrefl (sym (cong slot-of e′)) (m<m+n n (s≤s z≤n))

    eSlot₃ : readLoc x₃ (AtStack cf ev) ≡ just env-sv
    eSlot₃ = trans (writeLoc-preserves-other x₂ (AtStack cf pr) (AtStack cf ev) blk ne-pr-ev)
            (trans (writeLoc-preserves-other x₀ (AtStack cf k) (AtStack cf ev) (readReg (regs x₀) Output) ne-k-ev)
            (trans (keep₀ (AtStack cf ev)) ev0))

    lSlot₃ : readLoc x₃ (AtStack cf k) ≡ just lay-sv
    lSlot₃ = trans (writeLoc-preserves-other x₂ (AtStack cf pr) (AtStack cf k) blk ne-pr-k)
            (trans (writeLoc-read-same-stack x₀ cf k (readReg (regs x₀) Output)) (cong just lay-out))

    pSlot₃ : readLoc x₃ (AtStack cf pr) ≡ just blk
    pSlot₃ = writeLoc-read-same-stack x₂ cf pr blk

    cSlot₃ : readLoc x₃ (AtStack cf n) ≡ just tag-hc
    cSlot₃ = trans (writeLoc-preserves-other x₂ (AtStack cf pr) (AtStack cf n) blk ne-pr-n)
            (trans (writeLoc-preserves-other x₀ (AtStack cf k) (AtStack cf n) (readReg (regs x₀) Output) ne-k-n)
            (trans (keep₀ (AtStack cf n)) cl0))

    keep₃ : ∀ l → Live a l → readLoc x₃ l ≡ readLoc s l
    keep₃ (AtDynamic hl) _ = keep₀ (AtDynamic hl)

    freshA : ∀ o′ → Live a (AtDynamic (heap-loc rd o′)) → ⊥
    freshA o′ = FlatAlloc.alloc-fresh {FS} a o′
    fresh₀ : ∀ o′ → Live a₀ (AtDynamic (heap-loc rd o′)) → ⊥
    fresh₀ o′ lv = freshA o′ (bft₀ _ lv)

    S≤N : size E ℕ.+ size L ≤ N
    S≤N = m≤n⊔m 2 (size E ℕ.+ size L)

    bft₁ : ∀ l → Live a₀ l → Live A₁ l
    bft₁ l lv = FlatAlloc.alloc-bft {FS} N a l (bft₀ l lv)
    bk₁ : BlocksKept a₀ A₁
    bk₁ l lv ib = FlatAlloc.alloc-bk {FS} N a l (bft₀ l lv) (bk₀ l lv ib)

    -- (2) the two puts
    PE = put-run E ev pr 0 x₃ A₁ a₀ env-sv rd N h₀ eSlot₃ pSlot₃ bft₁ bk₁ fresh₀ (FlatAlloc.alloc-live {FS} N a)
           (≤-trans (m≤m+n (size E) (size L)) S≤N) (FlatAlloc.alloc-in {FS} N a)
           (src-tr (λ l lv → keep₃ l (bft₀ l lv)) srcE)
    module PE = PutOut PE
    sE = proj₁ (exec-trace (put E ev pr 0) x₃ A₁)

    PL = put-run L k pr (size E) sE A₁ a₀ lay-sv rd N PE.live
           (trans (PE.other (AtStack cf k) (λ j _ ())) lSlot₃)
           (trans (PE.other (AtStack cf pr) (λ j _ ())) pSlot₃)
           bft₁ bk₁ fresh₀ (FlatAlloc.alloc-live {FS} N a) S≤N (FlatAlloc.alloc-in {FS} N a)
           (src-tr (λ { (AtDynamic hl) lv → trans (PE.other (AtDynamic hl) (λ j _ e′ → fresh₀ _ (subst (Live a₀) e′ lv)))
                                                  (keep₃ (AtDynamic hl) (bft₀ _ lv)) }) srcL)
    module PL = PutOut PL
    sL = proj₁ (exec-trace (put L k pr (size E)) sE A₁)

    -- (3) the closure record to Input1
    y₁ = record sL { regs = writeReg (regs sL) Output tag-hc }
    y₂ = proj₁ (exec-abstract mov-to-input y₁ A₁)

    cSlotL : readLoc sL (AtStack cf n) ≡ just tag-hc
    cSlotL = trans (PL.other (AtStack cf n) (λ j _ ())) (trans (PE.other (AtStack cf n) (λ j _ ())) cSlot₃)

    lastA : exec-trace (load-from-slot n ∷ mov-to-input ∷ []) sL A₁ ≡ (y₂ , A₁)
    lastA = trans (exec-trace-cons (load-from-slot n) _ sL A₁ PL.live)
           (trans (cong (λ r → exec-trace (mov-to-input ∷ []) (proj₁ r) (proj₂ r))
                        (cong (λ mv → exec-load-from-slot-with-value mv sL A₁) cSlotL))
                  (exec-trace-cons mov-to-input [] y₁ A₁ PL.live))

    wholeA : exec-trace (callA i0 E L n) s a ≡ (y₂ , A₁)
    wholeA =
      trans prefix
     (trans (exec-trace-append (put E ev pr 0) (put L k pr (size E) DL.++ load-from-slot n ∷ mov-to-input ∷ []) x₃ A₁)
     (trans (cong (λ x → exec-trace (put L k pr (size E) DL.++ load-from-slot n ∷ mov-to-input ∷ []) sE x) PE.alloc-eq)
     (trans (exec-trace-append (put L k pr (size E)) (load-from-slot n ∷ mov-to-input ∷ []) sE A₁)
     (trans (cong (λ x → exec-trace (load-from-slot n ∷ mov-to-input ∷ []) sL x) PL.alloc-eq)
            lastA))))

    LA : ℕ
    LA = DL.length (callA i0 E L n)

    fA : FlatState
    fA = record σ { floc = y₂ ; falloc = A₁ ; fpc = LA ℕ.+ fpc σ }

    private
      stsA : All StraightStep (callA i0 E L n)
      stsA = head-st h ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
             ++⁺ (put-All {StraightStep} E ev pr 0 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                 (++⁺ (put-All {StraightStep} L k pr (size E) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                      ((λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []))
      evsA : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (callA i0 E L n)
      evsA = head-ev h ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
             ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} E ev pr 0 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                 (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} L k pr (size E) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                      ((λ _ → refl) ∷ (λ _ → refl) ∷ []))
      atA : SR.At prog (fpc σ) (callA i0 E L n)
      atA = span-take prog (callA i0 E L n) {instr-save-closure-reg ∷ callB n} (fpc σ) span
      heA : halted (proj₁ (exec-trace (callA i0 E L n) s a)) ≡ false
      heA = trans (cong (λ r → halted (proj₁ r)) wholeA) PL.live
      runA₀ = SR.straight-steps {prog} (callA i0 E L n) σ stsA atA nh0 heA
      eqA : SR.after (callA i0 E L n) σ ≡ fA
      eqA = cong (λ r → record σ { floc = proj₁ r ; falloc = proj₂ r ; fpc = LA ℕ.+ fpc σ }) wholeA

    runA : FlatSteps prog LA σ fA
    runA = subst (FlatSteps prog LA σ) eqA runA₀

    silA : chain-events runA ≡ []
    silA = trans (chain-events-subst eqA runA₀) (SR.straight-silent {prog} (callA i0 E L n) σ stsA atA nh0 heA evsA)

    -- (4) the closure register
    fS : FlatState
    fS = flat-exec-instr instr-save-closure-reg prog fA

    spRest : SpanAt prog (LA ℕ.+ fpc σ) (instr-save-closure-reg ∷ callB n)
    spRest = span-drop prog (callA i0 E L n) {instr-save-closure-reg ∷ callB n} (fpc σ) span

    runS1 : FlatSteps prog 1 fA fS
    runS1 = (PL.live , spRest 0 _ refl) ∷ []

    -- (5) the pair to Input1
    z₁ = record y₂ { regs = writeReg (regs y₂) Output blk }
    z₂ = proj₁ (exec-abstract mov-to-input z₁ A₁)

    pSlotY : readLoc y₂ (AtStack cf pr) ≡ just blk
    pSlotY = trans (PL.other (AtStack cf pr) (λ j _ ())) (trans (PE.other (AtStack cf pr) (λ j _ ())) pSlot₃)

    wholeB : exec-trace (callB n) y₂ A₁ ≡ (z₂ , A₁)
    wholeB = trans (exec-trace-cons (load-from-slot pr) _ y₂ A₁ PL.live)
            (trans (cong (λ r → exec-trace (mov-to-input ∷ []) (proj₁ r) (proj₂ r))
                         (cong (λ mv → exec-load-from-slot-with-value mv y₂ A₁) pSlotY))
                   (exec-trace-cons mov-to-input [] z₁ A₁ PL.live))

    w : FlatState
    w = record fS { floc = z₂ ; falloc = A₁ ; fpc = 2 ℕ.+ fpc fS }

    private
      stsB : All StraightStep (callB n)
      stsB = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
      evsB : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (callB n)
      evsB = (λ _ → refl) ∷ (λ _ → refl) ∷ []
      atB : SR.At prog (fpc fS) (callB n)
      atB = span-drop prog (instr-save-closure-reg ∷ []) {callB n} (LA ℕ.+ fpc σ) spRest
      heB : halted (proj₁ (exec-trace (callB n) (floc fS) (falloc fS))) ≡ false
      heB = trans (cong (λ r → halted (proj₁ r)) wholeB) PL.live
      runB₀ = SR.straight-steps {prog} (callB n) fS stsB atB PL.live heB
      eqB : SR.after (callB n) fS ≡ w
      eqB = cong (λ r → record fS { floc = proj₁ r ; falloc = proj₂ r ; fpc = 2 ℕ.+ fpc fS }) wholeB

    runB : FlatSteps prog 2 fS w
    runB = subst (FlatSteps prog 2 fS) eqB runB₀

    silB : chain-events runB ≡ []
    silB = trans (chain-events-subst eqB runB₀) (SR.straight-silent {prog} (callB n) fS stsB atB PL.live heB evsB)

    CK : ℕ
    CK = LA ℕ.+ (1 ℕ.+ 2)

    runK : FlatSteps prog CK σ w
    runK = FlatSteps-++ runA (FlatSteps-++ runS1 runB)

    evK : chain-events runK ≡ []
    evK = trans (chain-events-++ runA (FlatSteps-++ runS1 runB))
                (cong₂ DL._++_ silA (trans (chain-events-++ runS1 runB) (cong₂ DL._++_ refl silB)))

    -- the pair, in its block
    apart : ∀ j j′ → j < size E → (0 ℕ.+ j) ℕ.+ 0 ≡ (size E ℕ.+ j′) ℕ.+ 0 → ⊥
    apart j j′ j< e′ =
      <-irrefl refl (<-≤-trans j< (≤-trans (m≤m+n (size E) j′)
        (≤-reflexive (sym (trans (sym (+-identityʳ j)) (trans e′ (+-identityʳ (size E ℕ.+ j′))))))))

    keepZ : ∀ l → readLoc z₂ l ≡ readLoc sL l
    keepZ l = readLoc-stack-heap-eq z₂ sL l refl refl

    cellE : CellAt {prog = prog} A₁ E env P z₂
    cellE = PE.cell-at z₂
              (λ j j< → trans (keepZ (dst rd 0 j)) (PL.other (dst rd 0 j) (λ j′ _ e′ → apart j j′ j< (cong off-of e′))))
              (λ { (AtDynamic hl) lv → trans (keepZ (AtDynamic hl))
                    (trans (PL.other (AtDynamic hl) (λ j _ e′ → fresh₀ _ (subst (Live a₀) e′ lv)))
                           (PE.other (AtDynamic hl) (λ j _ e′ → fresh₀ _ (subst (Live a₀) e′ lv)))) })

    cellL : CellAt {prog = prog} A₁ L lay (SMCore.offsetLoc P (size E)) z₂
    cellL = PL.cell-at z₂ (λ j _ → keepZ (dst rd (size E) j))
              (λ { (AtDynamic hl) lv → trans (keepZ (AtDynamic hl)) (PL.other (AtDynamic hl) (λ j _ e′ → fresh₀ _ (subst (Live a₀) e′ lv))) })

    keepAll : ∀ l → Live a l → readLoc z₂ l ≡ readLoc s l
    keepAll (AtDynamic hl) lv =
      trans (keepZ (AtDynamic hl))
     (trans (PL.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv)))
     (trans (PE.other (AtDynamic hl) (λ j _ e′ → freshA _ (subst (Live a) e′ lv)))
            (keep₃ (AtDynamic hl) lv)))

    below : ∀ loc → BeforeFrontier (record a₀ { next-slot = n }) loc → readLoc z₂ loc ≡ readLoc s loc
    below (AtDynamic hl) (BeforeFrontier.heap-before p′) = keepAll (AtDynamic hl) (bft₀ _ (BeforeFrontier.heap-before p′))
    below (AtStack fr j) bf =
      trans (keepZ (AtStack fr j))
     (trans (PL.other (AtStack fr j) (λ _ _ ()))
     (trans (PE.other (AtStack fr j) (λ _ _ ()))
     (trans (store-slot-preserves-before pr x₂ (record a₀ { next-slot = n }) A₁ (AtStack fr j) cf0 (m≤m+n n 3) bf)
     (trans (store-slot-preserves-before k x₀ (record a₀ { next-slot = n }) a (AtStack fr j) cf0 (m≤m+n n 1) bf)
            (keep₀ (AtStack fr j))))))

    out : CallOut n prog σ a₀ hc lbl E L env lay CK
    out = record
      { w      = w
      ; runK   = runK , evK , trans (log-of runK evK) (++-identityʳ _)
      ; seg    = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }
      ; nh     = PL.live
      ; pc     = arith LA (fpc σ)
      ; ret    = refl
      ; lnk    = refl
      ; clo    = refl
      ; hp     = hp
      ; ref-hp = refl
      ; hr     = refl
      ; cf     = refl
      ; inp    = refl
      ; pairV  = valid-pair-wf tt (FlatAlloc.alloc-live {FS} N a 1) cellE cellL
      ; lhp    = FlatAlloc.alloc-live {FS} N a 0
      ; code   = trans (keepAll _ lhc) code0
      ; cl     = trans (keepZ (AtStack cf n)) cSlotL
      ; bk     = FlatAlloc.alloc-bk {FS} N a
      ; keep   = keepAll
      }
      where open import Data.Nat.Solver using (module +-*-Solver)
            open +-*-Solver using (solve; _:+_; con; _:=_)
            arith : ∀ x f → suc (suc (suc (x ℕ.+ f))) ≡ (x ℕ.+ (1 ℕ.+ 2)) ℕ.+ f
            arith = solve 2 (λ x f → con 3 :+ (x :+ f) := (x :+ (con 1 :+ con 2)) :+ f) refl
