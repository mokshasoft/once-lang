-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataConst.Setup   (plan 0.135 S3, cata M1)
--
-- THE CATA'S SETUP ROWS (`cata-call-setup E cl k ev body`), run from any
-- state whose `Input1` points at the input pair `(env , μ)`, which is flat
-- (plan 0.123 α2): the environment's words at word 0, the μ's pointer at
-- word `size E`.
--
--     get E 0 · store ev · load-at |E| · store k      split the pair
--     alloc 2 · store cl · mov-to-input · tag 0 · store-at 0 ·
--       code-addr body · store-at 1                    cl := [0 , body]
--     load k · mov-to-input                            Input1 := μ
--
-- What the call rows need afterwards: the closure record's code cell, the
-- environment's register form in slot `ev` (as a value to put), the record
-- pointer in `cl`, and `Input1` holding the μ's pointer. Everything the
-- caller has live is untouched (`seg`): the three slots are at or above the
-- frontier and the two heap writes land in the block this run allocated.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataConst.Setup (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRToTrace o using (cata-call-setup)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AllocState; module AllocState; module MemOps; module AbstractExec;
         StoredValue; readReg; writeReg; Output; Input1; SV-Code; SV-Ptr; SV-Tag; sv-as-loc; offsetLoc;
         store-at-slot; load-from-slot; mov-to-input; instr-alloc-heap; instr-load-code-addr; instr-load-tag-lit;
         load-at; store-at)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Label using (ℓ)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; sucHL; module HeapLocation; module HeapRef)
open HeapLocation using (heap-ref)
open HeapRef using (ref-id)
open import Once.IRTy using (IRTy)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (get)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.SMPrimitives
open import Once.CCC.Codegen.IRObsCorrect.Get o tbl using (module GetC)
open import Once.CCC.Codegen.IRObsCorrect.Pair.Build o tbl using (module PairBuildC)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Product using (Σ)
open import Data.Nat.Properties using (m<m+n; +-monoʳ-<)
import Data.Nat as ℕ

module CataSetupC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS} using (SegA; SRun; span-drop)
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack; writeLoc-regs; writeLoc-halted)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  open GetC {FS} using (GetOut; module GetOut; get-run; setOut; out-mem; get-len)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame; block-size)
  module SR = StraightRunAPI {FS}

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

  -- WHAT THE SETUP HANDS ON, as an opaque bundle: a consumer sees the last
  -- state only through these facts.
  record SetupOut (E : IRTy) (env : ⟦ E ⟧) (n l1 : ℕ) (prog : AbstractTrace) (σ : FlatState) (μ-sv : StoredValue FS) : Set where
    field
      u      : FlatState
      runS   : SRun prog 13 σ u
      seg    : SegA (falloc σ) n σ u
      nh     : halted (floc u) ≡ false
      pc     : fpc u ≡ 13 + fpc σ
      ret    : fret u ≡ fret σ
      clo    : fclosure u ≡ fclosure σ
      lnk    : flink u ≡ flink σ
      hc     : HeapLocation
      ref-hc : ref-id (heap-ref hc) ≡ next-heap-ref (falloc σ)
      inμ    : readReg (regs (floc u)) Input1 ≡ μ-sv
      cl     : readLoc (floc u) (AtStack (current-frame (falloc u)) n) ≡ just (SV-Ptr (AtDynamic hc))
      env-sv : StoredValue FS
      ev     : readLoc (floc u) (AtStack (current-frame (falloc u)) (n ℕ.+ 2)) ≡ just env-sv
      -- the environment, as a value to put (valid at the caller's allocator)
      src    : FlatPut.Src {FS} {prog} (falloc σ) (floc u) E env env-sv
      code   : readLoc (floc u) (AtDynamic (sucHL hc)) ≡ just (SV-Code (ℓ o l1))
      lhc    : Live (falloc u) (AtDynamic (sucHL hc))
      cf     : current-frame (falloc u) ≡ current-frame (falloc σ)
      hr     : next-heap-ref (falloc u) ≡ suc (next-heap-ref (falloc σ))
      -- D381: the caller's blocks keep their sizes; the record's block is fresh
      bk     : BlocksKept (falloc σ) (falloc u)
      keep   : ∀ l → Live (falloc σ) l → readLoc (floc u) l ≡ readLoc (floc σ) l

  module Setup (E : IRTy) (n l1 : ℕ) (prog : AbstractTrace) (σ : FlatState)
               (span : SpanAt prog (fpc σ) (cata-call-setup E n (n ℕ.+ 1) (n ℕ.+ 2) l1))
               (nh0 : halted (floc σ) ≡ false)
               {env : ⟦ E ⟧} (pl : ValueLocation FS)
               (rdi : readReg (regs (floc σ)) Input1 ≡ SV-Ptr pl)
               (lpl : Live (falloc σ) pl)
               (cE : CellAt {prog = prog} (falloc σ) E env (offsetLoc pl 0) (floc σ))
               (μ-sv : StoredValue FS)
               (cμ : readLoc (floc σ) (offsetLoc pl (size E)) ≡ just μ-sv)
               where

    a  = falloc σ
    cf₀ = current-frame a
    ev k cl : ℕ
    cl = n
    k  = n ℕ.+ 1
    ev = n ℕ.+ 2
    lbl = ℓ o l1

    T12 : AbstractTrace
    T12 = store-at-slot ev ∷ load-at (size E) ∷ store-at-slot k ∷ instr-alloc-heap 2 ∷ store-at-slot cl ∷
          mov-to-input ∷ instr-load-tag-lit 0 ∷ store-at 0 ∷ instr-load-code-addr lbl ∷ store-at 1 ∷
          load-from-slot k ∷ mov-to-input ∷ []

    -- (1) the environment, read
    g : GetOut {prog = prog} E env σ _
    g = get-run E 0 σ pl nh0 (λ i e′ → span 0 i (fetch-++-left (get E 0) T12 0 i e′)) rdi lpl cE
    gs = setOut σ (GetOut.out g)
    wE = GetOut.out g

    sp12 : SR.At prog (fpc gs) T12
    sp12 = subst (λ z → SpanAt prog (z ℕ.+ fpc σ) T12) (get-len E 0) (span-drop prog (get E 0) {T12} (fpc σ) span)

    -- (2) the twelve rows
    s  = floc gs
    v1 = proj₁ (exec-abstract (store-at-slot ev) s a)
    v2 = record v1 { regs = writeReg (regs v1) Output μ-sv }
    v3 = proj₁ (exec-abstract (store-at-slot k) v2 a)
    A₁ = FlatAlloc.alloc-after {FS} 2 a
    rd = FlatAlloc.fresh-ref {FS} a
    hc : HeapLocation
    hc = heap-loc rd 0
    H  : ValueLocation FS
    H  = AtDynamic hc
    H1 : ValueLocation FS
    H1 = AtDynamic (sucHL hc)
    v4 = proj₁ (exec-abstract (instr-alloc-heap 2) v3 a)
    v5 = proj₁ (exec-abstract (store-at-slot cl) v4 A₁)
    v6 = proj₁ (exec-abstract mov-to-input v5 A₁)
    v7 = proj₁ (exec-abstract (instr-load-tag-lit 0) v6 A₁)
    tag : StoredValue FS
    tag = SV-Tag 0
    v8 = writeLoc v7 H tag
    code : StoredValue FS
    code = SV-Code lbl
    v9 = proj₁ (exec-abstract (instr-load-code-addr lbl) v8 A₁)
    v10 = writeLoc v9 H1 code
    v11 = record v10 { regs = writeReg (regs v10) Output μ-sv }
    v12 = proj₁ (exec-abstract mov-to-input v11 A₁)

    dyn : ∀ {l} → Live a l → Σ HeapLocation (λ hl → l ≡ AtDynamic hl)
    dyn {AtDynamic hl} _ = hl , refl

    in1-v1 : readReg (regs v1) Input1 ≡ SV-Ptr pl
    in1-v1 = trans (cong (λ r → readReg r Input1) (writeLoc-regs s (AtStack cf₀ ev) wE)) rdi

    rμ-v1 : readLoc v1 (offsetLoc pl (size E)) ≡ just μ-sv
    rμ-v1 with dyn lpl
    ... | hl , refl = cμ

    ld2 : exec-abstract (load-at (size E)) v1 a ≡ (v2 , a)
    ld2 = trans (cong (λ x → (SMCore.ExecFinal.exec-load-at-resolved {FS} (size E) Output (sv-as-loc x) v1 , a)) in1-v1)
                (cong (λ m → (SMCore.ExecFinal.exec-load-with-value {FS} Output m v1 , a)) rμ-v1)

    ib₀ : InBlk A₁ H
    ib₀ = FlatAlloc.alloc-in {FS} 2 a 0 (s≤s z≤n)
    ib₁ : InBlk A₁ H1
    ib₁ = FlatAlloc.alloc-in {FS} 2 a 1 (s≤s (s≤s z≤n))

    st0 : exec-abstract (store-at 0) v7 A₁ ≡ (v8 , A₁)
    st0 = cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb H tag v7 , A₁)) ib₀

    in1-v9 : readReg (regs v9) Input1 ≡ SV-Ptr H
    in1-v9 = cong (λ r → readReg r Input1) (writeLoc-regs v7 H tag)

    st1 : exec-abstract (store-at 1) v9 A₁ ≡ (v10 , A₁)
    st1 = trans (cong (λ ml → (SMCore.ExecFinal.exec-store-at-resolved {FS} (block-size A₁) 1 ml code v9 , A₁)) (cong sv-as-loc in1-v9))
                (cong (λ bb → (SMCore.ExecFinal.exec-store-in-block {FS} bb H1 code v9 , A₁)) ib₁)

    kslot-v10 : readLoc v10 (AtStack cf₀ k) ≡ just μ-sv
    kslot-v10 = trans (writeLoc-preserves-other v9 H1 (AtStack cf₀ k) code (λ ()))
               (trans (writeLoc-preserves-other v7 H (AtStack cf₀ k) tag (λ ()))
               (trans (writeLoc-preserves-other v4 (AtStack cf₀ cl) (AtStack cf₀ k) (SV-Ptr H)
                         (λ e′ → <-irrefl (cong slot-of e′) (m<m+n n (s≤s z≤n))))
                      (writeLoc-read-same-stack v2 cf₀ k μ-sv)))

    ld11 : exec-abstract (load-from-slot k) v10 A₁ ≡ (v11 , A₁)
    ld11 = cong (λ mv → exec-load-from-slot-with-value mv v10 A₁) kslot-v10

    h8 : halted v8 ≡ false
    h8 = trans (writeLoc-halted v7 H tag) nh0
    h10 : halted v10 ≡ false
    h10 = trans (writeLoc-halted v9 H1 code) h8

    whole : exec-trace T12 s a ≡ (v12 , A₁)
    whole =
      trans (exec-trace-cons (store-at-slot ev) _ s a nh0)
     (trans (exec-trace-cons (load-at (size E)) _ v1 a nh0)
     (trans (cong (λ r → exec-trace (store-at-slot k ∷ instr-alloc-heap 2 ∷ store-at-slot cl ∷ mov-to-input ∷ instr-load-tag-lit 0 ∷
                                      store-at 0 ∷ instr-load-code-addr lbl ∷ store-at 1 ∷ load-from-slot k ∷ mov-to-input ∷ [])
                                     (proj₁ r) (proj₂ r)) ld2)
     (trans (exec-trace-cons (store-at-slot k) _ v2 a nh0)
     (trans (exec-trace-cons (instr-alloc-heap 2) _ v3 a nh0)
     (trans (exec-trace-cons (store-at-slot cl) _ v4 A₁ nh0)
     (trans (exec-trace-cons mov-to-input _ v5 A₁ nh0)
     (trans (exec-trace-cons (instr-load-tag-lit 0) _ v6 A₁ nh0)
     (trans (exec-trace-cons (store-at 0) _ v7 A₁ nh0)
     (trans (cong (λ r → exec-trace (instr-load-code-addr lbl ∷ store-at 1 ∷ load-from-slot k ∷ mov-to-input ∷ []) (proj₁ r) (proj₂ r)) st0)
     (trans (exec-trace-cons (instr-load-code-addr lbl) _ v8 A₁ h8)
     (trans (exec-trace-cons (store-at 1) _ v9 A₁ h8)
     (trans (cong (λ r → exec-trace (load-from-slot k ∷ mov-to-input ∷ []) (proj₁ r) (proj₂ r)) st1)
     (trans (exec-trace-cons (load-from-slot k) _ v10 A₁ h10)
     (trans (cong (λ r → exec-trace (mov-to-input ∷ []) (proj₁ r) (proj₂ r)) ld11)
            (exec-trace-cons mov-to-input [] v11 A₁ h10)))))))))))))))

    u : FlatState
    u = record gs { floc = v12 ; falloc = A₁ ; fpc = 12 ℕ.+ fpc gs }

    private
      sts : All StraightStep T12
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ []
      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T12
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ []
      he : halted (proj₁ (exec-trace T12 s a)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) whole) h10
      run₀ = SR.straight-steps {prog} T12 gs sts sp12 nh0 he
      eq : SR.after T12 gs ≡ u
      eq = cong (λ r → record gs { floc = proj₁ r ; falloc = proj₂ r ; fpc = 12 ℕ.+ fpc gs }) whole

    run12 : FlatSteps prog 12 gs u
    run12 = subst (FlatSteps prog 12 gs) eq run₀

    sil12 : chain-events run12 ≡ []
    sil12 = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} T12 gs sts sp12 nh0 he evs)

    run13 : FlatSteps prog 13 σ u
    run13 = FlatSteps-++ (GetOut.step g) run12

    ev13 : chain-events run13 ≡ []
    ev13 = trans (chain-events-++ (GetOut.step g) run12) (cong₂ DL._++_ (GetOut.silent g) sil12)

    -- what the run leaves
    freshH : ∀ o′ → Live a (AtDynamic (heap-loc rd o′)) → ⊥
    freshH o′ = FlatAlloc.alloc-fresh {FS} a o′

    keepU : ∀ l → Live a l → readLoc v12 l ≡ readLoc (floc σ) l
    keepU (AtDynamic hl) lv =
      trans (writeLoc-preserves-other v9 H1 (AtDynamic hl) code (λ e′ → freshH 1 (subst (Live a) (sym e′) lv)))
            (writeLoc-preserves-other v7 H (AtDynamic hl) tag (λ e′ → freshH 0 (subst (Live a) (sym e′) lv)))

    below : ∀ loc → BeforeFrontier (record a { next-slot = n }) loc → readLoc v12 loc ≡ readLoc (floc σ) loc
    below (AtDynamic hl) (BeforeFrontier.heap-before p) = keepU (AtDynamic hl) (BeforeFrontier.heap-before p)
    below (AtStack fr j) bf =
      trans (writeLoc-preserves-other v9 H1 (AtStack fr j) code (λ ()))
     (trans (writeLoc-preserves-other v7 H (AtStack fr j) tag (λ ()))
     (trans (store-slot-preserves-before cl v4 (record a { next-slot = n }) A₁ (AtStack fr j) refl ≤-refl bf)
     (trans (store-slot-preserves-before k v2 (record a { next-slot = n }) a (AtStack fr j) refl (m≤m+n n 1) bf)
     (trans (store-slot-preserves-before ev s (record a { next-slot = n }) a (AtStack fr j) refl
               (m≤m+n n 2) bf)
            (out-mem σ wE (AtStack fr j))))))

    out : SetupOut E env n l1 prog σ μ-sv
    out = record
      { u      = u
      ; runS   = run13 , ev13 , trans (log-of run13 ev13) (++-identityʳ _)
      ; seg    = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }
      ; nh     = h10
      ; pc     = refl
      ; ret    = refl
      ; clo    = refl
      ; lnk    = refl
      ; hc     = hc
      ; ref-hc = refl
      ; inμ    = refl
      ; cl     = trans (writeLoc-preserves-other v9 H1 (AtStack cf₀ cl) code (λ ()))
                (trans (writeLoc-preserves-other v7 H (AtStack cf₀ cl) tag (λ ()))
                       (writeLoc-read-same-stack v4 cf₀ cl (SV-Ptr H)))
      ; env-sv = wE
      ; ev     = trans (writeLoc-preserves-other v9 H1 (AtStack cf₀ ev) code (λ ()))
                (trans (writeLoc-preserves-other v7 H (AtStack cf₀ ev) tag (λ ()))
                (trans (writeLoc-preserves-other v4 (AtStack cf₀ cl) (AtStack cf₀ ev) (SV-Ptr H)
                          (λ e′ → <-irrefl (cong slot-of e′) (m<m+n n (s≤s z≤n))))
                (trans (writeLoc-preserves-other v2 (AtStack cf₀ k) (AtStack cf₀ ev) μ-sv
                          (λ e′ → <-irrefl (cong slot-of e′) (+-monoʳ-< n (s≤s (s≤s z≤n)))))
                       (writeLoc-read-same-stack s cf₀ ev wE))))
      ; src    = FlatPut.src-tr {FS} {prog} (λ l lv → trans (keepU l lv) (sym (out-mem σ wE l)))
                   (PairBuildC.src-of-place {FS} {prog} (GetOut.place g))
      ; code   = readLoc-writeLoc-same v9 H1 code
      ; lhc    = FlatAlloc.alloc-live {FS} 2 a 1
      ; cf     = refl
      ; hr     = refl
      ; bk     = FlatAlloc.alloc-bk {FS} 2 a
      ; keep   = keepU
      }
