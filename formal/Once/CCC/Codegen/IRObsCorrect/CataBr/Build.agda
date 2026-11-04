-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.CataBr.Build   (plan 0.123 B.4 α2)
--
-- THE REBUILD'S TWO BUILDS, on the flat layout (D375), as `Walk`s:
--
--   * `BuildPair`: `pair-text k₁ k₂ kb B C` — the first part's word (in
--     `Output`) to slot `k₁`, a fresh block of `2 ⊔ size (B * C)` words at
--     `kb`, the first part `put` at word 0 from `k₁`, the second (stashed
--     earlier at `k₂`) at word `size B`, the block's address into `Output`.
--     (`Pair.Build.Tail` is the same run with the stash roles the other way
--     round: there the word in `Output` is the SECOND part.)
--   * `BuildSum`: `wrap-sum t …` — the payload's word (in `Output`) to slot
--     `k`, a fresh block at `suc k`, the tag at word 0, the padding, the
--     payload `put` at word 1, the block's address into `Output`.
--     (`Inj.Run` is the same run after its `mov-to-output`.)
--
-- Each leaves `Output` holding a valid word for the built value, keeps every
-- slot but its own two, everything live at its start, and every block.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.CataBr.Build (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.Codegen.IRObsCorrect.Resusp.Base o tbl using (module ResuspBaseC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Stack o tbl using (module CataStackC)
open import Once.CCC.Codegen.IRObsCorrect.CataBr.Walk o tbl using (module CataWalkC)
open import Once.CCC.Codegen.IRToTrace o using (wrap-sum)
import Once.CCC.Machine.SMCore as SMCore
open import Once.CCC.Machine.SMCore
  using (LocState; module LocState; AbstractTrace; AbstractInstr; AllocState; module AllocState; module MemOps; module AbstractExec
        ; StoredValue; readReg; writeReg; Output; Input1; SV-Ptr; SV-Tag; sv-as-loc; sucLoc; offsetLoc
        ; store-at-slot; load-from-slot; mov-to-input; instr-alloc-heap; instr-load-tag-lit; store-at)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc)
open import Once.IRTy using (IRTy) renaming (_*_ to _*ᵀ_; _+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (kind; put; fill; put-All; fill-All)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat.Properties using (m≤n⊔m; m≤m⊔n; +-monoʳ-<; m+[n∸m]≡n)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
import Once.CCC.Machine.SMPrimitives

-- the pair build's text
pair-text : (k₁ k₂ kb : ℕ) (B C : IRTy) → AbstractTrace
pair-text k₁ k₂ kb B C =
  store-at-slot k₁ ∷ instr-alloc-heap (2 ⊔ size (B *ᵀ C)) ∷ store-at-slot kb ∷
  (put B k₁ kb 0 ++ put C k₂ kb (size B) ++ load-from-slot kb ∷ [])

-- a sum's arm: which tag, which payload type, which injection
data Arm : Set where
  arm-l arm-r : Arm

arm-tag : Arm → ℕ
arm-tag arm-l = 0
arm-tag arm-r = 1

arm-ty : Arm → IRTy → IRTy → IRTy
arm-ty arm-l A B = A
arm-ty arm-r A B = B

module CataBuildC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open ResuspBaseC {FS}
  open CataStackC {FS} using (WordAt)
  open CataWalkC {FS} using (Walk; SlotsKept)
  open LocState using (regs; halted)
  open AllocState using (next-slot; next-heap-ref; current-frame)
  open MemOps {FS} using (writeLoc; writeLoc-preserves-other; writeLoc-read-same-stack; writeLoc-regs; writeLoc-halted)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons; exec-load-from-slot-with-value)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open Once.CCC.Machine.SMPrimitives.MemoryOps {FS} using (readLoc-writeLoc-same)
  open FlatEventTrace {FS} using (chain-events-subst)
  open ClosureWellFormedBase {FS} using (Pad; cell-ptr; cell-inline; cell-flat)
  module SR = StraightRunAPI {FS}

  arm-val : ∀ (r : Arm) {A B : IRTy} → ⟦ arm-ty r A B ⟧ → ⟦ A +ᵀ B ⟧
  arm-val arm-l x = inj₁ x
  arm-val arm-r x = inj₂ x

  arm-fits : ∀ (r : Arm) (A B : IRTy) → suc (size (arm-ty r A B)) ≤ size (A +ᵀ B)
  arm-fits arm-l A B = s≤s (m≤m⊔n (size A) (size B))
  arm-fits arm-r A B = s≤s (m≤n⊔m (size A) (size B))

  private
    slot-of : ValueLocation FS → ℕ
    slot-of (AtStack _ j) = j
    slot-of (AtDynamic _) = 0

    off-of : ValueLocation FS → ℕ
    off-of (AtDynamic (heap-loc _ o′)) = o′
    off-of (AtStack _ _) = 0

    -- a write to one slot is not a read of another
    ns : ∀ {f} {i j : ℕ} → i ≢ j → AtStack {FS} f i ≢ AtStack f j
    ns d e = d (cong slot-of e)

  ------------------------------------------------------------------------
  -- THE PAIR.
  ------------------------------------------------------------------------
  module BuildPair {prog : AbstractTrace} (n k₁ k₂ kb : ℕ) (B C : IRTy) (σ : FlatState)
                   {vB : ⟦ B ⟧} {vC : ⟦ C ⟧} (wC : StoredValue FS)
                   (span : SpanAt prog (fpc σ) (pair-text k₁ k₂ kb B C))
                   (h : halted (floc σ) ≡ false)
                   (n≤k₁ : n ≤ k₁) (n≤kb : n ≤ kb)
                   (k₂≢k₁ : k₂ ≢ k₁) (kb≢k₁ : kb ≢ k₁) (kb≢k₂ : kb ≢ k₂)
                   (srcB : FlatPut.Src {FS} {prog} (falloc σ) (floc σ) B vB (readReg (regs (floc σ)) Output))
                   (srcC : FlatPut.Src {FS} {prog} (falloc σ) (floc σ) C vC wC)
                   (rsC : readLoc (floc σ) (AtStack (current-frame (falloc σ)) k₂) ≡ just wC)
    where
    open FlatPut {FS} {prog} using (Src; src-tr; src-flat; put-run; PutOut; dst)

    s  = floc σ
    a  = falloc σ
    cf = current-frame a
    T  = pair-text k₁ k₂ kb B C
    N  = 2 ⊔ size (B *ᵀ C)
    A₁ = FlatAlloc.alloc-after {FS} N a
    rd = FlatAlloc.fresh-ref {FS} a
    L : ValueLocation FS
    L  = AtDynamic (heap-loc rd 0)
    blk : StoredValue FS
    blk = SV-Ptr L
    wB = readReg (regs s) Output

    t₁ = proj₁ (exec-abstract (store-at-slot k₁) s a)
    t₂ = proj₁ (exec-abstract (instr-alloc-heap N) t₁ a)
    t₃ = proj₁ (exec-abstract (store-at-slot kb) t₂ A₁)

    R0 R1 R2 : AbstractTrace
    R0 = put B k₁ kb 0 ++ put C k₂ kb (size B) ++ load-from-slot kb ∷ []
    R1 = store-at-slot kb ∷ R0
    R2 = instr-alloc-heap N ∷ R1

    prefix : exec-trace T s a ≡ exec-trace R0 t₃ A₁
    prefix = trans (exec-trace-cons (store-at-slot k₁) R2 s a h)
            (trans (exec-trace-cons (instr-alloc-heap N) R1 t₁ a h)
                   (exec-trace-cons (store-at-slot kb) R0 t₂ A₁ h))

    fst₃ : readLoc t₃ (AtStack cf k₁) ≡ just wB
    fst₃ = trans (writeLoc-preserves-other t₂ (AtStack cf kb) (AtStack cf k₁) blk (ns kb≢k₁))
                 (writeLoc-read-same-stack s cf k₁ wB)

    snd₃ : readLoc t₃ (AtStack cf k₂) ≡ just wC
    snd₃ = trans (writeLoc-preserves-other t₂ (AtStack cf kb) (AtStack cf k₂) blk (ns kb≢k₂))
           (trans (writeLoc-preserves-other s (AtStack cf k₁) (AtStack cf k₂) wB (ns (λ e → k₂≢k₁ (sym e))))
                  rsC)

    blk₃ : readLoc t₃ (AtStack cf kb) ≡ just blk
    blk₃ = writeLoc-read-same-stack t₂ cf kb blk

    keep₃ : ∀ l → Live a l → readLoc t₃ l ≡ readLoc s l
    keep₃ (AtDynamic hl) _ = refl

    freshA : ∀ o′ → Live a (AtDynamic (heap-loc rd o′)) → ⊥
    freshA o′ = FlatAlloc.alloc-fresh {FS} a o′

    S≤N : size B + size C ≤ N
    S≤N = m≤n⊔m 2 (size B + size C)

    PB = put-run B k₁ kb 0 t₃ A₁ a wB rd N h fst₃ blk₃
           (FlatAlloc.alloc-bft {FS} N a) (FlatAlloc.alloc-bk {FS} N a) freshA
           (FlatAlloc.alloc-live {FS} N a) (≤-trans (m≤m+n (size B) (size C)) S≤N)
           (FlatAlloc.alloc-in {FS} N a) (src-tr keep₃ srcB)
    module PB = PutOut PB
    sB = proj₁ (exec-trace (put B k₁ kb 0) t₃ A₁)

    keepB : ∀ l → Live a l → readLoc sB l ≡ readLoc t₃ l
    keepB (AtDynamic hl) lv = PB.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e lv))

    PC = put-run C k₂ kb (size B) sB A₁ a wC rd N PB.live
           (trans (PB.other (AtStack cf k₂) (λ j _ ())) snd₃)
           (trans (PB.other (AtStack cf kb) (λ j _ ())) blk₃)
           (FlatAlloc.alloc-bft {FS} N a) (FlatAlloc.alloc-bk {FS} N a) freshA
           (FlatAlloc.alloc-live {FS} N a) S≤N (FlatAlloc.alloc-in {FS} N a)
           (src-tr (λ l lv → trans (keepB l lv) (keep₃ l lv)) srcC)
    module PC = PutOut PC
    sC = proj₁ (exec-trace (put C k₂ kb (size B)) sB A₁)

    sfin = record sC { regs = writeReg (regs sC) Output blk }

    last : exec-trace (load-from-slot kb ∷ []) sC A₁ ≡ (sfin , A₁)
    last = trans (exec-trace-cons (load-from-slot kb) [] sC A₁ PC.live)
                 (cong (λ mv → exec-load-from-slot-with-value mv sC A₁)
                       (trans (PC.other (AtStack cf kb) (λ j _ ())) (trans (PB.other (AtStack cf kb) (λ j _ ())) blk₃)))

    whole : exec-trace T s a ≡ (sfin , A₁)
    whole =
      trans prefix
     (trans (exec-trace-append (put B k₁ kb 0) (put C k₂ kb (size B) ++ load-from-slot kb ∷ []) t₃ A₁)
     (trans (cong (λ x → exec-trace (put C k₂ kb (size B) ++ load-from-slot kb ∷ []) sB x) PB.alloc-eq)
     (trans (exec-trace-append (put C k₂ kb (size B)) (load-from-slot kb ∷ []) sB A₁)
     (trans (cong (λ x → exec-trace (load-from-slot kb ∷ []) sC x) PC.alloc-eq)
            last))))

    hfin : halted sfin ≡ false
    hfin = PC.live

    -- the pair: the first part at word 0, kept by the second put; the second after
    cellB : CellAt {prog = prog} A₁ B vB L sfin
    cellB = PB.cell-at sfin
              (λ j j< → PC.other (dst rd 0 j) (λ j′ _ e → apart j j′ j< (cong off-of e)))
              (λ { (AtDynamic hl) lv → trans (PC.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e lv)))
                                             (PB.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e lv))) })
      where
        apart : ∀ j j′ → j < size B → (0 + j) + 0 ≡ (size B + j′) + 0 → ⊥
        apart j j′ j< e =
          <-irrefl refl (<-≤-trans j< (≤-trans (m≤m+n (size B) j′)
            (≤-reflexive (sym (trans (sym (+-identityʳ j)) (trans e (+-identityʳ (size B + j′))))))))

    cellC : CellAt {prog = prog} A₁ C vC (offsetLoc L (size B)) sfin
    cellC = PC.cell-at sfin (λ j _ → refl)
              (λ { (AtDynamic hl) lv → PC.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e lv)) })

    live-L : Live A₁ L
    live-L = FlatAlloc.alloc-live {FS} N a 0

    val : ValidAtWF {prog = prog} Heap A₁ {B *ᵀ C} (vB , vC) L sfin
    val = valid-pair-wf tt (FlatAlloc.alloc-live {FS} N a 1) cellB cellC

    -- the chain
    τ : FlatState
    τ = record σ { floc = sfin ; falloc = A₁ ; fpc = length T + fpc σ }

    private
      he : halted (proj₁ (exec-trace T s a)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) whole) hfin

      sts : All StraightStep T
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            ++⁺ (put-All {StraightStep} B k₁ kb 0 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                (++⁺ (put-All {StraightStep} C k₂ kb (size B) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                     ((λ _ _ → refl) ∷ []))

      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            ++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} B k₁ kb 0 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} C k₂ kb (size B) (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                     ((λ _ → refl) ∷ []))

      run₀ = SR.straight-steps {prog} T σ sts span h he
      eq : SR.after T σ ≡ τ
      eq = cong (λ r → record σ { floc = proj₁ r ; falloc = proj₂ r ; fpc = length T + fpc σ }) whole

    run : FlatSteps prog (length T) σ τ
    run = subst (FlatSteps prog (length T) σ) eq run₀

    silent : chain-events run ≡ []
    silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} T σ sts span h he evs)

    below : ∀ loc → BeforeFrontier (record a { next-slot = n }) loc → readLoc sfin loc ≡ readLoc s loc
    below (AtDynamic hl) (BeforeFrontier.heap-before p) =
      trans (PC.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e (BeforeFrontier.heap-before p))))
            (PB.other (AtDynamic hl) (λ j _ e → freshA _ (subst (Live a) e (BeforeFrontier.heap-before p))))
    below (AtStack fr j) bf =
      trans (PC.other (AtStack fr j) (λ _ _ ()))
     (trans (PB.other (AtStack fr j) (λ _ _ ()))
     (trans (store-slot-preserves-before kb t₂ (record a { next-slot = n }) A₁ (AtStack fr j) refl n≤kb bf)
            (store-slot-preserves-before k₁ s (record a { next-slot = n }) a (AtStack fr j) refl n≤k₁ bf)))

    slots : ∀ j → j ≢ k₁ → j ≢ kb → readLoc sfin (AtStack cf j) ≡ readLoc s (AtStack cf j)
    slots j d₁ d₂ =
      trans (PC.other (AtStack cf j) (λ _ _ ()))
     (trans (PB.other (AtStack cf j) (λ _ _ ()))
     (trans (writeLoc-preserves-other t₂ (AtStack cf kb) (AtStack cf j) blk (ns (λ e → d₂ (sym e))))
            (writeLoc-preserves-other s (AtStack cf k₁) (AtStack cf j) wB (ns (λ e → d₁ (sym e))))))

    walk : ∀ {K : ℕ → Set} → (∀ j → K j → (j ≢ k₁) × (j ≢ kb))
         → Walk prog n K σ (length T + fpc σ)
                (λ τ′ → WordAt prog (falloc τ′) (B *ᵀ C) (vB , vC) (readReg (regs (floc τ′)) Output) (floc τ′))
    walk f = record
      { τ = τ ; steps = length T ; run = run , silent , trans (log-of run silent) (++-identityʳ _)
      ; seg = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }
      ; bk = FlatAlloc.alloc-bk {FS} N a
      ; nh = hfin ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = refl
      ; slots = λ j kj → slots j (proj₁ (f j kj)) (proj₂ (f j kj))
      ; post = src-flat tt live-L val }

  ------------------------------------------------------------------------
  -- THE SUM.
  ------------------------------------------------------------------------
  module BuildSum {prog : AbstractTrace} (n : ℕ) (r : Arm) (A B : IRTy) (k : ℕ) (σ : FlatState)
                  (span : SpanAt prog (fpc σ) (wrap-sum (arm-tag r) (kind (arm-ty r A B)) (size (arm-ty r A B)) (size (A +ᵀ B)) k))
                  (h : halted (floc σ) ≡ false)
                  (n≤k : n ≤ k)
                  {x : ⟦ arm-ty r A B ⟧}
                  (src : FlatPut.Src {FS} {prog} (falloc σ) (floc σ) (arm-ty r A B) x (readReg (regs (floc σ)) Output))
    where
    open FlatPut {FS} {prog} using (Src; src-tr; src-flat; put-run; PutOut; fill-exec; FillOut; dst)

    P = arm-ty r A B
    S = A +ᵀ B
    t = arm-tag r
    sp≤S = arm-fits r A B
    T = wrap-sum t (kind P) (size P) (size S) k

    s     = floc σ
    alloc = falloc σ
    N  = 2 ⊔ size S
    c  = size S ∸ suc (size P)
    rd = FlatAlloc.fresh-ref {FS} alloc
    A₁ = FlatAlloc.alloc-after {FS} N alloc
    L  : ValueLocation FS
    L  = AtDynamic (heap-loc rd 0)
    blk : StoredValue FS
    blk = SV-Ptr L
    cf = current-frame alloc
    w  = readReg (regs s) Output
    tag = SV-Tag {FS} t

    two≤ : 2 ≤ N
    two≤ = m≤m⊔n 2 (size S)

    s₂ = proj₁ (exec-abstract (store-at-slot k) s alloc)
    s₃ = proj₁ (exec-abstract (instr-alloc-heap N) s₂ alloc)
    s₄ = proj₁ (exec-abstract (store-at-slot (suc k)) s₃ A₁)
    s₅ = proj₁ (exec-abstract mov-to-input s₄ A₁)
    s₆ = proj₁ (exec-abstract (instr-load-tag-lit t) s₅ A₁)
    s₇ = writeLoc s₆ L tag

    ib0 : InBlk A₁ L
    ib0 = FlatAlloc.alloc-in {FS} N alloc 0 (≤-trans (s≤s z≤n) two≤)

    R = fill (suc (size P)) c ++ put P k (suc k) 1 ++ load-from-slot (suc k) ∷ []

    st-eq : exec-abstract (store-at 0) s₆ A₁ ≡ (s₇ , A₁)
    st-eq = cong (λ b → (SMCore.ExecFinal.exec-store-in-block {FS} b L tag s₆ , A₁)) ib0

    pre : exec-trace T s alloc ≡ exec-trace R s₇ A₁
    pre =
      trans (exec-trace-cons (store-at-slot k) _ s alloc h)
     (trans (exec-trace-cons (instr-alloc-heap N) _ s₂ alloc h)
     (trans (exec-trace-cons (store-at-slot (suc k)) _ s₃ A₁ h)
     (trans (exec-trace-cons mov-to-input _ s₄ A₁ h)
     (trans (exec-trace-cons (instr-load-tag-lit t) _ s₅ A₁ h)
     (trans (exec-trace-cons (store-at 0) _ s₆ A₁ h)
            (cong (λ q → exec-trace R (proj₁ q) (proj₂ q)) st-eq))))))

    h₇ : halted s₇ ≡ false
    h₇ = trans (writeLoc-halted s₆ L tag) h

    k≢sk : suc k ≢ k
    k≢sk e = <-irrefl (sym e) (n<1+n k)

    slot-n₇ : readLoc s₇ (AtStack cf k) ≡ just w
    slot-n₇ =
      trans (writeLoc-preserves-other s₆ L (AtStack cf k) tag (λ ()))
            (trans (writeLoc-preserves-other s₃ (AtStack cf (suc k)) (AtStack cf k) (readReg (regs s₃) Output) (ns k≢sk))
                   (writeLoc-read-same-stack s cf k w))

    slot-b₇ : readLoc s₇ (AtStack cf (suc k)) ≡ just blk
    slot-b₇ =
      trans (writeLoc-preserves-other s₆ L (AtStack cf (suc k)) tag (λ ()))
            (writeLoc-read-same-stack s₃ cf (suc k) (readReg (regs s₃) Output))

    in1₇ : readReg (regs s₇) Input1 ≡ blk
    in1₇ = cong (λ q → readReg q Input1) (writeLoc-regs s₆ L tag)

    tag₇ : readLoc s₇ L ≡ just tag
    tag₇ = readLoc-writeLoc-same s₆ L tag

    pad< : ∀ j → j < c → suc (size P) + j < N
    pad< j j< = ≤-trans (subst (suc (size P) + j <_) (m+[n∸m]≡n sp≤S) (+-monoʳ-< (suc (size P)) j<)) (m≤n⊔m 2 (size S))

    F = fill-exec (suc (size P)) c s₇ A₁ rd h₇ in1₇
          (λ j j< → subst (λ z → InBlk A₁ (AtDynamic (heap-loc rd z))) (sym (+-identityʳ (suc (size P) + j)))
                          (FlatAlloc.alloc-in {FS} N alloc (suc (size P) + j) (pad< j j<)))
    sf = proj₁ (exec-trace (fill (suc (size P)) c) s₇ A₁)
    module F = FillOut F

    slot-nf : readLoc sf (AtStack cf k) ≡ just w
    slot-nf = trans (F.other (AtStack cf k) (λ j _ ())) slot-n₇

    slot-bf : readLoc sf (AtStack cf (suc k)) ≡ just blk
    slot-bf = trans (F.other (AtStack cf (suc k)) (λ j _ ())) slot-b₇

    fresh : ∀ o′ → Live alloc (AtDynamic (heap-loc rd o′)) → ⊥
    fresh o′ = FlatAlloc.alloc-fresh {FS} alloc o′

    not-rd : ∀ hl → Live alloc (AtDynamic hl) → ∀ o′ → AtDynamic {FS} hl ≢ AtDynamic (heap-loc rd o′)
    not-rd hl lv o′ e = fresh o′ (subst (Live alloc) e lv)

    keep₇ : ∀ hl → Live alloc (AtDynamic hl) → readLoc s₇ (AtDynamic hl) ≡ readLoc s (AtDynamic hl)
    keep₇ hl lv = writeLoc-preserves-other s₆ L (AtDynamic hl) tag (λ e → not-rd hl lv 0 (sym e))

    keepf : ∀ l → Live alloc l → readLoc sf l ≡ readLoc s l
    keepf (AtDynamic hl) lv = trans (F.other (AtDynamic hl) (λ j _ e → not-rd hl lv _ e)) (keep₇ hl lv)

    N≥ : 1 + size P ≤ N
    N≥ = ≤-trans sp≤S (m≤n⊔m 2 (size S))

    Pt = put-run P k (suc k) 1 sf A₁ alloc w rd N F.live slot-nf slot-bf
           (FlatAlloc.alloc-bft {FS} N alloc) (FlatAlloc.alloc-bk {FS} N alloc) fresh
           (FlatAlloc.alloc-live {FS} N alloc) N≥ (FlatAlloc.alloc-in {FS} N alloc)
           (src-tr keepf src)
    sp = proj₁ (exec-trace (put P k (suc k) 1) sf A₁)
    module Pt = PutOut Pt

    sfin = record sp { regs = writeReg (regs sp) Output blk }

    slot-bp : readLoc sp (AtStack cf (suc k)) ≡ just blk
    slot-bp = trans (Pt.other (AtStack cf (suc k)) (λ j _ ())) slot-bf

    last : exec-trace (load-from-slot (suc k) ∷ []) sp A₁ ≡ (sfin , A₁)
    last = trans (exec-trace-cons (load-from-slot (suc k)) [] sp A₁ Pt.live)
                 (cong (λ mv → exec-load-from-slot-with-value mv sp A₁) slot-bp)

    whole : exec-trace T s alloc ≡ (sfin , A₁)
    whole =
      trans pre
     (trans (exec-trace-append (fill (suc (size P)) c) (put P k (suc k) 1 ++ load-from-slot (suc k) ∷ []) s₇ A₁)
     (trans (cong (λ q → exec-trace (put P k (suc k) 1 ++ load-from-slot (suc k) ∷ []) sf q) F.alloc-eq)
     (trans (exec-trace-append (put P k (suc k) 1) (load-from-slot (suc k) ∷ []) sf A₁)
     (trans (cong (λ q → exec-trace (load-from-slot (suc k) ∷ []) sp q) Pt.alloc-eq)
            last))))

    hfin : halted sfin ≡ false
    hfin = Pt.live

    -- the sum's words, in the state the put leaves
    hl-inj : ∀ {a b} → AtDynamic {FS} (heap-loc rd a) ≡ AtDynamic (heap-loc rd b) → a ≡ b
    hl-inj q = cong off-of q

    suc≢0 : ∀ {a} → suc a ≡ 0 → ⊥
    suc≢0 ()

    tag-p : readLoc sp L ≡ just tag
    tag-p = trans (Pt.other L (λ j _ e → suc≢0 (sym (hl-inj e))))
                  (trans (F.other L (λ j _ e → suc≢0 (sym (hl-inj e)))) tag₇)

    pad-p : Pad sp L (suc (size P)) c
    pad-p j j< =
      proj₁ (F.written j j<) ,
      trans (Pt.other (dst rd (suc (size P)) j) (λ j′ j′< e → apart j′ j′< (hl-inj e))) (proj₂ (F.written j j<))
      where
        suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
        suc-inj refl = refl
        apart : ∀ j′ → j′ < size P → (suc (size P) + j) + 0 ≡ (1 + j′) + 0 → ⊥
        apart j′ j′< e =
          <-irrefl refl (<-≤-trans j′< (≤-trans (m≤m+n (size P) j)
            (≤-reflexive (suc-inj (trans (sym (+-identityʳ _)) (trans e (+-identityʳ _)))))))

    live-suc : Live A₁ (sucLoc L)
    live-suc = FlatAlloc.alloc-live {FS} N alloc 1

    live-L : Live A₁ L
    live-L = FlatAlloc.alloc-live {FS} N alloc 0

    in-suc : InBlk A₁ (sucLoc L)
    in-suc = FlatAlloc.alloc-in {FS} N alloc 1 (≤-trans (s≤s (s≤s z≤n)) two≤)

    sum-of : ∀ (r′ : Arm) → r′ ≡ r → CellAt {prog = prog} A₁ P x (sucLoc L) sp
           → ValidAtWF {prog = prog} Heap A₁ {S} (arm-val r x) L sp
    sum-of arm-l refl (cell-ptr nd q lv v) = valid-inl-wf nd tt tag-p q lv live-suc pad-p v
    sum-of arm-l refl (cell-inline rep q)  = valid-inl-reg-wf tt tag-p rep q live-suc pad-p
    sum-of arm-l refl (cell-flat fl hr v)  = valid-inl-flat-wf fl tt tag-p live-suc (λ _ → in-suc) pad-p v
    sum-of arm-r refl (cell-ptr nd q lv v) = valid-inr-wf nd tt tag-p q lv live-suc pad-p v
    sum-of arm-r refl (cell-inline rep q)  = valid-inr-reg-wf tt tag-p rep q live-suc pad-p
    sum-of arm-r refl (cell-flat fl hr v)  = valid-inr-flat-wf fl tt tag-p live-suc (λ _ → in-suc) pad-p v

    val : ValidAtWF {prog = prog} Heap A₁ {S} (arm-val r x) L sfin
    val = validityWF-mem-only (arm-val r x) L sp sfin refl refl (sum-of r refl Pt.cell)

    -- the chain
    τ : FlatState
    τ = record σ { floc = sfin ; falloc = A₁ ; fpc = length T + fpc σ }

    private
      he : halted (proj₁ (exec-trace T s alloc)) ≡ false
      he = trans (cong (λ q → halted (proj₁ q)) whole) hfin

      sts : All StraightStep T
      sts = (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
            ++⁺ (fill-All {StraightStep} (suc (size P)) c (λ _ _ → refl) (λ _ _ _ → refl))
                (++⁺ (put-All {StraightStep} P k (suc k) 1 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
                     ((λ _ _ → refl) ∷ []))

      evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T
      evs = (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
            ++⁺ (fill-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} (suc (size P)) c (λ _ → refl) (λ _ _ → refl))
                (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} P k (suc k) 1 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
                     ((λ _ → refl) ∷ []))

      run₀ = SR.straight-steps {prog} T σ sts span h he
      eq : SR.after T σ ≡ τ
      eq = cong (λ q → record σ { floc = proj₁ q ; falloc = proj₂ q ; fpc = length T + fpc σ }) whole

    run : FlatSteps prog (length T) σ τ
    run = subst (FlatSteps prog (length T) σ) eq run₀

    silent : chain-events run ≡ []
    silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} T σ sts span h he evs)

    B₀ = record alloc { next-slot = n }

    below : ∀ loc → BeforeFrontier B₀ loc → readLoc sfin loc ≡ readLoc s loc
    below (AtDynamic hl) (BeforeFrontier.heap-before p) =
      trans (Pt.other (AtDynamic hl) (λ j _ e → not-rd hl (BeforeFrontier.heap-before p) _ e))
            (keepf (AtDynamic hl) (BeforeFrontier.heap-before p))
    below (AtStack fr j) bf =
      trans (Pt.other (AtStack fr j) (λ j _ ()))
     (trans (F.other (AtStack fr j) (λ j _ ()))
     (trans (writeLoc-preserves-other s₆ L (AtStack fr j) tag (λ ()))
     (trans (store-slot-preserves-before (suc k) s₃ B₀ A₁ (AtStack fr j) refl (≤-trans n≤k (n≤1+n k)) bf)
            (store-slot-preserves-before k s B₀ alloc (AtStack fr j) refl n≤k bf))))

    slots : ∀ j → j ≢ k → j ≢ suc k → readLoc sfin (AtStack cf j) ≡ readLoc s (AtStack cf j)
    slots j d₁ d₂ =
      trans (Pt.other (AtStack cf j) (λ _ _ ()))
     (trans (F.other (AtStack cf j) (λ _ _ ()))
     (trans (writeLoc-preserves-other s₆ L (AtStack cf j) tag (λ ()))
     (trans (writeLoc-preserves-other s₃ (AtStack cf (suc k)) (AtStack cf j) (readReg (regs s₃) Output) (ns (λ e → d₂ (sym e))))
            (writeLoc-preserves-other s (AtStack cf k) (AtStack cf j) w (ns (λ e → d₁ (sym e)))))))

    walk : ∀ {K : ℕ → Set} → (∀ j → K j → (j ≢ k) × (j ≢ suc k))
         → Walk prog n K σ (length T + fpc σ)
                (λ τ′ → WordAt prog (falloc τ′) S (arm-val r x) (readReg (regs (floc τ′)) Output) (floc τ′))
    walk f = record
      { τ = τ ; steps = length T ; run = run , silent , trans (log-of run silent) (++-identityʳ _)
      ; seg = record { mem = below ; cf = refl ; sf = refl ; ns = refl ; href = n≤1+n _ }
      ; bk = FlatAlloc.alloc-bk {FS} N alloc
      ; nh = hfin ; pc = refl ; ret = refl ; clo = refl ; lnk = refl ; cf = refl
      ; slots = λ j kj → slots j (proj₁ (f j kj)) (proj₂ (f j kj))
      ; post = src-flat tt live-L val }
