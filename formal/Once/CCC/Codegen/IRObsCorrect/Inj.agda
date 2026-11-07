-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Inj
--
-- plan 0.123 B.4 α: `inl` and `inr` on the flat layout (D381). An injection
-- with tag `t` of a payload `P` into a sum `S` is one straight segment
-- (`IRToTrace.inj-trace`):
--
--   mov-to-output ; store-at-slot n            -- the payload, stashed
--   instr-alloc-heap (2 ⊔ size S) ; store-at-slot (suc n) ; mov-to-input
--   instr-load-tag-lit t ; store-at 0          -- the tag
--   fill (suc (size P)) (size S ∸ suc (size P))    -- the padding (D388)
--   put P n (suc n) 1                          -- the payload's words
--   load-from-slot (suc n)                     -- the block, the result
--
-- `Run` states the segment's effect (`exec-trace`), and the clauses read the
-- sum off it: the tag at word 0, the payload's cell at word 1 (`FlatPut`), the
-- padding after it. The chain is `StraightRun.straight-steps`.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.Inj (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic; ValueLocation)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; AbstractInstr; LocState; AllocState; module LocState; module AllocState; module MemOps; module AbstractExec;
         readReg; writeReg; writeReg-same; Input1; Output; SV-Ptr; SV-Tag; StoredValue; sucLoc; offsetLoc;
         mov-to-output; mov-to-input; store-at-slot; load-from-slot; instr-alloc-heap; instr-load-tag-lit; store-at;
         restore-input; load-at)
open LocState using (regs; halted)
open AllocState using (current-frame; next-slot; next-heap-ref)
open import Once.Memory.HeapAddress using (HeapRef; HeapLocation; heap-loc; offsetHL; mkHeapRef)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float; FitsInRegI)
  renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Codegen.FlatLayout using (fill; put; put-All; fill-All)
open import Once.CCC.Codegen.IRToTrace o using (inj-trace)
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
open import Once.CCC.Machine.Allocation using (module FrontierInvariant)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
open import Once.CCC.Machine.SMPrimitives using (module MemoryOps)
import Once.CCC.Machine.SMPrimitives

open import Data.Nat using (_⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⊔m; m≤m⊔n; +-monoʳ-<; m+[n∸m]≡n; +-cancelˡ-≡)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (Σ)
open import Data.Sum using (inj₁; inj₂)

module InjC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open MemOps {FS} using (writeLoc; writeLoc-halted; writeLoc-regs; writeLoc-preserves-other; writeLoc-read-same-stack)
  open AbstractExec {FS} using (exec-trace; exec-trace-cons)
  open import Once.CCC.Machine.SMCore using (module ExecFinal)
  open Once.CCC.Machine.SMPrimitives.TraceComposition {FS} using (exec-trace-append)
  open MemoryOps {FS} using (readLoc-writeLoc-same)
  module SR = StraightRunAPI {FS}
  open ClosureWellFormedBase {FS} using (Pad; wrap; cell-ptr; cell-inline; cell-flat)
  open FlatEventTrace {FS} using (chain-events-subst)

  ------------------------------------------------------------------------
  -- Sizes: the block holds the tag, the payload and the padding.
  ------------------------------------------------------------------------
  private
    two≤ : ∀ m → 2 ≤ 2 ⊔ m
    two≤ m = m≤m⊔n 2 m

    S≤N : ∀ m → m ≤ 2 ⊔ m
    S≤N m = m≤n⊔m 2 m

    -- a padding word is a word of the block
    pad< : ∀ p m j → suc p ≤ m → j < m ∸ suc p → suc p + j < 2 ⊔ m
    pad< p m j sp≤m j< =
      ≤-trans (subst (suc p + j <_) (m+[n∸m]≡n sp≤m) (+-monoʳ-< (suc p) j<)) (S≤N m)

    -- distinct offsets in one block are distinct cells
    off-of : ValueLocation FS → ℕ
    off-of (AtDynamic (heap-loc _ o)) = o
    off-of (AtStack _ _)              = 0

    hl-inj : ∀ {r a b} → AtDynamic {FS} (heap-loc r a) ≡ AtDynamic (heap-loc r b) → a ≡ b
    hl-inj q = cong off-of q

    suc≢0 : ∀ {a} → suc a ≡ 0 → ⊥
    suc≢0 ()

  ------------------------------------------------------------------------
  -- THE RUN
  ------------------------------------------------------------------------
  module Run {prog : AbstractTrace} (t : ℕ) (P S : IRTy) (n : ℕ)
             (s : LocState FS) (alloc : AllocState {FS})
             (h : halted s ≡ false)
             (sp≤S : suc (size P) ≤ size S) where

    open FlatPut {FS} {prog} using (Src; src-tr; put-run; PutOut; fill-exec; FillOut; dst)

    N  = 2 ⊔ size S
    c  = size S ∸ suc (size P)
    rd = FlatAlloc.fresh-ref {FS} alloc
    A₁ = FlatAlloc.alloc-after {FS} N alloc
    L  : ValueLocation FS
    L  = AtDynamic (heap-loc rd 0)
    blk : StoredValue FS
    blk = SV-Ptr L
    cf = current-frame alloc
    w  = readReg (regs s) Input1
    tag = SV-Tag {FS} t

    -- the seven rows before the padding
    s₁ = proj₁ (exec-abstract mov-to-output s alloc)
    s₂ = proj₁ (exec-abstract (store-at-slot n) s₁ alloc)
    s₃ = proj₁ (exec-abstract (instr-alloc-heap N) s₂ alloc)
    s₄ = proj₁ (exec-abstract (store-at-slot (suc n)) s₃ A₁)
    s₅ = proj₁ (exec-abstract mov-to-input s₄ A₁)
    s₆ = proj₁ (exec-abstract (instr-load-tag-lit t) s₅ A₁)
    s₇ = writeLoc s₆ L tag

    ib0 : InBlk A₁ L
    ib0 = FlatAlloc.alloc-in {FS} N alloc 0 (≤-trans (s≤s z≤n) (two≤ (size S)))

    R = fill (suc (size P)) c ++ put P n (suc n) 1 ++ load-from-slot (suc n) ∷ []

    -- the tag's store, in its block
    st-eq : exec-abstract (store-at 0) s₆ A₁ ≡ (s₇ , A₁)
    st-eq = cong (λ b → (ExecFinal.exec-store-in-block {FS} b L tag s₆ , A₁)) ib0

    pre : exec-trace (inj-trace t P S n) s alloc ≡ exec-trace R s₇ A₁
    pre =
      trans (exec-trace-cons mov-to-output _ s alloc h)
     (trans (exec-trace-cons (store-at-slot n) _ s₁ alloc h)
     (trans (exec-trace-cons (instr-alloc-heap N) _ s₂ alloc h)
     (trans (exec-trace-cons (store-at-slot (suc n)) _ s₃ A₁ h)
     (trans (exec-trace-cons mov-to-input _ s₄ A₁ h)
     (trans (exec-trace-cons (instr-load-tag-lit t) _ s₅ A₁ h)
     (trans (exec-trace-cons (store-at 0) _ s₆ A₁ h)
            (cong (λ r → exec-trace R (proj₁ r) (proj₂ r)) st-eq)))))))

    h₇ : halted s₇ ≡ false
    h₇ = trans (writeLoc-halted s₆ L tag) h

    -- the stash slots
    slot-n₂ : readLoc s₂ (AtStack cf n) ≡ just w
    slot-n₂ = writeLoc-read-same-stack s₁ cf n (readReg (regs s₁) Output)

    slot-n₇ : readLoc s₇ (AtStack cf n) ≡ just w
    slot-n₇ =
      trans (writeLoc-preserves-other s₆ L (AtStack cf n) tag (λ ()))
            (trans (writeLoc-preserves-other s₃ (AtStack cf (suc n)) (AtStack cf n) (readReg (regs s₃) Output)
                      (λ e → <-irrefl (sym (cong slot-of e)) (n<1+n n)))
                   slot-n₂)
      where
        slot-of : ValueLocation FS → ℕ
        slot-of (AtStack _ k) = k
        slot-of (AtDynamic _) = 0

    slot-b₇ : readLoc s₇ (AtStack cf (suc n)) ≡ just blk
    slot-b₇ =
      trans (writeLoc-preserves-other s₆ L (AtStack cf (suc n)) tag (λ ()))
            (writeLoc-read-same-stack s₃ cf (suc n) (readReg (regs s₃) Output))

    in1₇ : readReg (regs s₇) Input1 ≡ blk
    in1₇ = cong (λ q → readReg q Input1) (writeLoc-regs s₆ L tag)

    tag₇ : readLoc s₇ L ≡ just tag
    tag₇ = readLoc-writeLoc-same s₆ L tag

    ------------------------------------------------------------------------
    -- the padding
    ------------------------------------------------------------------------
    F = fill-exec (suc (size P)) c s₇ A₁ rd h₇ in1₇
          (λ j j< → subst (λ z → InBlk A₁ (AtDynamic (heap-loc rd z))) (sym (+-identityʳ (suc (size P) + j)))
                          (FlatAlloc.alloc-in {FS} N alloc (suc (size P) + j) (pad< (size P) (size S) j sp≤S j<)))
    σf = exec-trace (fill (suc (size P)) c) s₇ A₁
    sf = proj₁ σf
    module F = FillOut F

    -- a cell of a block other than the fresh one, or a frame slot, is the fill's to keep
    not-pad : ∀ l → (∀ o → l ≢ AtDynamic (heap-loc rd o)) → ∀ j → j < c → l ≢ dst rd (suc (size P)) j
    not-pad l ne j _ e = ne _ e

    slot-nf : readLoc sf (AtStack cf n) ≡ just w
    slot-nf = trans (F.other (AtStack cf n) (λ j _ ())) slot-n₇

    slot-bf : readLoc sf (AtStack cf (suc n)) ≡ just blk
    slot-bf = trans (F.other (AtStack cf (suc n)) (λ j _ ())) slot-b₇

    ------------------------------------------------------------------------
    -- what the caller has live is not in the fresh block, so the run keeps it
    ------------------------------------------------------------------------
    fresh : ∀ o → Live alloc (AtDynamic (heap-loc rd o)) → ⊥
    fresh o = FlatAlloc.alloc-fresh {FS} alloc o

    not-rd : ∀ hl → Live alloc (AtDynamic hl) → ∀ o → AtDynamic {FS} hl ≢ AtDynamic (heap-loc rd o)
    not-rd hl lv o e = fresh o (subst (Live alloc) e lv)

    keep₇ : ∀ hl → Live alloc (AtDynamic hl) → readLoc s₇ (AtDynamic hl) ≡ readLoc s (AtDynamic hl)
    keep₇ hl lv = writeLoc-preserves-other s₆ L (AtDynamic hl) tag (λ e → not-rd hl lv 0 (sym e))

    keepf : ∀ l → Live alloc l → readLoc sf l ≡ readLoc s l
    keepf (AtDynamic hl) lv = trans (F.other (AtDynamic hl) (λ j _ e → not-rd hl lv _ e)) (keep₇ hl lv)

    ------------------------------------------------------------------------
    -- the payload
    ------------------------------------------------------------------------
    module _ {x : ⟦ P ⟧} (src : Src alloc s P x w) where
      N≥ : 1 + size P ≤ N
      N≥ = ≤-trans sp≤S (S≤N (size S))

      Pt = put-run P n (suc n) 1 sf A₁ alloc w rd N F.live slot-nf slot-bf
             (FlatAlloc.alloc-bft {FS} N alloc) (FlatAlloc.alloc-bk {FS} N alloc) fresh
             (FlatAlloc.alloc-live {FS} N alloc) N≥ (FlatAlloc.alloc-in {FS} N alloc)
             (src-tr keepf src)
      sp = proj₁ (exec-trace (put P n (suc n) 1) sf A₁)
      module Pt = PutOut Pt

      -- the last row: the block is the result
      sfin = record sp { regs = writeReg (regs sp) Output blk }

      slot-bp : readLoc sp (AtStack cf (suc n)) ≡ just blk
      slot-bp = trans (Pt.other (AtStack cf (suc n)) (λ j _ ())) slot-bf

      last : exec-trace (load-from-slot (suc n) ∷ []) sp A₁ ≡ (sfin , A₁)
      last = trans (exec-trace-cons (load-from-slot (suc n)) [] sp A₁ Pt.live)
                   (cong (λ mv → AbstractExec.exec-load-from-slot-with-value {FS} mv sp A₁) slot-bp)

      whole : exec-trace (inj-trace t P S n) s alloc ≡ (sfin , A₁)
      whole =
        trans pre
       (trans (exec-trace-append (fill (suc (size P)) c) (put P n (suc n) 1 ++ load-from-slot (suc n) ∷ []) s₇ A₁)
       (trans (cong (λ a → exec-trace (put P n (suc n) 1 ++ load-from-slot (suc n) ∷ []) sf a) F.alloc-eq)
       (trans (exec-trace-append (put P n (suc n) 1) (load-from-slot (suc n) ∷ []) sf A₁)
       (trans (cong (λ a → exec-trace (load-from-slot (suc n) ∷ []) sp a) Pt.alloc-eq)
              last))))

      hfin : halted sfin ≡ false
      hfin = Pt.live

      ------------------------------------------------------------------------
      -- the sum's words, in the state the put leaves
      ------------------------------------------------------------------------
      tag-p : readLoc sp L ≡ just tag
      tag-p = trans (Pt.other L (λ j _ e → suc≢0 (sym (hl-inj e))))
                    (trans (F.other L (λ j _ e → suc≢0 (sym (hl-inj e)))) tag₇)

      pad-p : Pad sp L (suc (size P)) c
      pad-p j j< =
        proj₁ (F.written j j<) ,
        trans (Pt.other (dst rd (suc (size P)) j) (λ j′ j′< e → apart j′ j′< (hl-inj e))) (proj₂ (F.written j j<))
        where
          apart : ∀ j′ → j′ < size P → (suc (size P) + j) + 0 ≡ (1 + j′) + 0 → ⊥
          apart j′ j′< e =
            <-irrefl refl (<-≤-trans j′< (≤-trans (m≤m+n (size P) j)
              (≤-reflexive (suc-inj (trans (sym (+-identityʳ _)) (trans e (+-identityʳ _)))))))
            where suc-inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
                  suc-inj refl = refl

      cell-p : CellAt {prog = prog} A₁ P x (sucLoc L) sp
      cell-p = Pt.cell

      live-suc : Live A₁ (sucLoc L)
      live-suc = FlatAlloc.alloc-live {FS} N alloc 1

      live-L : Live A₁ L
      live-L = FlatAlloc.alloc-live {FS} N alloc 0

      in-suc : 0 < size P → InBlk A₁ (sucLoc L)
      in-suc _ = FlatAlloc.alloc-in {FS} N alloc 1 (≤-trans (s≤s (s≤s z≤n)) (two≤ (size S)))

      ------------------------------------------------------------------------
      -- what the run leaves alone: the caller's slots below `n`, its heap
      ------------------------------------------------------------------------
      B = record alloc { next-slot = n }

      keep-bf : ∀ l → BeforeFrontier B l → readLoc sfin l ≡ readLoc s l
      keep-bf (AtDynamic hl) (BeforeFrontier.heap-before p) =
        trans (Pt.other (AtDynamic hl) (λ j _ e → not-rd hl (BeforeFrontier.heap-before p) _ e))
              (keepf (AtDynamic hl) (BeforeFrontier.heap-before p))
      keep-bf (AtStack fr j) bf =
        trans (Pt.other (AtStack fr j) (λ j _ ()))
       (trans (F.other (AtStack fr j) (λ j _ ()))
       (trans (writeLoc-preserves-other s₆ L (AtStack fr j) tag (λ ()))
       (trans (store-slot-preserves-before (suc n) s₃ B A₁ (AtStack fr j) refl (n≤1+n n) bf)
              (store-slot-preserves-before n s₁ B alloc (AtStack fr j) refl ≤-refl bf))))

      bf-mono′ : ∀ m loc → BeforeFrontier (record alloc { next-slot = m }) loc
               → BeforeFrontier (record A₁ { next-slot = m }) loc
      bf-mono′ m _ (BeforeFrontier.stack-before e j<) = BeforeFrontier.stack-before e j<
      bf-mono′ m _ (BeforeFrontier.stack-ancestor a src′) = BeforeFrontier.stack-ancestor a src′
      bf-mono′ m _ (BeforeFrontier.heap-before p) = BeforeFrontier.heap-before (<-trans p (n<1+n _))

  ------------------------------------------------------------------------
  -- The segment is straight, and silent.
  ------------------------------------------------------------------------
  inj-straight : ∀ t P S n → All StraightStep (inj-trace t P S n)
  inj-straight t P S n =
    (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷ (λ _ _ → refl) ∷
    ++⁺ (fill-All {StraightStep} (suc (size P)) (size S ∸ suc (size P)) (λ _ _ → refl) (λ _ _ _ → refl))
        (++⁺ (put-All {StraightStep} P n (suc n) 1 (λ _ _ → refl) (λ _ _ → refl) (λ _ _ → refl) (λ _ _ _ → refl) (λ _ _ _ → refl))
             ((λ _ _ → refl) ∷ []))

  inj-silent : ∀ t P S n → All (λ i → ∀ fs′ → event-of i fs′ ≡ []) (inj-trace t P S n)
  inj-silent t P S n =
    (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷ (λ _ → refl) ∷
    ++⁺ (fill-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} (suc (size P)) (size S ∸ suc (size P)) (λ _ → refl) (λ _ _ → refl))
        (++⁺ (put-All {λ i → ∀ fs′ → event-of i fs′ ≡ []} P n (suc n) 1 (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ _ → refl) (λ _ _ → refl))
             ((λ _ → refl) ∷ []))

  ------------------------------------------------------------------------
  -- The input, as a value to put: a node or a flat value where it lies, a
  -- scalar in its register (D389: a scalar has no memory residence), a unit
  -- anyhow.
  ------------------------------------------------------------------------
  module _ {prog : AbstractTrace} where
    open FlatPut {FS} {prog} using (Src; src-node; src-scalar; src-flat; src-unit)

    src-loc : ∀ (C : IRTy) {alloc s c m l} → ValidAtWF {prog = prog} m alloc {C} c l s → Live alloc l
            → Src alloc s C c (SV-Ptr l)
    src-loc Unit       v lv = src-flat tt lv v
    src-loc (A * B)    v lv = src-flat tt lv v
    src-loc (A +ᵀ B)   v lv = src-flat tt lv v
    src-loc (μ-type F) v lv = src-node tt lv v
    src-loc (ν-type F) v lv = src-node tt lv v
    src-loc (A ⇛ B)    v lv = src-node tt lv v
    src-loc Int        (wrap ()) _
    src-loc Float      (wrap ()) _
    src-loc Void       {c = ()} _ _

    mk-src : ∀ (C : IRTy) {mIn alloc s} {c : ⟦ C ⟧} → InputAt {prog} {C} mIn alloc c s
           → Src alloc s C c (readReg (regs s) Input1)
    mk-src C {alloc = alloc} {s} {c} (in-loc l v lv eq) = subst (Src alloc s C c) (sym eq) (src-loc C v lv)
    mk-src C {alloc = alloc} {s} {c} (in-reg fit eq)    = subst (Src alloc s C c) (sym eq) (src-scalar fit)
    mk-src C (in-unit refl) = src-unit

  ------------------------------------------------------------------------
  -- `inl` and `inr`
  ------------------------------------------------------------------------
  obs-correct-inl : ∀ {A B} → IRObsCorrectF (inl {A} {B})
  obs-correct-inl {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = trans silent (sym (denot-[] k))
      ; value-realized =
          realized (length T) settle Heap R.A₁ run (λ _ → R.hfin src) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl)
                   (log-of run (trans silent (sym (denot-[] k))))
                   (λ { refl → at-loc R.L val (R.live-L src) refl val (R.live-L src) })
                   (m≤m+n k _)
                   (λ _ fr j bf → R.keep-bf src (AtStack fr j) bf) (λ _ hl bf → R.keep-bf src (AtDynamic hl) bf)
                   (λ _ → refl) (λ _ → R.bf-mono′ src) (λ _ → refl) (λ _ → FlatAlloc.alloc-bk {FS} R.N alloc)
      }
    where
      T = inj-trace 0 A (A +ᵀ B) n
      module R = Run {prog} 0 A (A +ᵀ B) n s alloc nh (s≤s (m≤m⊔n (size A) (size B)))
      src = mk-src {prog} A inp

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (inl {A} {B}) x ⟫ k) ≡ []
      denot-[] k = refl

      fs₀ = entry-flat base s alloc cl rs
      settle = record fs₀ { floc = R.sfin src ; falloc = R.A₁ ; fpc = length T + base }

      he : halted (proj₁ (exec-trace T s alloc)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) (R.whole src)) (R.hfin src)

      run₀ = SR.straight-steps {prog} T fs₀ (inj-straight 0 A (A +ᵀ B) n) span nh he
      eq : SR.after T fs₀ ≡ settle
      eq = cong (λ r → record fs₀ { floc = proj₁ r ; falloc = proj₂ r ; fpc = length T + base }) (R.whole src)
      run = subst (FlatSteps prog (length T) fs₀) eq run₀

      silent : chain-events run ≡ []
      silent = trans (chain-events-subst eq run₀)
                     (SR.straight-silent {prog} T fs₀ (inj-straight 0 A (A +ᵀ B) n) span nh he (inj-silent 0 A (A +ᵀ B) n))

      sum-of : CellAt {prog = prog} R.A₁ A x (sucLoc R.L) (R.sp src)
             → ValidAtWF {prog = prog} Heap R.A₁ {A +ᵀ B} (inj₁ x) R.L (R.sp src)
      sum-of (cell-ptr nd r lv v) = valid-inl-wf nd tt (R.tag-p src) r lv (R.live-suc src) (R.pad-p src) v
      sum-of (cell-inline rep r)  = valid-inl-reg-wf tt (R.tag-p src) rep r (R.live-suc src) (R.pad-p src)
      sum-of (cell-flat fl hr v)  = valid-inl-flat-wf fl tt (R.tag-p src) (R.live-suc src) (R.in-suc src) (R.pad-p src) v

      val = validityWF-mem-only (inj₁ x) R.L (R.sp src) (R.sfin src) refl refl (sum-of (R.cell-p src))

  obs-correct-inr : ∀ {A B} → IRObsCorrectF (inr {A} {B})
  obs-correct-inr {A} {B} n l prog base _ cr span _ _ mIn x s alloc cl ns0 nh inp k rs =
    record
      { traces-agree   = trans silent (sym (denot-[] k))
      ; value-realized =
          realized (length T) settle Heap R.A₁ run (λ _ → R.hfin src) (λ _ → refl) (λ ()) (λ _ → refl) (λ _ → refl)
                   (log-of run (trans silent (sym (denot-[] k))))
                   (λ { refl → at-loc R.L val (R.live-L src) refl val (R.live-L src) })
                   (m≤m+n k _)
                   (λ _ fr j bf → R.keep-bf src (AtStack fr j) bf) (λ _ hl bf → R.keep-bf src (AtDynamic hl) bf)
                   (λ _ → refl) (λ _ → R.bf-mono′ src) (λ _ → refl) (λ _ → FlatAlloc.alloc-bk {FS} R.N alloc)
      }
    where
      T = inj-trace 1 B (A +ᵀ B) n
      module R = Run {prog} 1 B (A +ᵀ B) n s alloc nh (s≤s (m≤n⊔m (size A) (size B)))
      src = mk-src {prog} B inp

      denot-[] : ∀ k → eventsAt s (⟪ evalᴰ (inr {A} {B}) x ⟫ k) ≡ []
      denot-[] k = refl

      fs₀ = entry-flat base s alloc cl rs
      settle = record fs₀ { floc = R.sfin src ; falloc = R.A₁ ; fpc = length T + base }

      he : halted (proj₁ (exec-trace T s alloc)) ≡ false
      he = trans (cong (λ r → halted (proj₁ r)) (R.whole src)) (R.hfin src)

      run₀ = SR.straight-steps {prog} T fs₀ (inj-straight 1 B (A +ᵀ B) n) span nh he
      eq : SR.after T fs₀ ≡ settle
      eq = cong (λ r → record fs₀ { floc = proj₁ r ; falloc = proj₂ r ; fpc = length T + base }) (R.whole src)
      run = subst (FlatSteps prog (length T) fs₀) eq run₀

      silent : chain-events run ≡ []
      silent = trans (chain-events-subst eq run₀)
                     (SR.straight-silent {prog} T fs₀ (inj-straight 1 B (A +ᵀ B) n) span nh he (inj-silent 1 B (A +ᵀ B) n))

      sum-of : CellAt {prog = prog} R.A₁ B x (sucLoc R.L) (R.sp src)
             → ValidAtWF {prog = prog} Heap R.A₁ {A +ᵀ B} (inj₂ x) R.L (R.sp src)
      sum-of (cell-ptr nd r lv v) = valid-inr-wf nd tt (R.tag-p src) r lv (R.live-suc src) (R.pad-p src) v
      sum-of (cell-inline rep r)  = valid-inr-reg-wf tt (R.tag-p src) rep r (R.live-suc src) (R.pad-p src)
      sum-of (cell-flat fl hr v)  = valid-inr-flat-wf fl tt (R.tag-p src) (R.live-suc src) (R.in-suc src) (R.pad-p src) v

      val = validityWF-mem-only (inj₂ x) R.L (R.sp src) (R.sfin src) refl refl (sum-of (R.cell-p src))
