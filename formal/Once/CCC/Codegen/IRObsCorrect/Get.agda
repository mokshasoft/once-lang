-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.Get
--
-- plan 0.123 B.4 α: READING A COMPONENT, once (`FlatLayout.get`).
--
-- `get C k` reads the component at word `k` of the flat value whose address
-- is in `Input1` into `Output`, in its register form: a node's or a scalar's
-- word (`load-at k`), a flat component's address (`addr-at k`, in its block
-- by the component's own witness, D381), or for a 0-word component the
-- container's pointer itself (`mov-to-output`, D381). Every clause that reads
-- a component — `fst`, `snd`, `case`'s arms, `Iter`, `apply`, the cata setup,
-- the re-suspension — runs this one step and gets the component's
-- `ResultPlace` from it.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Data.List as DL
open import Once.Denotation.Program using (IRFun)

module Once.CCC.Codegen.IRObsCorrect.Get (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Sum using (inj₁; inj₂)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (load-at; addr-at; mov-to-output; offsetLoc; module LocState; module ExecFinal; sv-as-loc;
  AbstractTrace; StoredValue; SV-Ptr; readReg; writeReg; writeReg-same; Input1; Output; AllocState)
open LocState using (regs; halted)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc)
open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; kind; get; get-k)
open import Once.CCC.Codegen.Size using (size)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float)
  renaming (_+_ to _+ᵀ_)
open import Once.CCC.Machine.LocMatchesMode using (LocMatchesMode)

module GetC {FS : FrameSemantics} where
  open Core {FS}
  open Mach {FS}

  ------------------------------------------------------------------------
  -- The text: `get` is one instruction, decided by the component's kind.
  ------------------------------------------------------------------------
  node-kind : ∀ {C : IRTy} → IsNode C → kind C ≡ word
  node-kind {μ-type _} _ = refl
  node-kind {ν-type _} _ = refl
  node-kind {_ ⇛ _}    _ = refl

  scalar-kind : ∀ {C : IRTy} → FitsInRegI C → kind C ≡ word
  scalar-kind fits-int   = refl
  scalar-kind fits-float = refl

  flat-kind : ∀ {C : IRTy} → IsFlat C → kind C ≡ flat
  flat-kind {Unit}   _ = refl
  flat-kind {_ * _}  _ = refl
  flat-kind {_ +ᵀ _} _ = refl

  node-size : ∀ {C : IRTy} → IsNode C → size C ≡ 1
  node-size {μ-type _} _ = refl
  node-size {ν-type _} _ = refl
  node-size {_ ⇛ _}    _ = refl

  scalar-size : ∀ {C : IRTy} → FitsInRegI C → size C ≡ 1
  scalar-size fits-int   = refl
  scalar-size fits-float = refl

  get-word : ∀ {C : IRTy} k → kind C ≡ word → get-k (kind C) (size C) k ≡ load-at k ∷ []
  get-word {C} k e rewrite e = refl

  get-flat0 : ∀ {C : IRTy} k → kind C ≡ flat → size C ≡ 0 → get-k (kind C) (size C) k ≡ mov-to-output ∷ []
  get-flat0 {C} k e z rewrite e | z = refl

  get-flat+ : ∀ {C : IRTy} k (n : ℕ) → kind C ≡ flat → size C ≡ suc n → get-k (kind C) (size C) k ≡ addr-at k ∷ []
  get-flat+ {C} k n e z rewrite e | z = refl

  -- the text at `pc` from its one instruction
  fetch-of : ∀ {prog : AbstractTrace} {t : AbstractTrace} {i} {pc : ℕ} → t ≡ i ∷ []
           → (∀ j → fetch t 0 ≡ just j → fetch prog pc ≡ just j) → fetch prog pc ≡ just i
  fetch-of refl at = at _ refl

  ------------------------------------------------------------------------
  -- The step: `Output` written, the pc past it, nothing else.
  ------------------------------------------------------------------------
  setOut : FlatState → StoredValue FS → FlatState
  setOut fs w = record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output w }
                          ; fpc  = suc (fpc fs) }

  -- what a read leaves: memory (a register write is invisible to `readLoc`)
  out-mem : ∀ (fs : FlatState) (w : StoredValue FS) l → readLoc (floc (setOut fs w)) l ≡ readLoc (floc fs) l
  out-mem fs w l = readLoc-stack-heap-eq (floc (setOut fs w)) (floc fs) l refl refl

  load-at-step : ∀ (prog : AbstractTrace) (fs : FlatState) k (loc : ValueLocation FS) (w : StoredValue FS)
               → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
               → readLoc (floc fs) (offsetLoc loc k) ≡ just w
               → flat-exec-instr (load-at k) prog fs ≡ setOut fs w
  load-at-step prog fs k loc w i1 r =
    cong (λ s′ → record fs { floc = s′ ; fpc = suc (fpc fs) })
      (trans (cong (λ x → ExecFinal.exec-load-at-resolved {FS} k Output (sv-as-loc x) (floc fs)) i1)
             (cong (λ m → ExecFinal.exec-load-with-value {FS} Output m (floc fs)) r))

  addr-at-step : ∀ (prog : AbstractTrace) (fs : FlatState) k (loc : ValueLocation FS)
               → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
               → InBlk (falloc fs) (offsetLoc loc k)
               → flat-exec-instr (addr-at k) prog fs ≡ setOut fs (SV-Ptr (offsetLoc loc k))
  addr-at-step prog fs k loc i1 ib =
    cong (λ s′ → record fs { floc = s′ ; fpc = suc (fpc fs) })
      (trans (cong (λ x → ExecFinal.exec-addr-at-resolved {FS} (AllocState.block-size (falloc fs)) k (sv-as-loc x) (floc fs)) i1)
             (cong (λ b → ExecFinal.exec-addr-in-block {FS} b (offsetLoc loc k) (floc fs)) ib))

  mov-out-step : ∀ (prog : AbstractTrace) (fs : FlatState) (loc : ValueLocation FS)
               → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
               → flat-exec-instr mov-to-output prog fs ≡ setOut fs (SV-Ptr loc)
  mov-out-step prog fs loc i1 = cong (setOut fs) i1

  ------------------------------------------------------------------------
  -- A 0-WORD VALUE IS VALID AT ANY LIVE HEAP ADDRESS: it has no word to be
  -- at (D381). Its components are 0-word too, so embedded (`cell-flat`) with
  -- a vacuous in-block witness.
  ------------------------------------------------------------------------
  live-any : ∀ {alloc : AllocState {FS}} {r o o′}
           → Live alloc (AtDynamic (heap-loc r o)) → Live alloc (AtDynamic (heap-loc r o′))
  live-any (BeforeFrontier.heap-before p) = BeforeFrontier.heap-before p

  lmm-any : ∀ {m} {h h′ : HeapLocation} → LocMatchesMode m (AtDynamic {FS} h) → LocMatchesMode m (AtDynamic {FS} h′)
  lmm-any {Heap}  l = l
  lmm-any {Stack} ()

  module _ {prog : AbstractTrace} where
    mutual
      zero-v : ∀ (C : IRTy) {m alloc c s} {h : HeapLocation} (r : _) (o : ℕ) → IsFlat C → size C ≡ 0
             → Live alloc (AtDynamic (heap-loc r o))
             → ValidAtWF {prog = prog} m alloc {C} c (AtDynamic h) s
             → ValidAtWF {prog = prog} m alloc {C} c (AtDynamic (heap-loc r o)) s
      zero-v Unit    r o _ _ _ valid-unit-wf = valid-unit-wf
      zero-v (A * B) r o _ z lv (valid-pair-wf lmm slb c₁ c₂) =
        valid-pair-wf (lmm-any lmm) (live-any lv)
          (zero-c A r o (m+n≡0⇒m≡0 (size A) z) lv c₁)
          (zero-c B r (size A + o) (m+n≡0⇒n≡0 (size A) z) (live-any lv) c₂)
      zero-v (A +ᵀ B)    r o _  () _ _
      zero-v Void        r o () _  _ _
      zero-v (A ⇛ B)     r o () _  _ _
      zero-v (μ-type F)  r o () _  _ _
      zero-v (ν-type F)  r o () _  _ _
      zero-v Int         r o () _  _ _
      zero-v Float       r o () _  _ _

      zero-c : ∀ (C : IRTy) {alloc c s} {h : HeapLocation} (r : _) (o : ℕ) → size C ≡ 0
             → Live alloc (AtDynamic (heap-loc r o))
             → CellAt {prog = prog} alloc C c (AtDynamic h) s
             → CellAt {prog = prog} alloc C c (AtDynamic (heap-loc r o)) s
      zero-c C r o z lv (cell-ptr nd _ _ _) = ⊥-elim (one≢zero (trans (sym (node-size nd)) z))
      zero-c C r o z lv (cell-inline (rep-prim fit) _) = ⊥-elim (one≢zero (trans (sym (scalar-size fit)) z))
      zero-c C r o z lv (cell-flat fl hr v) =
        cell-flat fl (λ p → ⊥-elim (no-pos (subst (0 <_) z p))) (zero-v C r o fl z lv v)

      one≢zero : 1 ≡ 0 → ⊥
      one≢zero ()

      no-pos : 0 < 0 → ⊥
      no-pos ()

    -- D395: a 0-word value rebuilt at the container's address uses only the
    -- container's block
    mutual
      zero-v-foot : ∀ (C : IRTy) {m alloc c s} {h : HeapLocation} (r : _) (o : ℕ) (fl : IsFlat C) (z : size C ≡ 0)
                    (lv : Live alloc (AtDynamic (heap-loc r o)))
                    (v : ValidAtWF {prog = prog} m alloc {C} c (AtDynamic h) s)
                  → ∀ l → l ∈ᶠ foot C (AtDynamic (heap-loc r o)) (zero-v C r o fl z lv v) → SameBlk (AtDynamic (heap-loc r o)) l
      zero-v-foot Unit r o _ _ _ valid-unit-wf l ()
      zero-v-foot (A * B) r o _ z lv (valid-pair-wf lmm slb c₁ c₂) l (here b) = b
      zero-v-foot (A * B) r o _ z lv (valid-pair-wf lmm slb c₁ c₂) l (there m)
        with AnyP.++⁻ (foot-cell A (zero-c A r o (m+n≡0⇒m≡0 (size A) z) lv c₁)) m
      ... | inj₁ p = zero-c-foot A r o (m+n≡0⇒m≡0 (size A) z) lv c₁ l p
      ... | inj₂ p = blk-trans {AtDynamic (heap-loc r o)} {AtDynamic (heap-loc r (size A + o))} refl
                       (zero-c-foot B r (size A + o) (m+n≡0⇒n≡0 (size A) z) (live-any lv) c₂ l p)
      zero-v-foot (A +ᵀ B)    r o _  () _ _
      zero-v-foot Void        r o () _  _ _
      zero-v-foot (A ⇛ B)     r o () _  _ _
      zero-v-foot (μ-type F)  r o () _  _ _
      zero-v-foot (ν-type F)  r o () _  _ _
      zero-v-foot Int         r o () _  _ _
      zero-v-foot Float       r o () _  _ _

      zero-c-foot : ∀ (C : IRTy) {alloc c s} {h : HeapLocation} (r : _) (o : ℕ) (z : size C ≡ 0)
                    (lv : Live alloc (AtDynamic (heap-loc r o)))
                    (x : CellAt {prog = prog} alloc C c (AtDynamic h) s)
                  → ∀ l → l ∈ᶠ foot-cell C (zero-c C r o z lv x) → SameBlk (AtDynamic (heap-loc r o)) l
      zero-c-foot C r o z lv (cell-ptr nd _ _ _) = ⊥-elim (one≢zero (trans (sym (node-size nd)) z))
      zero-c-foot C r o z lv (cell-inline (rep-prim fit) _) = ⊥-elim (one≢zero (trans (sym (scalar-size fit)) z))
      zero-c-foot C r o z lv (cell-flat fl hr v) = zero-v-foot C r o fl z lv v

    ------------------------------------------------------------------------
    -- THE READ: one step, and where the component is now.
    ------------------------------------------------------------------------
    -- D395: `K` is what the cell read uses; the component uses no more
    record GetOut (C : IRTy) (c : ⟦ C ⟧) (fs : FlatState) (K : Foot) : Set where
      field
        out    : StoredValue FS
        mode   : AllocMode
        step   : FlatSteps prog 1 fs (setOut fs out)
        silent : chain-events step ≡ []
        place  : ResultPlace {prog = prog} C mode (falloc fs) (falloc fs) c (floc (setOut fs out))
        in-K   : rp-foot place ⊆ᶠ K

    -- validity survives a register write
    val-out : ∀ {m C c l} (fs : FlatState) (w : StoredValue FS)
            → ValidAtWF {prog = prog} m (falloc fs) {C} c l (floc fs)
            → ValidAtWF {prog = prog} m (falloc fs) {C} c l (floc (setOut fs w))
    val-out {c = c} {l} fs w v = validityWF-mem-only c l (floc fs) _ refl refl v

    val-out-foot : ∀ {m C c l} (fs : FlatState) (w : StoredValue FS) (v : ValidAtWF {prog = prog} m (falloc fs) {C} c l (floc fs))
                 → foot C l (val-out fs w v) ≡ foot C l v
    val-out-foot {c = c} {l} fs w v = foot-mem-only c l (floc fs) _ refl refl v

    one-step : ∀ (fs : FlatState) {i fs′} → halted (floc fs) ≡ false → fetch prog (fpc fs) ≡ just i
             → flat-exec-instr i prog fs ≡ fs′ → FlatSteps prog 1 fs fs′
    one-step fs {i} {fs′} nh f e = (nh , f) ∷ subst (λ x → FlatSteps prog 0 x fs′) (sym e) []

    -- a silent instruction's step emits nothing
    one-step-silent : ∀ (fs : FlatState) {i fs′} (nh : halted (floc fs) ≡ false) (f : fetch prog (fpc fs) ≡ just i)
                    (e : flat-exec-instr i prog fs ≡ fs′) → event-of i fs ≡ []
                    → chain-events (one-step fs nh f e) ≡ []
    one-step-silent fs {i} nh f refl ev rewrite ev = refl

    -- the read, from its one step: the chain, its silence, and the place
    mk : ∀ {C : IRTy} {c : ⟦ C ⟧} {K} (fs : FlatState) {i} (w : StoredValue FS) (m : AllocMode)
       → halted (floc fs) ≡ false
       → fetch prog (fpc fs) ≡ just i
       → flat-exec-instr i prog fs ≡ setOut fs w
       → event-of i fs ≡ []
       → (pl : ResultPlace {prog = prog} C m (falloc fs) (falloc fs) c (floc (setOut fs w)))
       → rp-foot pl ⊆ᶠ K
       → GetOut C c fs K
    mk fs w m nh f e ev pl ik = record
      { out = w ; mode = m ; step = one-step fs nh f e ; silent = one-step-silent fs nh f e ev ; place = pl ; in-K = ik }

    -- a 0-word component: `Output` := the container's pointer, where the
    -- component is valid too
    get-zero : ∀ (C : IRTy) (k : ℕ) {c : ⟦ C ⟧} {mC} (fs : FlatState) (loc : ValueLocation FS)
             → halted (floc fs) ≡ false
             → (∀ i → fetch (get C k) 0 ≡ just i → fetch prog (fpc fs) ≡ just i)
             → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
             → Live (falloc fs) loc
             → IsFlat C
             → ValidAtWF {prog = prog} mC (falloc fs) {C} c (offsetLoc loc k) (floc fs)
             → size C ≡ 0
             → ∀ {K} → loc ∈ᶠ K
             → GetOut C c fs K
    get-zero C k fs (AtStack _ _) nh at i1 () fl v z
    get-zero C k {mC = mC} fs (AtDynamic (heap-loc r o)) nh at i1 lv fl v z lk =
      mk fs (SV-Ptr (AtDynamic (heap-loc r o))) mC nh
         (fetch-of {prog = prog} {pc = fpc fs} (get-flat0 k (flat-kind fl) z) at) (mov-out-step prog fs _ i1) refl
         (at-loc _ v′ lv (writeReg-same (regs (floc fs)) Output _) v′ lv)
         (λ l m → ∈ᶠ-blk lk (zero-v-foot C r o fl z lv v l (⊆ᶠ-≡ (val-out-foot fs (SV-Ptr (AtDynamic (heap-loc r o))) (zero-v C r o fl z lv v)) l m)))
      where v′ = val-out fs _ (zero-v C r o fl z lv v)

    get-run : ∀ (C : IRTy) (k : ℕ) {c : ⟦ C ⟧} (fs : FlatState) (loc : ValueLocation FS)
            → halted (floc fs) ≡ false
            → (∀ i → fetch (get C k) 0 ≡ just i → fetch prog (fpc fs) ≡ just i)
            → readReg (regs (floc fs)) Input1 ≡ SV-Ptr loc
            → Live (falloc fs) loc
            → (x : CellAt {prog = prog} (falloc fs) C c (offsetLoc loc k) (floc fs))
            → GetOut C c fs (loc ∷ foot-cell C x)
    -- a node: its pointer word
    get-run C k fs loc nh at i1 lv (cell-ptr {comp-loc = cl} {mC = mC} nd r clv v) =
      mk fs (SV-Ptr cl) mC nh (fetch-of {prog = prog} {pc = fpc fs} (get-word k (node-kind nd)) at)
         (load-at-step prog fs k loc _ i1 r) refl
         (at-loc cl (val-out fs _ v) clv (writeReg-same (regs (floc fs)) Output _) (val-out fs _ v) clv)
         (λ l m → there (there (⊆ᶠ-≡ (val-out-foot fs (SV-Ptr cl) v) l m)))
    -- a scalar: its word
    get-run C k fs loc nh at i1 lv (cell-inline (rep-prim fit) r) =
      mk fs _ Heap nh (fetch-of {prog = prog} {pc = fpc fs} (get-word k (scalar-kind fit)) at)
         (load-at-step prog fs k loc _ i1 r) refl
         (at-reg fit (writeReg-same (regs (floc fs)) Output _))
         ⊆ᶠ-[]
    -- a flat component: its address (words), or the container's (none)
    get-run C k fs loc nh at i1 lv (cell-flat {mC = mC} fl hr v) = by-size (size C) refl
      where
        by-size : ∀ (n : ℕ) → size C ≡ n → GetOut C _ fs (loc ∷ foot C (offsetLoc loc k) v)
        by-size zero    z = get-zero C k fs loc nh at i1 lv fl v z (here (blk-refl loc))
        by-size (suc n) z =
          mk fs (SV-Ptr (offsetLoc loc k)) mC nh
             (fetch-of {prog = prog} {pc = fpc fs} (get-flat+ k n (flat-kind fl) z) at)
             (addr-at-step prog fs k loc i1 (proj₂ (hr pos))) refl
             (at-loc _ (val-out fs _ v) (proj₁ (hr pos)) (writeReg-same (regs (floc fs)) Output _)
                       (val-out fs _ v) (proj₁ (hr pos)))
             (λ l m → there (⊆ᶠ-≡ (val-out-foot fs (SV-Ptr (offsetLoc loc k)) v) l m))
          where pos = subst (0 <_) (sym z) (s≤s z≤n)


  -- the first component is at the container's own address
  offset-zero : ∀ (l : ValueLocation FS) → offsetLoc l 0 ≡ l
  offset-zero (AtStack f k)             = refl
  offset-zero (AtDynamic (heap-loc r o)) = refl

  get-len : ∀ (C : IRTy) k → length (get C k) ≡ 1
  get-len C k = len (kind C) (size C)
    where
      len : ∀ kd n → length (get-k kd n k) ≡ 1
      len word _       = refl
      len flat zero    = refl
      len flat (suc _) = refl
