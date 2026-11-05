-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.X86-64.ArithBlockValue  (plan 0.123 α′ (f3c, f3d))
--
-- THE ARITH BLOCK'S VALUE, at the call site. At a non-faulting arith SigOp
-- the argument decoded (D386): a scalar is the literal in `Input1`, so in
-- `rdi` (D392, `in1-eq`); a compound is a heap pointer (never a stack one,
-- `StackPtrWF`) whose typed leaves are written cells at their flat offsets
-- (`FlatLeaf.leaf-at`), so the words at `rdi + 8k` (`heap-eq`,
-- `haddr-offset`), below the frontier and so below the block's frame (the
-- room check, D387). That is the block's `R-input` at its entry state; its
-- `Int` leaves are words (the store invariant, D391). The Core then gives the
-- out register: the block's meaning, which is the SigOp's output.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics; fs-numerics)
open FrameSemantics using (frame-word)
open import Once.CCC.Target.X86-64.Syntax using (slot-size; rax; rdi; rsp)
open import Once.Spec.Float.Dyadic using (binary64)
open import Once.Spec.Name using (CanonicalName)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

module Once.Adequacy.ArchCorrectness.X86-64.ArithBlockValue
  (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  (fmt-eq : FrameSemantics.float-format FS ≡ binary64)
  where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<_; _≤_)
open import Data.Nat.Properties
  using (≤-irrelevant; <-≤-trans; ≤-trans; *-comm; ∸-+-assoc; m+n≤o⇒m≤o∸n; +-monoʳ-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false)

open import Once.CCC.Machine.SMCore
open AbstractExec {FS} using (decode-at; exec-sigop-output; readTyped)
open MemOps {FS} using (readLoc)
open LocState using (regs; heapMem)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
import Once.CCC.Target.X86-64.Semantics as X

open import Once.Spec.Type using (Int; Float; Base; ∅ₖ; b-Int; b-Float; b-*)
open import Once.Type using (fits-int; fits-float)
open import Once.Spec.Numerics using (TargetNum; mkTargetNum)
open import Once.Target.Arch using (x86-64; arch-numerics)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo; blockV; Internal; internal-pure)
open SigOpInfo using (sem; baseA)
open import Once.SigOp.Words using (Words; IM; fromM; toWord-fromM; words-below)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR; shape-as-type; numtype-as-type)
open import Once.Semantics.Machine using (⟦_⟧)
open import Once.Arith.Machine.Shape
  using (InputShape; shape-unit; shape-int; shape-float; shape-pair; Path; here-int; here-flt; go-fst; go-snd; ⌊_⌋ᴾ; flat-off)
open import Once.Arith.Machine.Compile using (compile-abs; normalize; required-scratch)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.SigOp.BlockSem using (block-semM)
open import Once.Arith.Backend.X86-64.Dispatch using (dispatch-arith)
open import Once.Adequacy.CPU.X86-64 using (val-x86-64)
import Once.Adequacy.ArchCorrectness.ArithSimX86-64 as AS
open import Once.CCC.Machine.FlatLeaf FS using (leafM; fitsN; leaf-at)

open import Once.Adequacy.ArchCorrectness.X86-64.FlatSimulation o FS word-eq fmt-eq
  using (CompiledCorr; dataCorr; xrreg; module C)
open C using (HeapView; hfront; haddr; FlatCorr; enc-sv)
import Once.Adequacy.ArchCorrectness.FlatCore.RunLow as RL
open RL o FS slot-size word-eq using (RunLow; sigop-decodes; run-flat-wf; run-stack-ptr)
open import Once.CCC.Machine.FlatStackPtr FS using (StackPtrWF; StackPtrOK; module SPInv)
import Once.Adequacy.ArchCorrectness.FlatCore.ArithOutput FS as AO
open import Once.CCC.Machine.FlatStoreWF FS using (IMfs)

------------------------------------------------------------------------
-- The machine's numerics are x86-64's.
------------------------------------------------------------------------
tn = arch-numerics x86-64

numerics-agree : fs-numerics FS ≡ tn
numerics-agree = mk (cong (8 *_) word-eq) fmt-eq
  where
    mk : ∀ {a b f g p q} → a ≡ b → f ≡ g → mkTargetNum a f p ≡ mkTargetNum b g q
    mk refl refl = cong (mkTargetNum _ _) (≤-irrelevant _ _)

------------------------------------------------------------------------
-- A leaf's word, through the two readings of the same tree.
------------------------------------------------------------------------
-- a leaf's value is a word at either kind
leafℕ : ∀ m → ⟦ numtype-as-type m ⟧ → ℕ
leafℕ NInt   x = x
leafℕ NFloat x = x

leafWord-fromM : ∀ N {sh m} (p : Path sh m) (a : _) → AS.Sim.leafWord N p (fromM tn sh a) ≡ leafℕ m (leafM p a)
leafWord-fromM N here-int   a = refl
leafWord-fromM N here-flt   a = refl
leafWord-fromM N (go-fst p) a = leafWord-fromM N p (proj₁ a)
leafWord-fromM N (go-snd p) a = leafWord-fromM N p (proj₂ a)

enc-fitsN : ∀ (hv : HeapView) (m : NumType) v → enc-sv hv (SV-Lit (fitsN m) v) ≡ leafℕ m v
enc-fitsN hv NInt   v = refl
enc-fitsN hv NFloat v = refl

------------------------------------------------------------------------
-- The entry leaves.
------------------------------------------------------------------------
module _ {hv : HeapView} (prog : AbstractTrace) (fs : FlatState) (s : X.State)
         (r : RunLow prog fs) (cc : CompiledCorr hv prog fs s) (n : ℕ)
         (room : hfront hv + (8 + 8 * n) ≤ xrreg s rsp) where

  private
    ls = floc fs
    rdi≡ : xrreg s rdi ≡ enc-sv hv (readReg (regs ls) Input1)
    rdi≡ = FlatCorr.in1-eq (dataCorr cc)

    below : ∀ {x} → x < hfront hv → x < (xrreg s rsp ∸ 8) ∸ 8 * n
    below lt = <-≤-trans lt (subst (hfront hv ≤_) (sym (∸-+-assoc (xrreg s rsp) 8 (8 * n)))
                                   (m+n≤o⇒m≤o∸n (hfront hv) room))

    -- a compound input: a heap pointer, its leaves the cells at their offsets
    mem-leaf : ∀ {l r′ m} (hl : _) {a} → readReg (regs ls) Input1 ≡ SV-Ptr (AtDynamic hl)
             → readTyped (shape-as-type (shape-pair l r′)) (AtDynamic hl) ls ≡ just a
             → (P : Path (shape-pair l r′) m)
             → (X.readMem (X.State.memory s) (xrreg s rdi + 8 * flat-off P) ≡ just (leafℕ m (leafM P a)))
               × (xrreg s rdi + 8 * flat-off P < (xrreg s rsp ∸ 8) ∸ 8 * n)
    mem-leaf {m = m} hl {a} in1 dT P = val , bnd
      where
        k = flat-off P
        cell : heapMem ls (offsetHL hl k) ≡ just (SV-Lit (fitsN m) (leafM P a))
        cell = leaf-at P (AtDynamic hl) ls a dT
        addr : xrreg s rdi + 8 * k ≡ haddr hv (offsetHL hl k)
        addr = trans (cong (λ w → w + 8 * k) (trans rdi≡ (cong (enc-sv hv) in1)))
                     (trans (cong (haddr hv hl +_) (*-comm 8 k))
                            (sym (C.haddr-offset hv hl k)))
        val = trans (cong (X.readMem (X.State.memory s)) addr)
                    (trans (FlatCorr.heap-eq (dataCorr cc) _ cell)
                           (cong just (enc-fitsN hv m (leafM P a))))
        bnd = subst (_< (xrreg s rsp ∸ 8) ∸ 8 * n) (sym addr)
                    (below (C.HeapView.dom-below hv (FlatCorr.dom-written (dataCorr cc) _ cell)))

  entry-leaves : ∀ {sh} (bt : Base ∅ₖ (shape-as-type sh)) {a}
               → decode-at bt (readReg (regs ls) Input1) ls ≡ just a
               → ∀ {m} (p : Path sh m) → AS.EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (AS.Sim.leafWord (8 * n) p (fromM tn sh a))
  entry-leaves {sh} bt {a} d p = subst (AS.EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p)) (sym (leafWord-fromM (8 * n) p a)) (go bt (readReg (regs ls) Input1) refl d p)
    where
      go : ∀ {sh} (bt : Base ∅ₖ (shape-as-type sh)) (sv : StoredValue FS) → readReg (regs ls) Input1 ≡ sv → ∀ {a}
         → decode-at bt sv ls ≡ just a → ∀ {m} (p : Path sh m) → AS.EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (leafℕ m (leafM p a))
      go {shape-int}   b-Int   (SV-Lit fits-int v)   e refl here-int = trans rdi≡ (cong (enc-sv hv) e)
      go {shape-int}   b-Int   (SV-Lit fits-float v) e () here-int
      go {shape-int}   b-Int   (SV-Ptr _)            e () here-int
      go {shape-int}   b-Int   (SV-Tag _)            e () here-int
      go {shape-int}   b-Int   (SV-Code _)           e () here-int
      go {shape-float} b-Float (SV-Lit fits-float v) e refl here-flt = trans rdi≡ (cong (enc-sv hv) e)
      go {shape-float} b-Float (SV-Lit fits-int v)   e () here-flt
      go {shape-float} b-Float (SV-Ptr _)            e () here-flt
      go {shape-float} b-Float (SV-Tag _)            e () here-flt
      go {shape-float} b-Float (SV-Code _)           e () here-flt
      go {shape-unit} bt sv e d ()
      go {shape-pair l r′} (b-* _ _) (SV-Ptr (AtDynamic hl)) e dT (go-fst q) = mem-leaf hl e dT (go-fst q)
      go {shape-pair l r′} (b-* _ _) (SV-Ptr (AtDynamic hl)) e dT (go-snd q) = mem-leaf hl e dT (go-snd q)
      go {shape-pair l r′} (b-* _ _) (SV-Ptr (AtStack f k))  e dT P =
        ⊥-elim (subst StackPtrOK e (SPInv.sp-regs (run-stack-ptr prog fs r) Input1))
      go {shape-pair l r′} (b-* _ _) (SV-Lit _ _) e () P
      go {shape-pair l r′} (b-* _ _) (SV-Tag _)   e () P
      go {shape-pair l r′} (b-* _ _) (SV-Code _)  e () P

------------------------------------------------------------------------
-- THE VALUE: the dispatch's `rax` is the SigOp's output.
------------------------------------------------------------------------
value-int : ∀ {hv : HeapView} prog fs s {sh} (si : SigOpInfo (shape-as-type sh) Int) (e : MArithIR sh NInt)
          → sem si ≡ blockV e refl refl
          → RunLow prog fs → Internal (sem si) → CompiledCorr hv prog fs s
          → fetch prog (fpc fs) ≡ just (instr-sigop si) → LocState.halted (floc fs) ≡ false
          → hfront hv + (8 + 8 * required-scratch (normalize e)) ≤ xrreg s rsp
          → xrreg (dispatch-arith val-x86-64 (emit-program (compile-abs (normalize e))) (required-scratch (normalize e)) s) rax
            ≡ enc-sv hv (exec-sigop-output si (floc fs))
value-int {hv} prog fs s {sh} si e eq r int cc ftq h room with sigop-decodes prog fs si r h ftq (internal-pure int)
... | a , d =
  trans (AS.block-value-x86-64 e (fromM tn sh a) s (entry-leaves prog fs s r cc n room (baseA si) d) ib)
    (trans (cong (block-semM e tn) (toWord-fromM tn sh a))
      (trans (cong (λ t → block-semM e t a) (sym numerics-agree))
             (cong (enc-sv hv) (sym (AO.block-output si e eq (floc fs) d)))))
  where
    n = required-scratch (normalize e)
    ws : Words IMfs (shape-as-type sh) a
    ws = AO.input-words (run-flat-wf prog fs r) (baseA si) (readReg (regs (floc fs)) Input1) refl d
    ib = words-below tn sh a (subst (λ t → Words (IM t) (shape-as-type sh) a) numerics-agree ws)

value-flt : ∀ {hv : HeapView} prog fs s {sh} (si : SigOpInfo (shape-as-type sh) Float) (e : MArithIR sh NFloat)
          → sem si ≡ blockV e refl refl
          → RunLow prog fs → Internal (sem si) → CompiledCorr hv prog fs s
          → fetch prog (fpc fs) ≡ just (instr-sigop si) → LocState.halted (floc fs) ≡ false
          → hfront hv + (8 + 8 * required-scratch e) ≤ xrreg s rsp
          → xrreg (dispatch-arith val-x86-64 (emit-program (compile-abs e)) (required-scratch e) s) rax
            ≡ enc-sv hv (exec-sigop-output si (floc fs))
value-flt {hv} prog fs s {sh} si e eq r int cc ftq h room with sigop-decodes prog fs si r h ftq (internal-pure int)
... | a , d =
  trans (AS.block-value-x86-64-flt e (fromM tn sh a) s (entry-leaves prog fs s r cc (required-scratch e) room (baseA si) d))
    (trans (cong (block-semM e tn) (toWord-fromM tn sh a))
      (trans (cong (λ t → block-semM e t a) (sym numerics-agree))
             (cong (enc-sv hv) (sym (AO.block-output-flt si e eq (floc fs) d)))))
