-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.RiscV64.ArithBlockValue  (plan 0.123 α′ (f3c, f3d))
--
-- THE ARITH BLOCK'S VALUE, at the call site (riscv64; x86-64's twin). At a
-- non-faulting arith SigOp the argument decoded (D392): a scalar is the literal
-- in `Input1`, so in `t0` (D398, `in1-eq`); a compound is a pointer whose typed leaves are written cells at their flat
-- offsets (`FlatLeaf.leaf-at`), so the words at `t0 + 8k` (`heap-eq`,
-- `haddr-offset`), below the frontier and so below the block's frame (the
-- room check, D393) — or, at a stack pointer (D452 (d)), the words of the live
-- window the SigOp's check passed, above the block's frame. That is the block's `R-input` at its entry state; its
-- `Int` leaves are words (the store invariant, D397). The Core then gives the
-- out register: the block's meaning, which is the SigOp's output.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics; fs-numerics)
open FrameSemantics using (frame-word)
open import Once.CCC.Target.RiscV64.Syntax using (slot-size)
open import Once.Target.RiscV64.PhysReg using (a0; t0; sp)
open import Once.Spec.Float.Dyadic using (binary64)
open import Once.Spec.Name using (CanonicalName)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

module Once.Adequacy.ArchCorrectness.RiscV64.ArithBlockValue
  (o : CanonicalName)
  (FS : FrameSemantics)
  (word-eq : frame-word FS ≡ slot-size)
  (fmt-eq : FrameSemantics.float-format FS ≡ binary64)
  where

open import Data.Nat using (ℕ; _+_; _*_; _∸_; _<_; _≤_)
open import Data.Nat.Properties
  using (≤-irrelevant; <-≤-trans; *-comm; m+n≤o⇒m≤o∸n; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (false; true)

open import Once.CCC.Machine.SMCore
open import Once.Memory.HeapAddress using (offsetHL)
open AbstractExec {FS} using (decode-at; exec-sigop-output; readTyped; arg-words; tsize)
open ExecFinal {FS} using (range-ok; live-frames)
open MemOps {FS} using (readLoc)
open LocState using (regs; heapMem)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.Flat
open FlatMachine {FS}
open FlatState using (floc; fpc; falloc)
import Once.CCC.Target.RiscV64.Semantics as X

open import Once.Spec.Type using (Int; Float; Base; ∅ₖ; b-Int; b-Float; b-*)
open import Once.Type using (fits-int; fits-float)
open import Once.Spec.Numerics using (mkTargetNum)
open import Once.Target.Arch using (riscv64; arch-numerics)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo; blockV; Internal; internal-pure)
open SigOpInfo using (sem; baseA)
open import Once.SigOp.Words using (Words; IM; fromM; toWord-fromM; words-below)
open import Once.Arith.Type using (NumType; NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR; shape-as-type; numtype-as-type)
open import Once.Semantics.Machine using (module Value)
open Value using (⟦_⟧)
open import Once.Arith.Machine.Shape
  using (shape-unit; shape-int; shape-float; shape-pair; Path; here-int; here-flt; go-fst; go-snd; ⌊_⌋ᴾ; flat-off)
open import Once.Arith.Machine.Compile using (compile-abs; normalize; required-scratch)
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.SigOp.BlockSem using (block-semM)
open import Once.Arith.Backend.RiscV64.Dispatch using (dispatch-arith)
open import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 using (val-riscv64)
import Once.Adequacy.ArchCorrectness.ArithSimRiscV64 as AS
open import Once.CCC.Machine.FlatLeaf FS using (leafM; fitsN; leaf-at; off-lt; tsize-shape)

open import Once.Adequacy.ArchCorrectness.RiscV64.FlatSimulation o FS word-eq fmt-eq
  using (rreg'; module CompiledCorrespondence)
open CompiledCorrespondence using (CompiledCorr)
open CompiledCorrespondence.CompiledCorr using (dataCorr)
import Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence
module C = Once.Adequacy.ArchCorrectness.RiscV64.FlatCorrespondence FS word-eq
  using (module FlatCorrespondence)
open C using ()
open C.FlatCorrespondence using (HeapView; enc-sv; module FlatCorr)
open C.FlatCorrespondence.HeapView using (hfront; haddr)
import Once.Adequacy.ArchCorrectness.FlatCore.RunLow as RL
open RL o FS slot-size word-eq using (RunLow; sigop-decodes; sigop-gated; run-flat-wf)
import Data.Sum
open import Data.Sum using (_⊎_)
import Data.Bool
import Once.Adequacy.ArchCorrectness.FlatCore.ArithOutput FS as AO
open import Once.CCC.Machine.FlatStoreWF FS using (IMfs)

------------------------------------------------------------------------
-- The machine's numerics are riscv64's.
------------------------------------------------------------------------
tn = arch-numerics riscv64

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
         (room : hfront hv + 8 * n ≤ rreg' s sp) where

  private
    ls = floc fs
    t0≡ : rreg' s t0 ≡ enc-sv hv (readReg (regs ls) Input1)
    t0≡ = FlatCorr.in1-eq (dataCorr cc)

    below : ∀ {x} → x < hfront hv → x < rreg' s sp ∸ 8 * n
    below lt = <-≤-trans lt (m+n≤o⇒m≤o∸n (hfront hv) room)

    -- a compound input: a heap pointer, its leaves the cells at their offsets
    mem-leaf′ : ∀ {l r′ m} (hl : _) {a} → readReg (regs ls) Input1 ≡ SV-Ptr (AtDynamic hl)
             → readTyped (shape-as-type (shape-pair l r′)) (AtDynamic hl) ls ≡ just a
             → (P : Path (shape-pair l r′) m)
             → (X.readMem (X.State.memory s) (rreg' s t0 + 8 * flat-off P) ≡ just (leafℕ m (leafM P a)))
               × ((rreg' s t0 + 8 * flat-off P < rreg' s sp ∸ 8 * n)
                  ⊎ ((rreg' s sp ≤ rreg' s t0 + 8 * flat-off P) × (8 * n ≤ rreg' s sp)))
    mem-leaf′ {m = m} hl {a} in1 dT P = val , Data.Sum.inj₁ bnd
      where
        k = flat-off P
        cell : heapMem ls (offsetHL hl k) ≡ just (SV-Lit (fitsN m) (leafM P a))
        cell = leaf-at P (AtDynamic hl) ls a dT
        addr : rreg' s t0 + 8 * k ≡ haddr hv (offsetHL hl k)
        addr = trans (cong (λ w → w + 8 * k) (trans t0≡ (cong (enc-sv hv) in1)))
                     (trans (cong (haddr hv hl +_) (*-comm 8 k))
                            (sym (C.FlatCorrespondence.haddr-offset hv hl k)))
        val = trans (cong (X.readMem (X.State.memory s)) addr)
                    (trans (FlatCorr.heap-eq (dataCorr cc) _ cell)
                           (cong just (enc-fitsN hv m (leafM P a))))
        bnd = subst (_< rreg' s sp ∸ 8 * n) (sym addr)
                    (below (C.FlatCorrespondence.HeapView.dom-below hv (FlatCorr.dom-written (dataCorr cc) _ cell)))

    mem-leaf : ∀ {l r′ m} (hl : _) {a} → readReg (regs ls) Input1 ≡ SV-Ptr (AtDynamic hl)
             → readTyped (shape-as-type (shape-pair l r′)) (AtDynamic hl) ls ≡ just a
             → (P : Path (shape-pair l r′) m)
             → AS.EntryLeaf n s ⌊ P ⌋ᴾ (flat-off P) (leafℕ m (leafM P a))
    mem-leaf hl in1 dT (go-fst P) = mem-leaf′ hl in1 dT (go-fst P)
    mem-leaf hl in1 dT (go-snd P) = mem-leaf′ hl in1 dT (go-snd P)

    -- D452 (d): a compound input at a stack address: its leaves the words of the
    -- window the SigOp's check passed, above the block's frame
    stack-leaf′ : ∀ {l r′ m} f j {a} → readReg (regs ls) Input1 ≡ SV-Ptr (AtStack f j)
                → range-ok (live-frames (falloc fs)) (tsize (shape-as-type (shape-pair l r′))) (SV-Ptr (AtStack f j)) ≡ true
                → readTyped (shape-as-type (shape-pair l r′)) (AtStack f j) ls ≡ just a
                → (P : Path (shape-pair l r′) m)
                → (X.readMem (X.State.memory s) (rreg' s t0 + 8 * flat-off P) ≡ just (leafℕ m (leafM P a)))
                  × ((rreg' s t0 + 8 * flat-off P < rreg' s sp ∸ 8 * n)
                     ⊎ ((rreg' s sp ≤ rreg' s t0 + 8 * flat-off P) × (8 * n ≤ rreg' s sp)))
    stack-leaf′ {l} {r′} {m} f j {a} in1 g dT P = val , Data.Sum.inj₂ (bnd , rm)
      where
        k = flat-off P
        cell : LocState.stackMem ls f (k + j) ≡ just (SV-Lit (fitsN m) (leafM P a))
        cell = leaf-at P (AtStack f j) ls a dT
        win = C.FlatCorrespondence.range-win (live-frames (falloc fs)) _ f j k
                (subst (k <_) (sym (tsize-shape (shape-pair l r′))) (off-lt P)) g
        sar = C.FlatCorrespondence.stack-arg-read k f j _ (dataCorr cc) in1 win cell
        addr : rreg' s t0 + 8 * k ≡ rreg' s t0 + k * 8
        addr = cong (rreg' s t0 +_) (*-comm 8 k)
        val = trans (cong (X.readMem (X.State.memory s)) addr)
                    (trans (proj₁ sar) (cong just (enc-fitsN hv m (leafM P a))))
        bnd = subst (rreg' s sp ≤_) (sym addr) (proj₂ sar)
        rm : 8 * n ≤ rreg' s sp
        rm = ≤-trans (Data.Nat.Properties.m≤n+m (8 * n) (hfront hv)) room

    stack-leaf : ∀ {l r′ m} f j {a} → readReg (regs ls) Input1 ≡ SV-Ptr (AtStack f j)
               → range-ok (live-frames (falloc fs)) (tsize (shape-as-type (shape-pair l r′))) (SV-Ptr (AtStack f j)) ≡ true
               → readTyped (shape-as-type (shape-pair l r′)) (AtStack f j) ls ≡ just a
               → (P : Path (shape-pair l r′) m)
               → AS.EntryLeaf n s ⌊ P ⌋ᴾ (flat-off P) (leafℕ m (leafM P a))
    stack-leaf f j in1 g dT (go-fst P) = stack-leaf′ f j in1 g dT (go-fst P)
    stack-leaf f j in1 g dT (go-snd P) = stack-leaf′ f j in1 g dT (go-snd P)

  entry-leaves : ∀ {sh} (bt : Base ∅ₖ (shape-as-type sh)) {a}
               → range-ok (live-frames (falloc fs)) (arg-words bt) (readReg (regs ls) Input1) ≡ true
               → decode-at bt (readReg (regs ls) Input1) ls ≡ just a
               → ∀ {m} (p : Path sh m) → AS.EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (AS.Sim.leafWord (8 * n) p (fromM tn sh a))
  entry-leaves {sh} bt {a} gw d p = subst (AS.EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p)) (sym (leafWord-fromM (8 * n) p a)) (go bt (readReg (regs ls) Input1) refl gw d p)
    where
      go : ∀ {sh} (bt : Base ∅ₖ (shape-as-type sh)) (sv : StoredValue FS) → readReg (regs ls) Input1 ≡ sv
         → range-ok (live-frames (falloc fs)) (arg-words bt) sv ≡ true → ∀ {a}
         → decode-at bt sv ls ≡ just a → ∀ {m} (p : Path sh m) → AS.EntryLeaf n s ⌊ p ⌋ᴾ (flat-off p) (leafℕ m (leafM p a))
      go {shape-int}   b-Int   (SV-Lit fits-int v)   e g refl here-int = trans t0≡ (cong (enc-sv hv) e)
      go {shape-int}   b-Int   (SV-Lit fits-float v) e g () here-int
      go {shape-int}   b-Int   (SV-Ptr _)            e g () here-int
      go {shape-int}   b-Int   (SV-Tag _)            e g () here-int
      go {shape-int}   b-Int   (SV-Code _)           e g () here-int
      go {shape-float} b-Float (SV-Lit fits-float v) e g refl here-flt = trans t0≡ (cong (enc-sv hv) e)
      go {shape-float} b-Float (SV-Lit fits-int v)   e g () here-flt
      go {shape-float} b-Float (SV-Ptr _)            e g () here-flt
      go {shape-float} b-Float (SV-Tag _)            e g () here-flt
      go {shape-float} b-Float (SV-Code _)           e g () here-flt
      go {shape-unit} bt sv e g d ()
      go {shape-pair l r′} (b-* _ _) (SV-Ptr (AtDynamic hl)) e g dT (go-fst q) = mem-leaf hl e dT (go-fst q)
      go {shape-pair l r′} (b-* _ _) (SV-Ptr (AtDynamic hl)) e g dT (go-snd q) = mem-leaf hl e dT (go-snd q)
      go {shape-pair l r′} (b-* _ _) (SV-Ptr (AtStack f k))  e g dT P = stack-leaf f k e g dT P
      go {shape-pair l r′} (b-* _ _) (SV-Lit _ _) e g () P
      go {shape-pair l r′} (b-* _ _) (SV-Tag _)   e g () P
      go {shape-pair l r′} (b-* _ _) (SV-Code _)  e g () P

-- the argument's half of the SigOp's window check (`sigop-gate`)
private
  ∧-l : ∀ a b → (a Data.Bool.∧ b) ≡ true → a ≡ true
  ∧-l true b _ = refl
  ∧-l false b ()

gate-in : ∀ prog fs {A B} (si : SigOpInfo A B) → RunLow prog fs → LocState.halted (floc fs) ≡ false
        → fetch prog (fpc fs) ≡ just (instr-sigop si)
        → range-ok (live-frames (falloc fs)) (arg-words (baseA si)) (readReg (regs (floc fs)) Input1) ≡ true
gate-in prog fs si r h ftq = ∧-l _ _ (sigop-gated prog fs si r h ftq)

------------------------------------------------------------------------
-- THE VALUE: the dispatch's `a0` is the SigOp's output.
------------------------------------------------------------------------
value-int : ∀ {hv : HeapView} prog fs s {sh} (si : SigOpInfo (shape-as-type sh) Int) (e : MArithIR sh NInt)
          → sem si ≡ blockV e refl refl
          → RunLow prog fs → Internal (sem si) → CompiledCorr hv prog fs s
          → fetch prog (fpc fs) ≡ just (instr-sigop si) → LocState.halted (floc fs) ≡ false
          → hfront hv + 8 * required-scratch (normalize e) ≤ rreg' s sp
          → rreg' (dispatch-arith val-riscv64 (emit-program (compile-abs (normalize e))) (required-scratch (normalize e)) s) a0
            ≡ enc-sv hv (exec-sigop-output si (floc fs))
value-int {hv} prog fs s {sh} si e eq r int cc ftq h room with sigop-decodes prog fs si r h ftq (internal-pure int)
... | a , d =
  trans (AS.block-value-riscv64 e (fromM tn sh a) s (entry-leaves prog fs s r cc n room (baseA si) (gate-in prog fs si r h ftq) d) ib)
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
          → hfront hv + 8 * required-scratch e ≤ rreg' s sp
          → rreg' (dispatch-arith val-riscv64 (emit-program (compile-abs e)) (required-scratch e) s) a0
            ≡ enc-sv hv (exec-sigop-output si (floc fs))
value-flt {hv} prog fs s {sh} si e eq r int cc ftq h room with sigop-decodes prog fs si r h ftq (internal-pure int)
... | a , d =
  trans (AS.block-value-riscv64-flt e (fromM tn sh a) s (entry-leaves prog fs s r cc (required-scratch e) room (baseA si) (gate-in prog fs si r h ftq) d))
    (trans (cong (block-semM e tn) (toWord-fromM tn sh a))
      (trans (cong (λ t → block-semM e t a) (sym numerics-agree))
             (cong (enc-sv hv) (sym (AO.block-output-flt si e eq (floc fs) d)))))
