-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.IRObsCorrect.TwoCell.Copy   (D393, plan 0.123 β1/β2)
--
-- THE TWO-CELL BUILD OF A COPY. A flat value that a node keeps (a closure's
-- environment, a suspension's seed, an `in-ν` layer) is first copied into a
-- fresh block (`NodeCopy`), and the two-cell build then keeps the COPY's
-- address in cell 0:
--
--   node-copy-trace E n ++ mov-to-input ∷ two-cell-trace (suc (suc n)) l
--
-- `CopyRun` states the whole straight segment's run and the facts the
-- clauses read off its end state, relative to the ENTRY state: the build's
-- facts (`TwoCellBuild`, from the copy's end state) composed with the copy's.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
import Once.CCC.Machine.SMCore as SMCore

import Data.List as DL
open import Once.Denotation.Program using (IRFun)
module Once.CCC.Codegen.IRObsCorrect.TwoCell.Copy (o : CanonicalName) (tbl : DL.List IRFun) where

open import Once.CCC.Codegen.IRObsCorrect.Machine o tbl
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack; ValueLocation)
open import Once.CCC.Machine.SMCore
  using (AllocState; AbstractTrace; LocState; StoredValue; sucLoc; readReg; writeReg; writeReg-same; Input1; Output;
         SV-Ptr; mov-to-input; module LocState; module AllocState)
open AllocState using (next-slot; next-heap-ref; current-frame; saved-frames)
open LocState using (halted; regs)
import Once.IRTy as IT
open import Once.IRTy using (IRTy)

open import Once.CCC.Codegen.FlatLayout using (Kind; word; flat; kind)
open import Once.CCC.Codegen.IRToTrace o using (node-copy-trace)
open import Once.CCC.Codegen.IRObsCorrect.NodeCopy o tbl using (module NodeCopyC)
open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Run o tbl
open import Once.CCC.Codegen.IRObsCorrect.TwoCell.Build o tbl
open import Once.CCC.Codegen.StraightRun using (module StraightRunAPI)
import Once.CCC.Machine.FlatPut as FlatPut
import Once.CCC.Machine.FlatAlloc as FlatAlloc
open import Data.List.Relation.Unary.All using ([]; _∷_)

import Once.Denotation.ValueDomain as ValueDomain
import Data.Product as DP

-- a flat kind is neither a node nor a scalar
module KindFacts {FS : FrameSemantics} where
  open Core {FS}

  flat-not-node : ∀ (T : IRTy) → kind T ≡ flat → IsNode T → ⊥
  flat-not-node (_ IT.⇛ _)    () _
  flat-not-node (IT.μ-type _) () _
  flat-not-node (IT.ν-type _) () _
  flat-not-node IT.Unit       _ ()
  flat-not-node IT.Void       _ ()
  flat-not-node (_ IT.* _)    _ ()
  flat-not-node (_ IT.+ _)   _ ()
  flat-not-node IT.Int        () _
  flat-not-node IT.Float      () _

  flat-not-fit : ∀ (T : IRTy) → kind T ≡ flat → IT.FitsInRegI T → ⊥
  flat-not-fit IT.Int   () _
  flat-not-fit IT.Float () _

module CopyTwoCellC {FS : FrameSemantics} where

  open Core {FS}
  open Mach {FS}
  open TwoCellRunC {FS}
  open TwoCellBuildC {FS}
  open KindFacts {FS}
  open SMCore.AbstractExec {FS} using (exec-trace; exec-trace-cons)
  open import Once.CCC.Machine.SMPrimitives using (module TraceComposition)
  open TraceComposition {FS} using (exec-trace-append)
  open FlatEventTrace {FS} using (chain-events-subst)

  copy-two-cell-trace : IRTy → ℕ → ℕ → AbstractTrace
  copy-two-cell-trace E n l = node-copy-trace E n DL.++ mov-to-input ∷ two-cell-trace (suc (suc n)) l

  module CopyRun
    (E : IRTy) (kf : kind E ≡ flat)
    (n l : ℕ) (prog : AbstractTrace) (base : ℕ)
    (s : LocState FS) (alloc : AllocState {FS}) (cl : StoredValue FS) (rs : List ℕ)
    (n≤ : next-slot alloc ≤ n) (nh : halted s ≡ false)
    (span : SpanAt prog base (copy-two-cell-trace E n l))
    {x : ⟦ E ⟧} (src : FlatPut.Src {FS} {prog} alloc s E x (readReg (regs s) Input1))
    where

    module NC = NodeCopyC.Run {FS} {prog} E n s alloc nh
    A₁ = NC.A₁
    s₁ = NC.sfin src
    s₂ = proj₁ (exec-abstract mov-to-input s₁ A₁)

    in1₂ : readReg (regs s₂) Input1 ≡ SV-Ptr NC.Nd
    in1₂ = writeReg-same (regs s₁) Input1 (readReg (regs s₁) Output)

    P : AbstractTrace
    P = node-copy-trace E n

    base₂ : ℕ
    base₂ = suc (length P + base)

    span₂ : SpanAt prog base₂ (two-cell-trace (suc (suc n)) l)
    span₂ k i eq =
      subst (λ m → fetch prog m ≡ just i) (shuf (length P) k base)
            (span (length P + suc k) i
                  (trans (fetch-++-right P (mov-to-input ∷ two-cell-trace (suc (suc n)) l) (suc k)) eq))
      where
        shuf : ∀ a b c → (a + suc b) + c ≡ b + suc (a + c)
        shuf a b c = trans (+-assoc a (suc b) c)
                    (trans (+-suc a (b + c))
                    (trans (cong suc (sym (+-assoc a b c)))
                    (trans (cong (λ z → suc (z + c)) (+-comm a b))
                    (trans (cong suc (+-assoc b a c)) (sym (+-suc b (a + c)))))))

    n≤₂ : next-slot A₁ ≤ suc (suc n)
    n≤₂ = ≤-trans n≤ (≤-trans (n≤1+n n) (n≤1+n (suc n)))

    nh₂ : halted s₂ ≡ false
    nh₂ = NC.hfin src

    module TCR = TwoCellRun (suc (suc n)) l prog base₂ s₂ A₁ cl rs n≤₂ nh₂ span₂
    module TCB = TwoCellBuild (suc (suc n)) l prog base₂ s₂ A₁ cl rs n≤₂ nh₂ span₂

    T : AbstractTrace
    T = copy-two-cell-trace E n l

    whole : exec-trace T s alloc ≡ (TCR.t₁₀ , TCR.A₁)
    whole =
      trans (exec-trace-append P (mov-to-input ∷ two-cell-trace (suc (suc n)) l) s alloc)
     (trans (cong (λ r → exec-trace (mov-to-input ∷ two-cell-trace (suc (suc n)) l) (proj₁ r) (proj₂ r)) (NC.whole src))
     (trans (exec-trace-cons mov-to-input _ s₁ A₁ (NC.hfin src)) TCR.whole))

    -- ── THE CHAIN
    fs0 fsF : FlatState
    fs0 = entry-flat base s alloc cl rs
    fsF = record fs0 { floc = TCR.t₁₀ ; falloc = TCR.A₁ ; fpc = length T + base }

    nhF : halted (floc fsF) ≡ false
    nhF = TCR.nh10

    he : halted (proj₁ (exec-trace T s alloc)) ≡ false
    he = trans (cong (λ r → halted (proj₁ r)) whole) TCR.nh10

    sts : All StraightStep T
    sts = ++⁺ (NodeCopyC.node-copy-straight {FS} E n) ((λ _ _ → refl) ∷ TCR.sts)

    evs : All (λ i → ∀ fs′ → event-of i fs′ ≡ []) T
    evs = ++⁺ (NodeCopyC.node-copy-silent {FS} E n) ((λ _ → refl) ∷ TCR.evs)

    run₀ = SR.straight-steps {prog} T fs0 sts span nh he

    eq : SR.after T fs0 ≡ fsF
    eq = cong (λ r → record fs0 { floc = proj₁ r ; falloc = proj₂ r ; fpc = length T + base }) whole

    run : FlatSteps prog (length T) fs0 fsF
    run = subst (FlatSteps prog (length T) fs0) eq run₀

    silent : chain-events run ≡ []
    silent = trans (chain-events-subst eq run₀) (SR.straight-silent {prog} T fs0 sts span nh he evs)

    -- ── THE FACTS, relative to the entry
    obj-loc : ValueLocation FS
    obj-loc = TCR.obj-loc

    cell0 : SMCore.MemOps.readLoc (floc fsF) obj-loc ≡ just (SV-Ptr NC.Nd)
    cell0 = trans TCB.cell0-fs10 (cong just (trans (writeReg-same (regs s₂) Output (readReg (regs s₂) Input1)) in1₂))

    heapref-≤ : next-heap-ref alloc ≤ next-heap-ref TCR.A₁
    heapref-≤ = ≤-trans (n≤1+n _) TCB.heapref-≤

    cf-F : current-frame TCR.A₁ ≡ current-frame alloc
    cf-F = refl

    sf-F : saved-frames TCR.A₁ ≡ saved-frames alloc
    sf-F = refl

    bf-advance : ∀ {lc : ValueLocation FS} → BeforeFrontier alloc lc → BeforeFrontier TCR.A₁ lc
    bf-advance {lc} bf = TCB.bf-advance (NC.bf-mono′ src (next-slot alloc) lc bf)

    blocks-kept : BlocksKept alloc TCR.A₁
    blocks-kept = bk-trans {a = alloc} {b = A₁} {c = TCR.A₁} (FlatAlloc.alloc-bk {FS} NC.N alloc) TCB.blocks-kept
                    (live-mono (NC.bf-mono′ src))

    mem-pres : ∀ (loc : ValueLocation FS)
             → BeforeFrontier (record alloc { next-slot = n }) loc
             → SMCore.MemOps.readLoc (floc fsF) loc ≡ SMCore.MemOps.readLoc s loc
    mem-pres loc bf =
      trans (TCB.mem-pres loc
               (frontier-monotone (record A₁ { next-slot = n }) (record A₁ { next-slot = suc (suc n) })
                  refl (≤-trans (n≤1+n n) (n≤1+n (suc n))) ≤-refl loc (NC.bf-mono′ src n loc bf)))
     (trans (readLoc-stack-heap-eq s₂ s₁ loc refl refl)
            (NC.keep-bf src loc bf))

    -- a value valid at the entry is valid at the end
    valid-transport : ∀ {mIn A} (y : ValueDomain.⟦ A ⟧ᴰᴵ) (loc : ValueLocation FS)
                    → BeforeFrontier alloc loc
                    → ValidAtWF {prog = prog} mIn alloc {A} y loc s
                    → ValidAtWF {prog = prog} mIn TCR.A₁ {A} y loc (floc fsF)
    valid-transport {A = A} y loc bf valid =
      validityWF-frontier-advance {A = A} y loc (floc fsF)
        cf-F (≤-reflexive refl) heapref-≤ blocks-kept
        (validityWF-mem-preserved {A = A} y loc s (floc fsF) bf
           (λ loc' bf' → mem-pres loc'
                           (frontier-monotone alloc (record alloc { next-slot = n })
                              refl n≤ ≤-refl loc' bf'))
           valid)

    -- ── THE COPY: valid at its own block, at the copy's end and at the end
    lay : CellAt {prog = prog} A₁ E x NC.Nd (NC.sp src) → DP.Σ AllocMode (λ m → ValidAtWF {prog = prog} m A₁ x NC.Nd (NC.sp src))
    lay (cell-ptr nd _ _ _)            = ⊥-elim (flat-not-node E kf nd)
    lay (cell-inline (rep-prim fit) _) = ⊥-elim (flat-not-fit E kf fit)
    lay (cell-flat {mC = m} _ _ v)     = m , v

    copy-mode : AllocMode
    copy-mode = proj₁ (lay (NC.cell-p src))

    copy-valid₂ : ValidAtWF {prog = prog} copy-mode A₁ x NC.Nd s₂
    copy-valid₂ = validityWF-mem-only x NC.Nd (NC.sp src) s₂ refl refl (proj₂ (lay (NC.cell-p src)))

    copy-live₂ : Live A₁ NC.Nd
    copy-live₂ = NC.live-Nd src

    copy-input₂ : InputAt {prog} {E} copy-mode A₁ x s₂
    copy-input₂ = in-loc NC.Nd copy-valid₂ copy-live₂ in1₂

    copy-live : Live TCR.A₁ NC.Nd
    copy-live = live-lift TCB.bf-advance copy-live₂

    copy-valid : ValidAtWF {prog = prog} copy-mode TCR.A₁ x NC.Nd (floc fsF)
    copy-valid = TCB.valid-transport x NC.Nd (live→bf copy-live₂) copy-valid₂
