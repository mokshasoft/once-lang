-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.OpStep — plan 0.146 B1.4b (D426): AN OP'S STEP. The
-- argument's address into `Input1`, the sigop, its answer (none, or the
-- Output word) stored in the argument's place. Relative to the machine's
-- world (`StepOp.Agree.OpVal`): the machine does not halt and answers the
-- image's answer.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; s≤s; z≤n)
import Data.Nat.Properties
open import Data.Nat.Properties using (+-comm; ≤-trans; m≤n+m; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; false; true; _∨_; not; _∧_; if_then_else_)
open import Data.Bool.Properties using (∨-identityʳ)
import Data.Bool
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Arith.CmpOp using (CmpOp)
open import Once.Arith.SigOp.Compare using (cmp-block-info; cmp-of)
open import Once.SigOp.Info using (SigOpSem; blockV; ffiV; callsV; emitsV; haltsV; primV)
open import Once.Arith.Prim using (p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-cmp)
open import Once.Type using (fits-int)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (module SigOpInfo; SigOpInfo; mk-info')
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)

module Once.LinCore.OpStep
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV)
open import Once.LinCore.Machine fmt ans bw using (Stk; _∷ˢ_; Slots; _∥_; _∣_)
open import Once.LinCore.Keys fmt ans bw using (Univ; nus; tys; cty)
open import Once.LinCore.Layout fmt ans bw
open import Once.LinCore.Words fmt ans bw
open import Once.LinCore.LowerSim fmt ans bw
open import Once.LinCore.Lower fmt ans bw using (module Lowering; flatB; cmpOf; opSig; inMem)
open import Once.LinCore.AnsWrite fmt ans bw using (module Keep)
open import Once.LinCore.ArgDecode fmt ans bw using (tsize-wsz)
open import Data.List.Membership.Propositional using (_∈_)
open import Once.LinCore.StepOp fmt ans bw using (module Agree; hdOr)

module OpSim {FS : FrameSemantics} (U : Univ)
             (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
             (ldConst : ∀ {b} → Lit b → AbstractInstr)
             (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Lowering U ncty ldConst using (answer; ansDst; argIn; lowOp; fbudget)
  open Rel {FS} U wordOf
  open Sim {FS} U wordOf
  open CfgW
  open Agree {FS} U wordOf using (OpVal; OpValM; OpValN; at-arg; argV; argD)
  open import Once.LinCore.Moves {FS} using (Seg; slot; lea-step; load-step; mov-in-step; store-step; store-same; store-other
                                           ; store-frame; InBlk; Old)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open LocState using (heapMem) renaming (halted to fhalted)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps; step-at) renaming ([] to done)
  open AbstractExec {FS} using (exec-sigop-output; exec-sigop-halts; sigop-gate; arg-words; tsize)
  open ExecFinal {FS} using (range-ok; live-frames)

  -- what an op's flat run leaves: as `Ran`, but the log grows by the sigop's events
  record OpRan (n lo hi : ℕ) (fs fs′ : FlatState) (evs : List SigOpEvent) : Set where
    field
      or-frame : AllocState.current-frame (falloc fs′) ≡ AllocState.current-frame (falloc fs)
      or-slots : AllocState.frame-slots (falloc fs′) ≡ AllocState.frame-slots (falloc fs)
      or-saved : AllocState.saved-frames (falloc fs′) ≡ AllocState.saved-frames (falloc fs)
      or-ret   : FlatMachine.fret fs′ ≡ FlatMachine.fret fs
      or-other : ∀ f x → ¬ f ≡ AllocState.current-frame (falloc fs) → LocState.stackMem (floc fs′) f x ≡ LocState.stackMem (floc fs) f x
      or-halt  : fhalted (floc fs′) ≡ fhalted (floc fs)
      or-inb   : InBlk fs → InBlk fs′
      or-log   : LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs) ++ evs
      or-pc    : fpc fs′ ≡ n + fpc fs
      or-next  : AllocState.next-heap-ref (falloc fs′) ≡ AllocState.next-heap-ref (falloc fs)
      or-old   : Old lo fs fs′
      or-top   : ∀ x → hi ≤ x → slot fs′ x ≡ slot fs x
  open OpRan public

  -- the register answer's store, by its word count (one word, or none)
  answerN : ℕ → ℕ → AbstractTrace
  answerN (suc zero) bot = store-at-slot (bot ∸ 1) ∷ []
  {-# CATCHALL #-}
  answerN _          bot = []

  private
    new-top : ∀ B a s → (B ∸ s) ∸ a ≡ B ∸ (a + s)
    new-top B a s = trans (Data.Nat.Properties.∸-+-assoc B s a) (cong (B ∸_) (+-comm s a))

    -- D435 (d): THE SIGOP'S WINDOW CHECK PASSES in the new image: the argument
    -- and the answer's buffer are words of the current frame, below its
    -- reservation (`fbudget φ`, `Here.h-slots`)
    tb : ∀ b → Data.Bool.T b → b ≡ true
    tb true _ = refl

    win-here : ∀ {X : Set} (D : Dec X) → X → ∀ b l → b ≡ true → win-pick D b l ≡ true
    win-here (yes _) x b l refl = refl
    win-here (no nx) x b l _    = ⊥-elim (nx x)

    frame-range : ∀ (al : AllocState {FS}) d n → d + n ≤ AllocState.frame-slots al
                → range-ok (live-frames al) n (SV-Ptr (AtStack (AllocState.current-frame al) d)) ≡ true
    frame-range al d zero    _  = refl
    frame-range al d (suc n) le =
      win-here (FrameSemantics._≟F_ FS (AllocState.current-frame al) (AllocState.current-frame al)) refl _ _
        (tb _ (Data.Nat.Properties.<⇒<ᵇ (subst (_≤ AllocState.frame-slots al)
                 (trans (Data.Nat.Properties.+-suc d n) (cong suc (+-comm d n))) le)))

    -- a compound argument is its address (`argV`); a scalar is no word the check reads
    arg-range : ∀ {A} (b : ST.Base ST.∅ₖ A) (fs : FlatState) d wx
              → d + tsize A ≤ AllocState.frame-slots (falloc fs)
              → range-ok (live-frames (falloc fs)) (arg-words b) (argV b fs d wx) ≡ true
    arg-range (ST.b-var {i = ()} _) fs d wx le
    arg-range ST.b-Unit    fs d wx le = refl
    arg-range ST.b-Void    fs d wx le = refl
    arg-range ST.b-Int     fs d wx le = refl
    arg-range ST.b-Float   fs d wx le = refl
    arg-range {A} (ST.b-* _ _) fs d wx le = frame-range (falloc fs) d (tsize A) le
    arg-range {A} (ST.b-+ _ _) fs d wx le = frame-range (falloc fs) d (tsize A) le

    -- a compare's argument is a pair of `Int`s, its block's two words
    cmp-pair : ∀ {A B} (c : SigOpSem A B) {o} → cmp-of c ≡ just o → A ≡ ST.Int ST.* ST.Int
    cmp-pair (primV (p-cmp _)) refl = refl
    cmp-pair (primV p-add)  ()
    cmp-pair (primV p-sub)  ()
    cmp-pair (primV p-mul)  ()
    cmp-pair (primV p-div)  ()
    cmp-pair (primV p-mod)  ()
    cmp-pair (primV p-neg)  ()
    cmp-pair (primV p-fadd) ()
    cmp-pair (primV p-fsub) ()
    cmp-pair (primV p-fmul) ()
    cmp-pair (primV p-fdiv) ()
    cmp-pair (primV p-i2f)  ()
    cmp-pair (blockV _ _ _) ()
    cmp-pair ffiV           ()
    cmp-pair callsV         ()
    cmp-pair (emitsV _)     ()
    cmp-pair (haltsV _)     ()

    cmp-range : ∀ {A} (b : ST.Base ST.∅ₖ A) (fs : FlatState) d wx → A ≡ ST.Int ST.* ST.Int
              → d + 2 ≤ AllocState.frame-slots (falloc fs)
              → range-ok (live-frames (falloc fs)) 2 (argV b fs d wx) ≡ true
    cmp-range (ST.b-var {i = ()} _) fs d wx e le
    cmp-range ST.b-Unit    fs d wx () le
    cmp-range ST.b-Void    fs d wx () le
    cmp-range ST.b-Int     fs d wx () le
    cmp-range ST.b-Float   fs d wx () le
    cmp-range (ST.b-* _ _) fs d wx e  le = frame-range (falloc fs) d 2 le
    cmp-range (ST.b-+ _ _) fs d wx () le

    -- an answer not in memory has no buffer to check
    inmem-false : ∀ {B} (b : ST.Base ST.∅ₖ B) → inMem b ≡ false → in-memory? B ≡ false
    inmem-false (ST.b-var {i = ()} _) e
    inmem-false ST.b-Unit    e = refl
    inmem-false ST.b-Void    e = refl
    inmem-false ST.b-Int     e = refl
    inmem-false ST.b-Float   e = refl
    inmem-false (ST.b-* _ _) ()
    inmem-false (ST.b-+ _ _) ()

    no-buffer : ∀ (B : ST.Type) fr v → in-memory? B ≡ false → range-ok fr (AbstractExec.ans-words {FS} B) v ≡ true
    no-buffer B fr v nm = cong (λ b → range-ok fr (if b then tsize B else 0) v) nm

    -- the argument's words lie below the operand stack's top, in the reservation
    arg-bnd : ∀ (φ : Frame) S wA fsl → wA + ws S ≤ budget φ → fbudget φ ≤ fsl
            → ((budget φ ∸ ws S) ∸ wA) + wA ≤ fsl
    arg-bnd φ S wA fsl fit fb =
      subst (_≤ fsl) (sym (Data.Nat.Properties.m∸n+n≡m (≤∸ wA (ws S) (budget φ) fit)))
        (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S))
           (≤-trans (Data.Nat.Properties.n≤1+n _) (≤-trans (Data.Nat.Properties.n≤1+n _) fb)))

    cmp-bnd : ∀ (φ : Frame) S wA fsl → fbudget φ ≤ fsl → ((budget φ ∸ ws S) ∸ wA) + 2 ≤ fsl
    cmp-bnd φ S wA fsl fb =
      ≤-trans (Data.Nat.Properties.+-monoˡ-≤ 2
                 (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ ∸ ws S) wA) (Data.Nat.Properties.m∸n≤m (budget φ) (ws S))))
              (subst (_≤ fsl) (+-comm 2 (budget φ)) fb)

    -- …so the step halts exactly as the SigOp does
    gated : ∀ {A B} (si : SigOpInfo A B) (al : AllocState {FS}) (st : LocState FS)
          → sigop-gate al si st ≡ true → exec-sigop-halts si st ≡ false
          → (exec-sigop-halts si st ∨ not (sigop-gate al si st)) ≡ false
    gated si al st gt hf = trans (cong (λ g → exec-sigop-halts si st ∨ not g) gt) (trans (∨-identityʳ _) hf)

  -- ★ D428: the argument's step, by its base: a scalar loaded, any other its address
  arg-step : ∀ {A} (b : ST.Base ST.∅ₖ A) prog (fs : FlatState) bot {x : MV ⌜ flatB b ⌝} {wx : List W}
           → VW (heapMem (floc fs)) x wx → SlotsAt (slot fs) (bot ∸ wsz ⌜ flatB b ⌝) wx
           → FlatMachine.flat-exec-instr {FS} (argIn b bot (wsz ⌜ flatB b ⌝)) prog fs
             ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (argV b fs (bot ∸ wsz ⌜ flatB b ⌝) wx) }
                         ; fpc = suc (fpc fs) }
  arg-step (ST.b-var {i = ()} _) prog fs bot px sx
  arg-step ST.b-Unit    prog fs bot px sx = refl
  arg-step ST.b-Void    prog fs bot px sx = refl
  arg-step ST.b-Int     prog fs bot px sx = one (vw-len px) sx
    where
      one : ∀ {wx : List W} → length wx ≡ 1 → SlotsAt (slot fs) (bot ∸ 1) wx
          → FlatMachine.flat-exec-instr {FS} (load-from-slot (bot ∸ 1)) prog fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (hdOr wx (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) (bot ∸ 1)))) }
                        ; fpc = suc (fpc fs) }
      one {w ∷ []} refl (e , _) = load-step fs (bot ∸ 1) e
  arg-step ST.b-Float   prog fs bot px sx = one (vw-len px) sx
    where
      one : ∀ {wx : List W} → length wx ≡ 1 → SlotsAt (slot fs) (bot ∸ 1) wx
          → FlatMachine.flat-exec-instr {FS} (load-from-slot (bot ∸ 1)) prog fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output (hdOr wx (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) (bot ∸ 1)))) }
                        ; fpc = suc (fpc fs) }
      one {w ∷ []} refl (e , _) = load-step fs (bot ∸ 1) e
  arg-step (ST.b-* _ _) prog fs bot px sx = refl
  arg-step (ST.b-+ _ _) prog fs bot px sx = refl

  lop-sim₀ : ∀ prog (fs : FlatState) (φ : Frame) (s : Sig) {Es S} {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝} {E}
          → in-memory? (Sig.sB s) ≡ false
          → OpValN false s x y E fs
          → Seg prog (fpc fs) (argIn (SigOpInfo.baseA (info s)) (budget φ ∸ ws S) (wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info s)
                               ∷ answerN (wsz ⌜ scod s ⌝) (budget φ ∸ ws S))
          → fhalted (floc fs) ≡ false
          → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
          → ws (⌜ scod s ⌝ ∷ S) ≤ OP φ
          → fbudget φ ≤ AllocState.frame-slots (falloc fs)
          → Σ FlatState λ fs′ → FlatSteps prog (3 + length (answerN (wsz ⌜ scod s ⌝) (budget φ ∸ ws S))) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
              × OpRan (3 + length (answerN (wsz ⌜ scod s ⌝) (budget φ ∸ ws S))) (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
  lop-sim₀ prog fs φ s {Es} {S} {es} {os} {x} {y} {E} nm ag seg h C fit fb = with-arg (c-stk C)
    where
      cf = AllocState.current-frame (falloc fs)
      bot = budget φ ∸ ws S
      d₀ = bot ∸ wsz ⌜ sdom s ⌝
      with-arg : StkW (heapMem (floc fs)) (slot fs) φ (x ∷ˢ os) → _
      with-arg ((wx , px , sx) , st) = go (wsz ⌜ scod s ⌝) refl seg (ag d₀ wx px sx₀)
        where
          sx₀ = subst (λ z → SlotsAt (slot fs) z wx) (sym (new-top (budget φ) (wsz ⌜ sdom s ⌝) (ws S))) sx
          v₀ = argV (SigOpInfo.baseA (info s)) fs d₀ wx
          fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output v₀ } ; fpc = suc (fpc fs) }
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 v₀ } ; fpc = suc (fpc fs₁) }
          -- the sigop's step at a memory `m` (its own store, which is none: `nm`)
          G : LocState FS → FlatState
          G m = record fs₂ { floc = record (floc fs₂)
                               { regs     = writeReg (LocState.regs (floc fs₂)) Output (exec-sigop-output (info s) (floc fs₂))
                               ; stackMem = LocState.stackMem m ; heapMem = LocState.heapMem m
                               ; halted   = exec-sigop-halts (info s) (floc fs₂) ∨ not (sigop-gate (falloc fs₂) (info s) (floc fs₂))
                               ; faulted  = AbstractExec.exec-sigop-faults {FS} (info s) (floc fs₂) ∨ (not (sigop-gate (falloc fs₂) (info s) (floc fs₂)) ∨ LocState.faulted (floc fs₂))
                               ; ev-log   = LocState.ev-log (floc fs₂) ++ AbstractExec.sigop-events {FS} (info s) (floc fs₂) }
                           ; fpc = suc (fpc fs₂) }
          fs₃ = G (floc fs₂)
          eq₃ : FlatMachine.flat-exec-instr {FS} (instr-sigop (info s)) prog fs₂ ≡ fs₃
          eq₃ = cong G (AbstractExec.sigop-store-id {FS} (info s) (floc fs₂) nm)
          out = exec-sigop-output (info s) (at-arg fs v₀)
          a-step = arg-step (SigOpInfo.baseA (info s)) prog fs bot px sx₀
          gt : sigop-gate (falloc fs) (info s) (at-arg fs v₀) ≡ true
          gt = cong₂ _∧_
                 (arg-range (SigOpInfo.baseA (info s)) fs d₀ wx
                    (subst (λ t → d₀ + t ≤ AllocState.frame-slots (falloc fs)) (sym (tsize-wsz {FS} (SigOpInfo.baseA (info s))))
                       (arg-bnd φ S (wsz ⌜ sdom s ⌝) _ (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))) fb)))
                 (no-buffer _ _ v₀ nm)
          hgate = gated (info s) (falloc fs) (at-arg fs v₀) gt
          ran₃ : exec-sigop-halts (info s) (at-arg fs v₀) ≡ false → AbstractExec.sigop-events {FS} (info s) (at-arg fs v₀) ≡ E
               → OpRan 3 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs₃ E
          ran₃ hf ee = record { or-frame = refl ; or-slots = refl ; or-saved = refl ; or-ret = refl ; or-other = λ _ _ _ → refl
                           ; or-halt = trans (hgate hf) (sym h) ; or-inb = λ I → I ; or-log = cong (LocState.ev-log (floc fs) ++_) ee ; or-pc = refl ; or-next = refl
                           ; or-old = λ _ _ → refl ; or-top = λ _ _ → refl }
          go : ∀ n → wsz ⌜ scod s ⌝ ≡ n
             → Seg prog (fpc fs) (argIn (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info s) ∷ answerN n bot)
             → (exec-sigop-halts (info s) (at-arg fs v₀) ≡ false)
               × (AbstractExec.sigop-events {FS} (info s) (at-arg fs v₀) ≡ E)
               × Σ (List W) (λ wy → VW (heapMem (floc fs)) y wy × ((wy ≡ []) Data.Sum.⊎ (wy ≡ out ∷ [])))
             → Σ FlatState λ fs′ → FlatSteps prog (3 + length (answerN n bot)) fs fs′
                 × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
                 × OpRan (3 + length (answerN n bot)) (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
          go zero eC (g₁ , g₂ , g₃ , _) (hf , ee , .[] , pw , inj₁ refl) =
            fs₃ ,
            step-at fs₁ (h , g₁) a-step (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) eq₃ done)) ,
            record { c-env = c-env C ; c-stk = (([] , pw , tt) , st) ; c-efit = c-efit C ; c-sfit = fit } ,
            ran₃ hf ee
          go zero eC _ (hf , ee , .(out ∷ []) , pw , inj₂ refl) = ⊥-elim (Data.Nat.Properties.1+n≢0 (trans (vw-len pw) eC))
          go (suc zero) eC _ (hf , ee , .[] , pw , inj₁ refl) = ⊥-elim (Data.Nat.Properties.0≢1+n (trans (vw-len pw) eC))
          go (suc zero) eC (g₁ , g₂ , g₃ , g₄ , _) (hf , ee , .(out ∷ []) , pw , inj₂ refl) =
            fs₄ ,
            step-at fs₁ (h , g₁) a-step (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) eq₃
              (step-at fs₄ (h₃ , g₄) (store-step fs₃ dst) done))) ,
            record { c-env  = envW-frame es (λ z z< → store-other (floc fs₃) cf dst out z
                                             (λ e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans z< env≤))) (c-env C)
                   ; c-stk  = ( out ∷ [] , pw
                              , (trans (cong (slot fs₄) pos) (store-same (floc fs₃) cf dst out) , tt) )
                            , stkW-frame os fitS (λ z lo _ → store-other (floc fs₃) cf dst out z
                                                   (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans b1<b lo))) st
                   ; c-efit = c-efit C ; c-sfit = fit } ,
            record { or-frame = refl ; or-slots = refl ; or-saved = refl ; or-ret = refl
                   ; or-other = λ f z ne → store-frame (floc fs₃) cf dst out f z (λ e → ne (sym e))
                   ; or-halt = trans (hgate hf) (sym h) ; or-inb = λ I → I ; or-log = cong (LocState.ev-log (floc fs) ++_) ee ; or-pc = refl ; or-next = refl
                   ; or-old = λ _ _ → refl
                   ; or-top = λ z le → store-other (floc fs₃) cf dst out z
                                         (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans b1<b (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) le))) }
            where
              dst = bot ∸ 1
              h₃ : fhalted (floc fs₃) ≡ false
              h₃ = hgate hf
              fs₄ = record fs₃ { floc = MemOps.writeLoc {FS} (floc fs₃) (AtStack cf dst) out ; fpc = suc (fpc fs₃) }
              fit1 : 1 + ws S ≤ OP φ
              fit1 = subst (λ z → z + ws S ≤ OP φ) eC fit
              fitB : 1 + ws S ≤ budget φ
              fitB = ≤-trans fit1 (m≤n+m (OP φ) (EP φ))
              fitS : ws S ≤ budget φ
              fitS = ≤-trans (m≤n+m (ws S) 1) fitB
              env≤ : ws Es ≤ dst
              env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (1 + ws S) fit1))
              b1<b : dst < bot
              b1<b = Data.Nat.Properties.∸-monoʳ-< {o = 0} (s≤s z≤n) (≤∸ 1 (ws S) (budget φ) fitB)
              pos : budget φ ∸ ws (⌜ scod s ⌝ ∷ S) ≡ dst
              pos = trans (cong (λ z → budget φ ∸ (z + ws S)) eC) (sym (new-top (budget φ) 1 (ws S)))
          go (suc (suc n)) eC _ (hf , ee , .[] , pw , inj₁ refl) = ⊥-elim (Data.Nat.Properties.0≢1+n (trans (vw-len pw) eC))
          go (suc (suc n)) eC _ (hf , ee , .(out ∷ []) , pw , inj₂ refl) =
            ⊥-elim (Data.Nat.Properties.0≢1+n (Data.Nat.Properties.suc-injective (trans (vw-len pw) eC)))

  -- ★ D428: a compare: its block's sigop (an `Int`), its truth as a tag (`out-nz`), stored
  lop-cmp : ∀ prog (fs : FlatState) (φ : Frame) (s : Sig) {Es S} {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝} {E}
            (o : CmpOp) → cmpOf s ≡ just o
          → OpValM s (just o) x y E fs
          → Seg prog (fpc fs) (lowOp s (just o) (budget φ ∸ ws S))
          → fhalted (floc fs) ≡ false
          → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
          → ws (⌜ scod s ⌝ ∷ S) ≤ OP φ
          → fbudget φ ≤ AllocState.frame-slots (falloc fs)
          → Σ FlatState λ fs′ → FlatSteps prog 5 fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
              × OpRan 5 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
  lop-cmp prog fs φ s {Es} {S} {es} {os} {x} {y} {E} o eo ag (g₁ , g₂ , g₃ , g₄ , g₅ , _) h C fit fb = with-arg (c-stk C)
    where
      cf = AllocState.current-frame (falloc fs)
      bot = budget φ ∸ ws S
      d₀ = bot ∸ wsz ⌜ sdom s ⌝
      with-arg : StkW (heapMem (floc fs)) (slot fs) φ (x ∷ˢ os) → _
      with-arg ((wx , px , sx) , st) = fin (ag d₀ wx px sx₀)
        where
          sx₀ = subst (λ z → SlotsAt (slot fs) z wx) (sym (new-top (budget φ) (wsz ⌜ sdom s ⌝) (ws S))) sx
          v₀ = argV (SigOpInfo.baseA (info s)) fs d₀ wx
          fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output v₀ } ; fpc = suc (fpc fs) }
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 v₀ } ; fpc = suc (fpc fs₁) }
          fs₃ = FlatMachine.flat-exec-instr {FS} (instr-sigop (cmp-block-info o)) prog fs₂
          a-step = arg-step (SigOpInfo.baseA (info s)) prog fs bot px sx₀
          gt : sigop-gate (falloc fs) (cmp-block-info o) (at-arg fs v₀) ≡ true
          gt = cong₂ _∧_
                 (cmp-range (SigOpInfo.baseA (info s)) fs d₀ wx (cmp-pair (SigOpInfo.sem (info s)) eo)
                    (cmp-bnd φ S (wsz ⌜ sdom s ⌝) _ fb))
                 refl
          fin : (exec-sigop-halts (cmp-block-info o) (at-arg fs v₀) ≡ false)
                × (AbstractExec.sigop-events {FS} (cmp-block-info o) (at-arg fs v₀) ≡ E)
                × Σ _ (λ k → (exec-sigop-output (cmp-block-info o) (at-arg fs v₀) ≡ SV-Lit fits-int k)
                              × VW (heapMem (floc fs)) y (sv-nz (SV-Lit {FS} fits-int k) ∷ []))
              → Σ FlatState λ fs′ → FlatSteps prog 5 fs fs′
                  × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
                  × OpRan 5 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
          fin (hf₀ , ee , k , ek , pw) =
            fs₅ ,
            step-at fs₁ (h , g₁) a-step (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) refl
              (step-at fs₄ (hf , g₄) nz-step (step-at fs₅ (hf , g₅) (store-step fs₄ dst) done)))) ,
            record { c-env  = envW-frame es (λ z z< → store-other (floc fs₄) cf dst tw z
                                             (λ e → Data.Nat.Properties.<-irrefl (sym e) (<-≤-trans z< env≤))) (c-env C)
                   ; c-stk  = ( tw ∷ [] , pw
                              , (trans (cong (slot fs₅) pos) (store-same (floc fs₄) cf dst tw) , tt) )
                            , stkW-frame os fitS (λ z lo _ → store-other (floc fs₄) cf dst tw z
                                                   (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans b1<b lo))) st
                   ; c-efit = c-efit C ; c-sfit = fit } ,
            record { or-frame = refl ; or-slots = refl ; or-saved = refl ; or-ret = refl
                   ; or-other = λ f z ne → store-frame (floc fs₄) cf dst tw f z (λ e → ne (sym e))
                   ; or-halt = trans hf (sym h) ; or-inb = λ I → I ; or-log = cong (LocState.ev-log (floc fs) ++_) ee ; or-pc = refl ; or-next = refl
                   ; or-old = λ _ _ → refl
                   ; or-top = λ z le → store-other (floc fs₄) cf dst tw z
                                         (λ e → Data.Nat.Properties.<-irrefl e (<-≤-trans b1<b (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) le))) }
            where
              hf = gated (cmp-block-info o) (falloc fs) (at-arg fs v₀) gt hf₀
              dst = bot ∸ 1
              tw = sv-nz (SV-Lit {FS} fits-int k)
              fs₄ = record fs₃ { floc = record (floc fs₃) { regs = writeReg (LocState.regs (floc fs₃)) Output tw } ; fpc = suc (fpc fs₃) }
              nz-step : FlatMachine.flat-exec-instr {FS} (instr-reg-op out-nz) prog fs₃ ≡ fs₄
              nz-step = trans (cong (λ v → FlatMachine.do-nz {FS} v fs₃) ek)
                              (cong (λ v → record fs₃ { floc = record (floc fs₃) { regs = writeReg (LocState.regs (floc fs₃)) Output (sv-nz v) } ; fpc = suc (fpc fs₃) }) ek)
              fs₅ = record fs₄ { floc = MemOps.writeLoc {FS} (floc fs₄) (AtStack cf dst) tw ; fpc = suc (fpc fs₄) }
              eC : wsz ⌜ scod s ⌝ ≡ 1
              eC = sym (vw-len pw)
              fit1 : 1 + ws S ≤ OP φ
              fit1 = subst (λ z → z + ws S ≤ OP φ) eC fit
              fitB : 1 + ws S ≤ budget φ
              fitB = ≤-trans fit1 (m≤n+m (OP φ) (EP φ))
              fitS : ws S ≤ budget φ
              fitS = ≤-trans (m≤n+m (ws S) 1) fitB
              env≤ : ws Es ≤ dst
              env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) 1 (ws S))) (env-below φ (1 + ws S) fit1))
              b1<b : dst < bot
              b1<b = Data.Nat.Properties.∸-monoʳ-< {o = 0} (s≤s z≤n) (≤∸ 1 (ws S) (budget φ) fitB)
              pos : budget φ ∸ ws (⌜ scod s ⌝ ∷ S) ≡ dst
              pos = trans (cong (λ z → budget φ ∸ (z + ws S)) eC) (sym (new-top (budget φ) 1 (ws S)))

  -- ★ D432: an op whose answer is in memory (a product, a sum): the argument, the answer's
  -- address into `Output` (the result's slots), the sigop, which writes the answer there
  open Keep {FS} using (st-heap; st-frame; st-out)
  open import Once.LinCore.Moves {FS} using (inb-same)
  lop-mem : ∀ prog (fs : FlatState) (φ : Frame) {A B} (si : SigOpInfo A B) {Es S} {es : Slots Es} {os : Stk S}
              {x : MV ⌜ sdom (sig si) ⌝} {y : MV ⌜ scod (sig si) ⌝} {E}
          → (im : in-memory? B ≡ true)
          → OpValN true (sig si) x y E fs
          → Seg prog (fpc fs) (argIn (SigOpInfo.baseA si) (budget φ ∸ ws S) (wsz ⌜ sdom (sig si) ⌝) ∷ mov-to-input
                               ∷ lea-slot ((budget φ ∸ ws S) ∸ wsz ⌜ scod (sig si) ⌝) ∷ instr-sigop si ∷ [])
          → fhalted (floc fs) ≡ false
          → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
          → ws (⌜ scod (sig si) ⌝ ∷ S) ≤ OP φ
          → fbudget φ ≤ AllocState.frame-slots (falloc fs)
          → Σ FlatState λ fs′ → FlatSteps prog 4 fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
              × OpRan 4 (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
  lop-mem prog fs φ {A} {B} si {Es} {S} {es} {os} {x} {y} {E} im ag (g₁ , g₂ , g₃ , g₄ , _) h C fit fb = with-arg (c-stk C)
    where
      s = sig si
      cf = AllocState.current-frame (falloc fs)
      bot = budget φ ∸ ws S
      wB = wsz ⌜ scod s ⌝
      d₀ = bot ∸ wsz ⌜ sdom s ⌝
      dst = bot ∸ wB
      tB : AbstractExec.tsize {FS} B ≡ wB
      tB = tsize-wsz {FS} (SigOpInfo.conB si)
      fitB : wB + ws S ≤ budget φ
      fitB = ≤-trans fit (m≤n+m (OP φ) (EP φ))
      wB≤ : wB ≤ bot
      wB≤ = ≤∸ wB (ws S) (budget φ) fitB
      dst+ : dst + AbstractExec.tsize {FS} B ≡ bot
      dst+ = trans (cong (dst +_) tB) (Data.Nat.Properties.m∸n+n≡m wB≤)
      env≤ : ws Es ≤ dst
      env≤ = ≤-trans (c-efit C) (subst (EP φ ≤_) (sym (new-top (budget φ) wB (ws S))) (env-below φ (wB + ws S) fit))
      fitS : ws S ≤ budget φ
      fitS = ≤-trans (m≤n+m (ws S) wB) fitB
      pos : budget φ ∸ ws (⌜ scod s ⌝ ∷ S) ≡ dst
      pos = sym (new-top (budget φ) wB (ws S))
      with-arg : StkW (heapMem (floc fs)) (slot fs) φ (x ∷ˢ os) → _
      with-arg ((wx , px , sx) , st) = fin (ag d₀ dst wx px sx₀)
        where
          sx₀ = subst (λ z → SlotsAt (slot fs) z wx) (sym (new-top (budget φ) (wsz ⌜ sdom s ⌝) (ws S))) sx
          v₀ = argV (SigOpInfo.baseA si) fs d₀ wx
          fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output v₀ } ; fpc = suc (fpc fs) }
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 v₀ } ; fpc = suc (fpc fs₁) }
          fs₂′ = record fs₂ { floc = record (floc fs₂) { regs = writeReg (LocState.regs (floc fs₂)) Output (SV-Ptr (AtStack cf dst)) }
                            ; fpc = suc (fpc fs₂) }
          fs₃ = FlatMachine.flat-exec-instr {FS} (instr-sigop si) prog fs₂′
          st₀ = argD s fs d₀ dst wx
          ma = AbstractExec.sigop-answer {FS} si st₀
          a-step = arg-step (SigOpInfo.baseA si) prog fs bot px sx₀
          gt : sigop-gate (falloc fs) si st₀ ≡ true
          gt = cong₂ _∧_
                 (arg-range (SigOpInfo.baseA si) fs d₀ wx
                    (subst (λ t → d₀ + t ≤ AllocState.frame-slots (falloc fs)) (sym (tsize-wsz {FS} (SigOpInfo.baseA si)))
                       (arg-bnd φ S (wsz ⌜ sdom s ⌝) _ (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))) fb)))
                 (trans (cong (λ b → range-ok (live-frames (falloc fs)) (if b then tsize B else 0) (SV-Ptr (AtStack cf dst))) im)
                        (frame-range (falloc fs) dst (tsize B)
                           (subst (_≤ AllocState.frame-slots (falloc fs)) (sym dst+)
                              (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S))
                                 (≤-trans (Data.Nat.Properties.n≤1+n _) (≤-trans (Data.Nat.Properties.n≤1+n _) fb))))))
          eqh : heapMem (floc fs₃) ≡ heapMem (floc fs)
          eqh = st-heap (SigOpInfo.conB si) (in-memory? B) im ma cf dst st₀
          -- the frame outside the answer's words is as it was
          keep : ∀ z → (z < dst ⊎ dst + AbstractExec.tsize {FS} B ≤ z) → slot fs₃ z ≡ slot fs z
          keep z o = st-out (SigOpInfo.conB si) (in-memory? B) im ma cf dst st₀ z o
          fin : _ → _
          fin (hf , ee , wy , pw , sy) =
            fs₃ ,
            step-at fs₁ (h , g₁) a-step (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₂′ (h , g₃) (lea-step fs₂ dst)
              (step-at fs₃ (h , g₄) refl done))) ,
            subst (λ hp → CfgW hp (slot fs₃) φ (es ∥ y ∷ˢ os)) (sym eqh)
              (record { c-env  = envW-frame es (λ z z< → keep z (inj₁ (<-≤-trans z< env≤))) (c-env C)
                      ; c-stk  = ( wy , pw , subst (λ z → SlotsAt (slot fs₃) z wy) (sym pos) sy )
                               , stkW-frame os fitS (λ z lo _ → keep z (inj₂ (subst (_≤ z) (sym dst+) lo))) st
                      ; c-efit = c-efit C ; c-sfit = fit }) ,
            record { or-frame = refl ; or-slots = refl ; or-saved = refl ; or-ret = refl
                   ; or-other = λ f z ne → st-frame (SigOpInfo.conB si) (in-memory? B) im ma cf dst st₀ f z (λ e → ne (sym e))
                   ; or-halt = trans (gated si (falloc fs) st₀ gt hf) (sym h) ; or-inb = inb-same {fs} {fs₃} eqh refl
                   ; or-log = cong (LocState.ev-log (floc fs) ++_) ee ; or-pc = refl ; or-next = refl
                   ; or-old = λ hl _ → cong (λ m → m hl) eqh
                   ; or-top = λ z le → keep z (inj₂ (subst (_≤ z) (sym dst+)
                                         (≤-trans (Data.Nat.Properties.m∸n≤m (budget φ) (ws S)) le))) }

  -- ★ an op, by the sigop its code runs (D428)
  lop-sim : ∀ prog (fs : FlatState) (φ : Frame) (s : Sig) {Es S} {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝} {E}
            (m : Maybe CmpOp) → cmpOf s ≡ m
          → OpValM s m x y E fs
          → Seg prog (fpc fs) (lowOp s m (budget φ ∸ ws S))
          → fhalted (floc fs) ≡ false
          → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
          → ws (⌜ scod s ⌝ ∷ S) ≤ OP φ
          → fbudget φ ≤ AllocState.frame-slots (falloc fs)
          → Σ FlatState λ fs′ → FlatSteps prog (length (lowOp s m (budget φ ∸ ws S))) fs fs′
              × CfgW (heapMem (floc fs′)) (slot fs′) φ (es ∥ y ∷ˢ os)
              × OpRan (length (lowOp s m (budget φ ∸ ws S))) (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
  lop-sim prog fs φ s (just o) eo ag seg h C fit fb = lop-cmp prog fs φ s o eo ag seg h C fit fb
  lop-sim prog fs φ (sig (mk-info' n c bA (ST.b-var {i = ()} _))) nothing _ ag seg h C fit fb
  lop-sim prog fs φ s@(sig (mk-info' n c bA ST.b-Unit))  nothing _ ag seg h C fit fb = lop-sim₀ prog fs φ s refl ag seg h C fit fb
  lop-sim prog fs φ s@(sig (mk-info' n c bA ST.b-Void))  nothing _ ag seg h C fit fb = lop-sim₀ prog fs φ s refl ag seg h C fit fb
  lop-sim prog fs φ s@(sig (mk-info' n c bA ST.b-Int))   nothing _ ag seg h C fit fb = lop-sim₀ prog fs φ s refl ag seg h C fit fb
  lop-sim prog fs φ s@(sig (mk-info' n c bA ST.b-Float)) nothing _ ag seg h C fit fb = lop-sim₀ prog fs φ s refl ag seg h C fit fb
  lop-sim prog fs φ (sig si@(mk-info' n c bA (ST.b-* _ _))) nothing _ ag seg h C fit fb = lop-mem prog fs φ si refl ag seg h C fit fb
  lop-sim prog fs φ (sig si@(mk-info' n c bA (ST.b-+ _ _))) nothing _ ag seg h C fit fb = lop-mem prog fs φ si refl ag seg h C fit fb

  -- ★ a halting op: the argument's address, the sigop, the machine halted
  lop-halt : ∀ prog (fs : FlatState) (φ : Frame) (s : Sig) {Es S} {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {E}
           → Agree.OpHalt {FS} U wordOf s x E fs
           → Seg prog (fpc fs) (argIn (SigOpInfo.baseA (info s)) (budget φ ∸ ws S) (wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info (opSig s (cmpOf s))) ∷ [])
           → fhalted (floc fs) ≡ false
           → CfgW (heapMem (floc fs)) (slot fs) φ (es ∥ x ∷ˢ os)
           → fbudget φ ≤ AllocState.frame-slots (falloc fs)
           → Σ FlatState λ fs′ → FlatSteps prog 3 fs fs′ × fhalted (floc fs′) ≡ true
               × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs) ++ E × ending (floc fs′) ≡ ending (floc fs)
  lop-halt prog fs φ s {Es} {S} {es} {os} {x} {E} (nb , ag) (g₁ , g₂ , g₃ , _) h C fb = with-arg (c-stk C)
    where
      cf = AllocState.current-frame (falloc fs)
      d₀ = (budget φ ∸ ws S) ∸ wsz ⌜ sdom s ⌝
      with-arg : StkW (heapMem (floc fs)) (slot fs) φ (x ∷ˢ os) → _
      with-arg ((wx , px , sx) , _) =
        fs₃ ,
        step-at fs₁ (h , g₁) (arg-step (SigOpInfo.baseA (info s)) prog fs (budget φ ∸ ws S) px sx₀)
          (step-at fs₂ (h , g₂) (mov-in-step fs₁) (step-at fs₃ (h , g₃) refl done)) ,
        fin (ag d₀ wx px sx₀)
        where
          sx₀ = subst (λ z → SlotsAt (slot fs) z wx) (sym (new-top (budget φ) (wsz ⌜ sdom s ⌝) (ws S))) sx
          v₀ = argV (SigOpInfo.baseA (info s)) fs d₀ wx
          fs₁ = record fs { floc = record (floc fs) { regs = writeReg (LocState.regs (floc fs)) Output v₀ } ; fpc = suc (fpc fs) }
          fs₂ = record fs₁ { floc = record (floc fs₁) { regs = writeReg (LocState.regs (floc fs₁)) Input1 v₀ } ; fpc = suc (fpc fs₁) }
          fs₃ = FlatMachine.flat-exec-instr {FS} (instr-sigop (info (opSig s (cmpOf s)))) prog fs₂
          st = at-arg fs v₀
          -- the window check, by whether the op is a compare
          gate-m : ∀ m → cmpOf s ≡ m → sigop-gate (falloc fs) (info (opSig s m)) st ≡ true
          gate-m nothing e = cong₂ _∧_
            (arg-range (SigOpInfo.baseA (info s)) fs d₀ wx
               (subst (λ t → d₀ + t ≤ AllocState.frame-slots (falloc fs)) (sym (tsize-wsz {FS} (SigOpInfo.baseA (info s))))
                  (arg-bnd φ S (wsz ⌜ sdom s ⌝) _ (≤-trans (c-sfit C) (m≤n+m (OP φ) (EP φ))) fb)))
            (no-buffer _ _ v₀ (inmem-false (SigOpInfo.conB (info s)) nb))
          gate-m (just o) e = cong₂ _∧_
            (cmp-range (SigOpInfo.baseA (info s)) fs d₀ wx (cmp-pair (SigOpInfo.sem (info s)) e) (cmp-bnd φ S (wsz ⌜ sdom s ⌝) _ fb))
            refl
          gt : sigop-gate (falloc fs) (info (opSig s (cmpOf s))) st ≡ true
          gt = gate-m (cmpOf s) refl
          fin : _ → _
          fin (ht , ee , nf) =
            cong (λ b → b ∨ not (sigop-gate (falloc fs) (info (opSig s (cmpOf s))) st)) ht ,
            cong (LocState.ev-log (floc fs) ++_) ee ,
            cong (λ b → LocState.left (floc fs) , b)
              (trans (cong (λ b → b ∨ (not (sigop-gate (falloc fs) (info (opSig s (cmpOf s))) st) ∨ LocState.faulted (floc fs))) nf)
                     (cong (λ g → not g ∨ LocState.faulted (floc fs)) gt))

------------------------------------------------------------------------
-- ★ AT A ROOT'S PATH.
------------------------------------------------------------------------

open import Once.LinCore.Image fmt ans bw using (Codeᴵ; _⨾_; prim)
open import Once.LinCore.ImagePt fmt ans bw using (Sub; next)
open import Once.LinCore.LowAt fmt ans bw using (Inside; module At)
open import Once.LinCore.StepLocal fmt ans bw using (module Loc)
open import Once.LinCore.Events fmt ans bw using (Run; r-op; r-tmp; Outcome; gives)

-- an op's run keeps the counter
op-n : ∀ {Γ} {ds : Defs Γ} {E} {s : Sig} {e : MV E} {x : MV ⌜ sdom s ⌝} {y n n′ t} → Run ds (lop s) e x n (gives y n′) t → n′ ≡ n
op-n (r-op _) = refl
op-n (r-tmp r _ _) = op-n r

module OpR {FS : FrameSemantics} (U : Univ)
           (ncty : ∀ {F S} → (F , S) ∈ nus U → cty (F , S) ∈ tys U)
           (ldConst : ∀ {b} → Lit b → AbstractInstr)
           (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS)
           (prog : AbstractTrace)
           {sh₀ U₀} (root : Codeᴵ sh₀ U₀) (j : ℕ)
           (L₀ : At.Low U ncty ldConst (frameOf root) j root)
           (R : Inside prog (At.code U ncty ldConst (frameOf root) j L₀)) where
  open Loc {FS} U ncty ldConst wordOf prog root j L₀ R
  open OpSim {FS} U ncty ldConst wordOf
  open Agree {FS} U wordOf using (OpVal; OpHalt)
  open import Once.CCC.Machine.Flat using (module FlatMachine)
  open FlatMachine {FS} using (FlatState; floc; falloc; fpc)
  open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
  open FlatStepsAPI {FS} using (FlatSteps)
  open import Once.LinCore.Moves {FS} using (Seg; Seg-++ˡ)
  open Lowering U ncty ldConst using (answer; ansDst; argIn; lowOp)

  st-op : ∀ {Γ} {ds : Defs Γ} {Es S V} {s : Sig} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) V} (sb : Sub root (prim ds (lop s) ⨾ k))
            {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {y : MV ⌜ scod s ⌝} {E fs}
        → Here sb (es ∥ x ∷ˢ os) fs → OpVal s x y E fs
        → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × Here (next sb) (es ∥ y ∷ˢ os) fs′
            × OpRan N (AllocState.next-heap-ref (falloc fs)) (budget φ) fs fs′ E
  st-op {S = S} {s = s} sb {fs = fs} H ag = fin (lop-sim prog fs φ s (cmpOf s) refl ag (Seg-++ˡ prog (fpc fs) (insC sb) _ (seg-at sb H)) (Here.h-run H) (Here.h-cfg H)
                                                  (proj₂ (shape-fits (next sb))) (Data.Nat.Properties.≤-reflexive (sym (Here.h-slots H))))
    where
      fin : _ → _
      fin (fs′ , st , C′ , OR) =
        _ , fs′ , st ,
        record { h-pc = trans (or-pc OR) (trans (cong (length (insC sb) +_) (Here.h-pc H))
                          (trans (Data.Nat.Properties.+-comm (length (insC sb)) (pos sb)) (sym (pos-next sb))))
               ; h-run = trans (or-halt OR) (Here.h-run H) ; h-cfg = C′ ; h-slots = trans (or-slots OR) (Here.h-slots H) } ,
        OR

  st-opend : ∀ {Γ} {ds : Defs Γ} {Es S V} {s : Sig} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) V} (sb : Sub root (prim ds (lop s) ⨾ k))
               {es : Slots Es} {os : Stk S} {x : MV ⌜ sdom s ⌝} {E fs}
           → Here sb (es ∥ x ∷ˢ os) fs → OpHalt s x E fs
           → Σ ℕ λ N → Σ FlatState λ fs′ → FlatSteps prog N fs fs′ × LocState.halted (floc fs′) ≡ true
               × LocState.ev-log (floc fs′) ≡ LocState.ev-log (floc fs) ++ E × ending (floc fs′) ≡ ending (floc fs)
               × LocState.halted (floc fs) ≡ Data.Bool.false
  st-opend {S = S} {s = s} sb {fs = fs} H ag =
    case-out (lop-halt prog fs φ s ag (halt-seg s (cmpOf s) (proj₁ ag) (Seg-++ˡ prog (fpc fs) (insC sb) _ (seg-at sb H))) (Here.h-run H) (Here.h-cfg H)
                       (Data.Nat.Properties.≤-reflexive (sym (Here.h-slots H))))
    where
      bot = budget φ ∸ ws S
      -- D432: a halting op's answer is not in memory, so its code has no destination
      dst-none : ∀ {B} (b : ST.Base ST.∅ₖ B) w → inMem b ≡ false → ansDst b bot w ≡ []
      dst-none (ST.b-var {i = ()} _) w e
      dst-none ST.b-Unit    w e = refl
      dst-none ST.b-Void    w e = refl
      dst-none ST.b-Int     w e = refl
      dst-none ST.b-Float   w e = refl
      dst-none (ST.b-* _ _) w ()
      dst-none (ST.b-+ _ _) w ()
      halt-seg : ∀ s m → inMem (SigOpInfo.conB (info s)) ≡ false → Seg prog (fpc fs) (lowOp s m bot)
               → Seg prog (fpc fs) (argIn (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info (opSig s m)) ∷ [])
      halt-seg s nothing  k sq =
        Seg-++ˡ prog (fpc fs) (argIn (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ mov-to-input ∷ instr-sigop (info s) ∷ [])
          (answer (SigOpInfo.conB (info s)) bot)
          (subst (λ l → Seg prog (fpc fs) (argIn (SigOpInfo.baseA (info s)) bot (wsz ⌜ sdom s ⌝) ∷ mov-to-input
                                            ∷ l ++ instr-sigop (info s) ∷ answer (SigOpInfo.conB (info s)) bot))
                 (dst-none (SigOpInfo.conB (info s)) (wsz ⌜ scod s ⌝) k) sq)
      halt-seg s (just o) k sq = Seg-++ˡ prog (fpc fs) _ _ sq
      case-out : _ → _
      case-out (fs′ , st , hlt , lg , lft) = 3 , fs′ , st , hlt , lg , lft , Here.h-run H
