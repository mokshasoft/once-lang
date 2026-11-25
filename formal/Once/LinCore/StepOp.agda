-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepOp — plan 0.146 B1.4b (D445): AN OP STEP AGREES WITH THE
-- MACHINE. The image's op takes the world's answer as given; the flat
-- machine answers by its effect class and interpretation. The step theorem
-- is relative to the machine's world: at an op step, the machine's sigop
-- (Input1 and Output at the argument's words, as the lowering leaves them)
-- does not halt and the answer's words are none or its Output word; at a
-- halting op it halts. Every other step: nothing. The split on the step
-- lives here, in a module of its own.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; Σ)
open import Data.Bool using (Bool; false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Type using (fits-int)
open import Once.Arith.SigOp.Compare using (CmpAt; cmp-block-info)
import Once.Spec.Type as ST
open import Once.SigOp.Info using (module SigOpInfo)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtStack)
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.StepOp
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (Base; ⟦_⟧b)
open import Once.IR.Semantics.Trace using (T)
open Sig using (info; sA)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (Io; io-call; io-halt; ios)
open import Once.LinCore.Values fmt bw using (MV; Trace)
open import Once.IR.Semantics.Event using (SigOpEvent)
open import Once.IR.Semantics.Trace using (callEvent; haltEvent)
open import Once.LinCore.Code fmt bw using (Sh)
open import Once.LinCore.Image fmt bw using (Codeᴵ)
open import Once.LinCore.ImageRun fmt ans bw using (Ret; StepI; i-unpair; i-pair; i-swap; i-unit; i-prim; i-opend; i-untag; i-untag₁; i-tag₁; i-case₁; i-case₂; i-elend; i-eunlend; i-elift; i-efst; i-esnd; i-eout; i-eoutq; i-ecase₁; i-ecase₂; i-eapp; i-epop; i-eword; i-call; i-ret; i-reti; i-loop; i-icall; i-icallω; i-oncify; i-iobs; i-ccopy; i-ncopy; i-cfree; i-nfree; i-open1; i-openω; i-nopen; i-copen; i-copenν; i-reclose; i-recloseν; i-fopen; i-fopenν)
open import Once.LinCore.Keys fmt bw using (Univ)
open import Once.LinCore.Lower fmt bw using (cmpOf; opSig; inMem)
open import Once.LinCore.Words fmt ans bw using (module Rel)

-- ★ D446: what a trace shows the machine's log: its calls and halts, each the
-- sigop event of the op, its argument (the answer is the world's)
ioEvent : Io → SigOpEvent
ioEvent (io-call o a _) = callEvent o a
ioEvent (io-halt o a)   = haltEvent o a

evsOf : Trace → List SigOpEvent
evsOf t = map ioEvent (ios t)

-- the head word, or a default
hdOr : ∀ {X : Set} → List X → X → X
hdOr (w ∷ _) _ = w
hdOr []      p = p

module Agree {FS : FrameSemantics} (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue FS) where
  open Rel {FS} U wordOf using (W; VW; SlotsAt)
  open FlatMachine {FS} using (FlatState; module FlatState)
  open FlatState using (floc; falloc)
  open AbstractExec {FS} using (exec-sigop-output; exec-sigop-halts; sigop-events; exec-sigop-faults)
  open import Once.LinCore.Moves {FS} using (slot)

  -- the sigop's state: Input1 and Output the argument's word (`argIn`, `mov-to-input`)
  at-arg : FlatState → StoredValue FS → LocState FS
  at-arg fs v = record (floc fs) { regs = writeReg (writeReg (LocState.regs (floc fs)) Output v) Input1 v }

  -- ★ D447: the argument's word, by its base (D398): a scalar its one word, any other its address
  argV : ∀ {A} → ST.Base ST.∅ₖ A → FlatState → ℕ → List W → StoredValue FS
  argV (ST.b-var {i = ()} _) fs d wx
  argV ST.b-Unit    fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)
  argV ST.b-Void    fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)
  argV ST.b-Int     fs d wx = hdOr wx (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d))
  argV ST.b-Float   fs d wx = hdOr wx (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d))
  argV (ST.b-* _ _) fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)
  argV (ST.b-+ _ _) fs d wx = SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) d)

  -- the sigop's state at an argument at slot `d` of words `wx`
  arg : Sig → FlatState → ℕ → List W → LocState FS
  arg s fs d wx = at-arg fs (argV (SigOpInfo.baseA (info s)) fs d wx)

  -- an op's answer, by the sigop its code runs (D447): the machine does not halt; the answer's
  -- words are none or its Output word, or (a compare) its Output's truth as a tag
  -- ★ D451: the sigop's state for an answer in memory: `Output` its destination's address
  argD : Sig → FlatState → ℕ → ℕ → List W → LocState FS
  argD s fs d dst wx = record (arg s fs d wx)
    { regs = writeReg (LocState.regs (arg s fs d wx)) Output (SV-Ptr (AtStack (AllocState.current-frame (falloc fs)) dst)) }

  -- an answer not in memory: none, or the sigop's `Output` word; one in memory: its words
  -- where the sigop writes them, at any destination `dst` of the frame (`sigop-store`)
  OpValN : Bool → (s : Sig) → MV ⌜ sdom s ⌝ → MV ⌜ scod s ⌝ → List SigOpEvent → FlatState → Set
  OpValN false s x y E fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                 → (exec-sigop-halts (info s) (arg s fs d wx) ≡ false)
                   × (sigop-events (info s) (arg s fs d wx) ≡ E)
                   × Σ (List W) λ wy → VW (LocState.heapMem (floc fs)) y wy
                       × ((wy ≡ []) ⊎ (wy ≡ exec-sigop-output (info s) (arg s fs d wx) ∷ []))
  OpValN true s x y E fs = ∀ d dst (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                 → (exec-sigop-halts (info s) (argD s fs d dst wx) ≡ false)
                   × (sigop-events (info s) (argD s fs d dst wx) ≡ E)
                   × Σ (List W) λ wy → VW (LocState.heapMem (floc fs)) y wy
                       × SlotsAt (LocState.stackMem (AbstractExec.sigop-store {FS} (info s) (argD s fs d dst wx))
                                   (AllocState.current-frame (falloc fs))) dst wy

  OpValM : (s : Sig) → Maybe (CmpAt (sA s)) → MV ⌜ sdom s ⌝ → MV ⌜ scod s ⌝ → List SigOpEvent → FlatState → Set
  OpValM s nothing x y E fs = OpValN (inMem (SigOpInfo.conB (info s))) s x y E fs
  OpValM s (just o) x y E fs = ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                 → (exec-sigop-halts (cmp-block-info o) (arg s fs d wx) ≡ false)
                   × (sigop-events (cmp-block-info o) (arg s fs d wx) ≡ E)
                   × Σ _ λ k → (exec-sigop-output (cmp-block-info o) (arg s fs d wx) ≡ SV-Lit fits-int k)
                       × VW (LocState.heapMem (floc fs)) y (sv-nz (SV-Lit {FS} fits-int k) ∷ [])

  OpVal : (s : Sig) → MV ⌜ sdom s ⌝ → MV ⌜ scod s ⌝ → List SigOpEvent → FlatState → Set
  OpVal s = OpValM s (cmpOf s)

  -- a halting op: the machine halts
  OpHalt : (s : Sig) → MV ⌜ sdom s ⌝ → List SigOpEvent → FlatState → Set
  OpHalt s x E fs = (inMem (SigOpInfo.conB (info s)) ≡ false) × ∀ d (wx : List W) → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
                → (exec-sigop-halts (info (opSig s (cmpOf s))) (arg s fs d wx) ≡ true)
                  × (sigop-events (info (opSig s (cmpOf s))) (arg s fs d wx) ≡ E)
                  -- (a halt, not a fault)
                  × (exec-sigop-faults (info (opSig s (cmpOf s))) (arg s fs d wx) ≡ false)

  -- a prim step's agreement, by its term alone: an op's contract, nothing for the rest
  -- (a function of the term, so a proof splits the term, not the step, to reduce it)
  PrimOk : ∀ {Γ A B} → LTm Γ A B → MV A → MV B → Trace → FlatState → Set
  PrimOk (lop s) x y t fs = OpVal s x y (evsOf t) fs
  {-# CATCHALL #-}
  PrimOk _ _ _ _ _ = ⊤

  module _ {T : Sh} where
    Agrees : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
           → StepI c r m n t c′ r′ m′ n′ → FlatState → Set
    Agrees (i-prim {g = g} {v = x} {w = y} {t = t} _) fs = PrimOk g x y t fs
    Agrees (i-opend {s = s} {x = x} {t = t} _) fs = OpHalt s x (evsOf t) fs
    {-# CATCHALL #-}
    Agrees _ fs = ⊤

    -- ★ a step by what it owes: a prim (its `PrimOk`), an op that halts (`OpHalt`), or a
    -- quiet step (no i/o, nothing owed). The one split on a step for `Agrees`, here in a
    -- small context: a split of `StepI` unifies its indices with the whole clause context
    -- (in `AgreeRun`'s module it cost 30 s, here a few).
    data StepCase : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
                  → StepI c r m n t c′ r′ m′ n′ → Set where
      sc-prim  : ∀ {Γ ds Es A B S U g k r es v w os n n′ t run}
               → StepCase (i-prim {Γ = Γ} {ds = ds} {Es = Es} {A = A} {B = B} {S = S} {U = U} {g = g} {k = k} {r = r}
                                   {es = es} {v = v} {w = w} {os = os} {n = n} {n′ = n′} {t = t} run)
      sc-opend : ∀ {Γ ds Es s S U k r es x os n t p}
               → StepCase (i-opend {Γ = Γ} {ds = ds} {Es = Es} {s = s} {S = S} {U = U} {k = k} {r = r}
                                    {es = es} {x = x} {os = os} {n = n} {t = t} p)
      sc-quiet : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
                   {st : StepI c r m n t c′ r′ m′ n′}
               → ios t ≡ [] → (∀ fs → Agrees st fs) → StepCase st

    step-case : ∀ {sh U′ sh′ U″} {c : Codeᴵ sh U′} {r : Ret U′ T} {m n t} {c′ : Codeᴵ sh′ U″} {r′ : Ret U″ T} {m′ n′}
              → (st : StepI c r m n t c′ r′ m′ n′) → StepCase st
    step-case (i-prim run) = sc-prim
    step-case (i-opend p) = sc-opend
    step-case i-unpair = sc-quiet refl (λ _ → tt)
    step-case i-pair = sc-quiet refl (λ _ → tt)
    step-case i-swap = sc-quiet refl (λ _ → tt)
    step-case i-unit = sc-quiet refl (λ _ → tt)
    step-case i-untag = sc-quiet refl (λ _ → tt)
    step-case i-oncify = sc-quiet refl (λ _ → tt)
    step-case i-untag₁ = sc-quiet refl (λ _ → tt)
    step-case i-tag₁ = sc-quiet refl (λ _ → tt)
    step-case i-case₁ = sc-quiet refl (λ _ → tt)
    step-case i-case₂ = sc-quiet refl (λ _ → tt)
    step-case i-elend = sc-quiet refl (λ _ → tt)
    step-case i-eunlend = sc-quiet refl (λ _ → tt)
    step-case i-elift = sc-quiet refl (λ _ → tt)
    step-case i-epop = sc-quiet refl (λ _ → tt)
    step-case i-call = sc-quiet refl (λ _ → tt)
    step-case i-ret = sc-quiet refl (λ _ → tt)
    step-case i-reti = sc-quiet refl (λ _ → tt)
    step-case i-loop = sc-quiet refl (λ _ → tt)
    step-case i-icall = sc-quiet refl (λ _ → tt)
    step-case i-iobs = sc-quiet refl (λ _ → tt)
    step-case i-cfree = sc-quiet refl (λ _ → tt)
    step-case i-nfree = sc-quiet refl (λ _ → tt)
    step-case i-open1 = sc-quiet refl (λ _ → tt)
    step-case i-nopen = sc-quiet refl (λ _ → tt)
    step-case i-fopen = sc-quiet refl (λ _ → tt)
    step-case i-fopenν = sc-quiet refl (λ _ → tt)
    step-case (i-efst _) = sc-quiet refl (λ _ → tt)
    step-case (i-esnd _) = sc-quiet refl (λ _ → tt)
    step-case (i-eout _) = sc-quiet refl (λ _ → tt)
    step-case (i-eoutq _) = sc-quiet refl (λ _ → tt)
    step-case (i-ecase₁ _) = sc-quiet refl (λ _ → tt)
    step-case (i-ecase₂ _) = sc-quiet refl (λ _ → tt)
    step-case (i-eapp _) = sc-quiet refl (λ _ → tt)
    step-case (i-eword _) = sc-quiet refl (λ _ → tt)
    step-case (i-icallω _) = sc-quiet refl (λ _ → tt)
    step-case (i-ccopy _) = sc-quiet refl (λ _ → tt)
    step-case (i-ncopy _) = sc-quiet refl (λ _ → tt)
    step-case (i-openω _) = sc-quiet refl (λ _ → tt)
    step-case (i-copen _) = sc-quiet refl (λ _ → tt)
    step-case (i-copenν _) = sc-quiet refl (λ _ → tt)
    step-case (i-reclose _) = sc-quiet refl (λ _ → tt)
    step-case (i-recloseν _) = sc-quiet refl (λ _ → tt)
