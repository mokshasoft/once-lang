-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.OpMachine — plan 0.146 B1.5 (D426, D428, D429): ★ AN OP AT
-- THE MACHINE. An op's contract path (`OpPath` over `opF`), its calls
-- answered by the interpretation's world from a history, is what the
-- machine's sigop computes at a state whose log is that history
-- (`StepOp.OpVal`/`OpHalt`): the same events (the call at the decoded
-- argument, `ArgDecode`), the same halting, and the answer's word the
-- Output. By the contract class (`SigOp.Info.SigOpSem`), as master's
-- `IRObsCorrect.SigOp`: an emitting, halting or answering op here; a pure
-- one, a compare, and a codomain that fits no register are what the module
-- is given (`OpsOwed`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
import Once.IR.Semantics.Boundary
import Once.Type
import Once.Contract
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.LinCore.Flat using (Base)
open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi; module FrameSemantics)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
import Once.Spec.Type as ST
open import Once.Type using (fits-int; fits-float)
open import Once.SigOp.Info using (SigOpInfo; mk-info'; SigOpSem; emitsV; haltsV; callsV)
import Once.IR.Semantics.Trace as TM

module Once.LinCore.OpMachine (Mach : FrameSemantics) (bw : Base → ℕ) where

private
  fmt = fs-numerics Mach
  ans = fs-ffi Mach
  ι   = FrameSemantics.fs-interp Mach

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (MV; er; mone; mbase; mvF; OpPath; p-ret; p-call; p-halt; Trace)
import Once.LinCore.Events
open import Once.LinCore.Keys fmt ans bw using (Univ)
open import Once.LinCore.Total fmt ans bw using (WTr)
open import Once.LinCore.StepOp fmt ans bw using (module Agree; evsOf)
open import Once.LinCore.Words fmt ans bw using (module Rel)
open import Once.LinCore.Lower fmt ans bw using (flatB)
import Once.LinCore.BudgetSound
import Once.LinCore.ArgDecode

module OM (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach)
          (w-int   : ∀ (n : ⟦ int ⟧b)   → wordOf {int} n ≡ SV-Lit fits-int n)
          (w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n) where
  open Agree {Mach} U wordOf using (OpVal; OpHalt; arg; at-arg; argV)
  open Rel {Mach} U wordOf using (W; VW; vone; vbase; SlotsAt)
  open Once.LinCore.BudgetSound.W fmt ans bw ι using (Wι; answered)
  open Once.LinCore.ArgDecode.Dec fmt ans bw {Mach} U wordOf w-int w-float using (arg-dec)
  open AbstractExec {Mach} using (exec-sigop-halts; sigop-events; exec-sigop-output; decode-at; events-at-arg)
  open FlatMachine {Mach} using (FlatState; floc)
  open import Once.LinCore.Moves {Mach} using (slot)

  -- ★ an emitting op: a call answered `tt`, no value, the machine goes on
  op-emits : ∀ {A} {n} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
           → OpPath (opF (sig (mk-info' n (emitsV refl) bA ST.b-Unit)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
           → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
           → OpVal (sig (mk-info' n (emitsV refl) bA ST.b-Unit)) x (mvF funit y₀) (evsOf tp) fs
  op-emits {bA = bA} {x = x} (p-call p-ret) w fs lg d wx px sx =
    refl , cong (events-at-arg (mk-info' _ (emitsV refl) bA ST.b-Unit)) (arg-dec bA fs d _ px sx) , [] , vone , inj₁ refl

  -- ★ a halting op: a halt, the machine halts with the halt's event
  op-halts : ∀ {A} {n} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {tp L L′}
           → OpPath (opF (sig (mk-info' n (haltsV refl) bA ST.b-Void)) (toF (flatB bA) (er x))) tp (inj₂ Once.LinCore.Events.halted)
           → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
           → OpHalt (sig (mk-info' n (haltsV refl) bA ST.b-Void)) x (evsOf tp) fs
  op-halts {bA = bA} p-halt w fs lg d wx px sx =
    refl , cong (events-at-arg (mk-info' _ (haltsV refl) bA ST.b-Void)) (arg-dec bA fs d _ px sx)

  -- ★ an answering op whose answer is a register word: the interpretation's answer at the history
  private
    ans-word : ∀ {A B} (si : SigOpInfo A B) (fit : Once.Type.FitsInReg B) (st : LocState Mach) {a b L} (nu : B ≡ ST.Unit → ⊥)
             → LocState.ev-log st ≡ L
             → decode-at (SigOpInfo.baseA si) (readReg (LocState.regs st) Input1) st ≡ just a
             → (D : Dec (TM.callKey (TM.callOp (SigOpInfo.name si) A (SigOpInfo.baseA si) B) ∈ TM.calls ι))
             → TM.callAnswer-at ι L (TM.callOp (SigOpInfo.name si) A (SigOpInfo.baseA si) B) a (no nu) D ≡ just b
             → AbstractExec.call-sigop-ans {Mach} si st fit D ≡ SV-Lit fit (Once.IR.Semantics.Boundary.atTarget fmt B b)
    ans-word si fit st nu refl dec (yes p) refl =
      cong (λ m → AbstractExec.call-sigop-ans-at {Mach} si st fit p m) dec
    ans-word si fit st nu lg dec (no _) ()

  -- an answering op, by its codomain
  op-calls-int : ∀ {A} {n} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
               → OpPath (opF (sig (mk-info' n callsV bA ST.b-Int)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
               → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
               → OpVal (sig (mk-info' n callsV bA ST.b-Int)) x (mvF (fw int) y₀) (evsOf tp) fs
  op-calls-int {A} {n = n} {bA = bA} {x = x} {L = L} (p-call p-ret) (h₁ , e , w) fs lg d wx px sx =
    refl , cong (events-at-arg (mk-info' n callsV bA ST.b-Int)) (arg-dec bA fs d _ px sx) ,
    _ , vbase , inj₂ (cong (_∷ []) (trans (w-int _)
                       (sym (ans-word (mk-info' n callsV bA ST.b-Int) fits-int _ (λ ()) lg (arg-dec bA fs d _ px sx)
                             (TM.callKey (TM.callOp n A bA ST.Int) Once.Contract.∈K? TM.calls ι)
                             (proj₁ (answered {h = L} {o = TM.callOp n A bA ST.Int} {a = toV bA (toF (flatB bA) (er x))} e))))))

  op-calls-float : ∀ {A} {n} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
                 → OpPath (opF (sig (mk-info' n callsV bA ST.b-Float)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
                 → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
                 → OpVal (sig (mk-info' n callsV bA ST.b-Float)) x (mvF (fw float) y₀) (evsOf tp) fs
  op-calls-float {A} {n = n} {bA = bA} {x = x} {L = L} (p-call p-ret) (h₁ , e , w) fs lg d wx px sx =
    refl , cong (events-at-arg (mk-info' n callsV bA ST.b-Float)) (arg-dec bA fs d _ px sx) ,
    _ , vbase , inj₂ (cong (_∷ []) (trans (w-float _)
                       (sym (ans-word (mk-info' n callsV bA ST.b-Float) fits-float _ (λ ()) lg (arg-dec bA fs d _ px sx)
                             (TM.callKey (TM.callOp n A bA ST.Float) Once.Contract.∈K? TM.calls ι)
                             (proj₁ (answered {h = L} {o = TM.callOp n A bA ST.Float} {a = toV bA (toF (flatB bA) (er x))} e))))))

  op-calls-unit : ∀ {A} {n} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
                → OpPath (opF (sig (mk-info' n callsV bA ST.b-Unit)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
                → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
                → OpVal (sig (mk-info' n callsV bA ST.b-Unit)) x (mvF funit y₀) (evsOf tp) fs
  op-calls-unit {n = n} {bA = bA} (p-call p-ret) w fs lg d wx px sx =
    refl , cong (events-at-arg (mk-info' n callsV bA ST.b-Unit)) (arg-dec bA fs d _ px sx) , [] , vone , inj₁ refl
