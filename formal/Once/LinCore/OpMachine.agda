-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.OpMachine — plan 0.146 B1.5 (D443, D445, D446): ★ AN OP AT
-- THE MACHINE. An op's contract path (`OpPath` over `opF`), its calls
-- answered by the interpretation's world from a history, is what the
-- machine's sigop computes at a state whose log is that history
-- (`StepOp.OpVal`/`OpHalt`): the same events (the call at the decoded
-- argument, `ArgDecode`), the same halting, and the same answer: a scalar
-- the Output's word, a product or a sum its words written in place at the
-- result's slots (D449, `AnsWrite`), Unit none. By the contract class
-- (`SigOp.Info.SigOpSem`), as master's `IRObsCorrect.SigOp`: every class,
-- for every base answer (`Dispatch`).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
import Once.IR.Semantics.Boundary
import Once.Type
import Once.Contract
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
import Once.Type.Core
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Once.CCC.Machine.Locations using (AtStack)
open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Type.Core using (isUnit?)
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

open import Once.LinCore.Core fmt
open import Once.LinCore.Flat using (funit; fw; Base; int; float; ⟦_⟧b)
open import Once.IR.Semantics.Trace using (T)
open Sig using (info)
open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw using (er; OpPath; p-ret; p-call; p-halt)
open import Once.LinCore.Values fmt bw using (MV; mone; mbase; mpair; mvF; Trace)
import Once.LinCore.Events
open import Once.LinCore.Keys fmt bw using (Univ)
open import Once.LinCore.Total fmt ans bw using (WTr; CutOp; CutAt; c-here; c-call)
open import Once.LinCore.StepOp fmt ans bw using (module Agree; evsOf)
open import Once.LinCore.Words fmt ans bw using (module Rel)
open import Once.LinCore.Lower fmt bw using (flatB; inMem)
import Once.LinCore.AnsWrite
import Once.LinCore.BudgetSound
import Once.LinCore.ArgDecode
import Once.Semantics.Machine

module OM (U : Univ) (wordOf : ∀ {b} → ⟦ b ⟧b → StoredValue Mach)
          (w-int   : ∀ (n : ⟦ int ⟧b)   → wordOf {int} n ≡ SV-Lit fits-int n)
          (w-float : ∀ (n : ⟦ float ⟧b) → wordOf {float} n ≡ SV-Lit fits-float n) where
  open Agree {Mach} U wordOf using (OpVal; OpHalt; arg; at-arg; argV)
  open Rel {Mach} U wordOf using (W; VW; vone; vbase; vinl; vinr; SlotsAt)
  open Once.LinCore.BudgetSound.W fmt ans bw ι using (Wι; answered)
  open Once.LinCore.ArgDecode.Dec fmt ans bw {Mach} U wordOf w-int w-float using (arg-dec)
  open AbstractExec {Mach} using (exec-sigop-halts; sigop-events; exec-sigop-output; decode-at; events-at-arg)
  open FlatMachine {Mach} using (FlatState; module FlatState)
  open FlatState using (floc)
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
  op-halts {bA = bA} p-halt w fs lg =
    refl , λ d wx px sx → refl , cong (events-at-arg (mk-info' _ (haltsV refl) bA ST.b-Void)) (arg-dec bA fs d _ px sx) , refl

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

  -- ★ a pure op reads its argument as the sigop decodes it: a scalar from the register, any
  -- other base value in place
  open Once.LinCore.ArgDecode.Dec fmt ans bw {Mach} U wordOf w-int w-float using (read-in)
  open AbstractExec {Mach} using (pure-sigop-out-aux; pure-sigop-out-val)
  arg-in : ∀ {A B} (si : SigOpInfo A B) (fit : Once.Type.FitsInReg B) (fs : FlatState) d (wx : List W)
             {x : MV ⌜ flatB (SigOpInfo.baseA si) ⌝}
         → VW (LocState.heapMem (floc fs)) x wx → SlotsAt (slot fs) d wx
         → pure-sigop-out-aux si (at-arg fs (argV (SigOpInfo.baseA si) fs d wx)) (just fit)
             (sv-as-loc (argV (SigOpInfo.baseA si) fs d wx))
           ≡ pure-sigop-out-val si fit (just (toV (SigOpInfo.baseA si) (toF (flatB (SigOpInfo.baseA si)) (er x))))
  arg-in (mk-info' n c (ST.b-var {i = ()} _) bB) fit fs d wx px sx
  arg-in (mk-info' n c ST.b-Unit bB) fit fs d wx vone sx = refl
  arg-in (mk-info' n c ST.b-Void bB) fit fs d wx () sx
  arg-in si@(mk-info' n c ST.b-Int bB) fit fs d (w ∷ []) (vbase {x = v}) sx =
    cong (λ z → pure-sigop-out-aux si (at-arg fs z) (just fit) (sv-as-loc z)) (w-int v)
  arg-in si@(mk-info' n c ST.b-Float bB) fit fs d (w ∷ []) (vbase {x = v}) sx =
    cong (λ z → pure-sigop-out-aux si (at-arg fs z) (just fit) (sv-as-loc z)) (w-float v)
  arg-in si@(mk-info' n c (ST.b-* a b) bB) fit fs d wx px sx =
    cong (pure-sigop-out-val si fit) (read-in (ST.b-* a b) (at-arg fs _) (AllocState.current-frame (FlatMachine.FlatState.falloc fs)) d px sx)
  arg-in si@(mk-info' n c (ST.b-+ a b) bB) fit fs d wx px sx =
    cong (pure-sigop-out-val si fit) (read-in (ST.b-+ a b) (at-arg fs _) (AllocState.current-frame (FlatMachine.FlatState.falloc fs)) d px sx)

  -- ★ a pure op (not a compare) whose value fits a register or is none
  open import Once.SigOp.Info using (effect-of; semM-of; Pure)
  open import Once.Arith.SigOp.Compare using (cmp-of)
  open import Once.Res using (returns)
  import Once.Denotation.DenotTrace as DT
  open AbstractExec {Mach} using (exec-sigop-halts-of; sigop-events-of; exec-sigop-output-of; unread?)
  open Agree {Mach} U wordOf using (OpValM)

  private
    ret-path : ∀ {X : Set} {v : X} {tp y₀} → OpPath (TM.ret v) tp (inj₁ y₀) → (tp ≡ []) × (y₀ ≡ v)
    ret-path p-ret = refl , refl

  -- the value both readers give, at the argument
  PureAgree : ∀ {A B} (n : _) (c : SigOpSem A B) (bA : ST.Base ST.∅ₖ A) (bB : ST.Base ST.∅ₖ B) → _ → Set
  PureAgree {B = B} n c bA bB a =
    Σ (Once.Semantics.Machine.Value.⟦ B ⟧) λ w →
      (semM-of ans n c fmt a ≡ returns w) × (DT.sigOpSemT fmt ans (mk-info' n c bA bB) c a ≡ TM.ret w)

  op-pure-int : ∀ {A} {n} {c : SigOpSem A ST.Int} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
              → effect-of c ≡ Pure → cmp-of c ≡ nothing → PureAgree n c bA ST.b-Int (toV bA (toF (flatB bA) (er x)))
              → OpPath (opF (sig (mk-info' n c bA ST.b-Int)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
              → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
              → OpVal (sig (mk-info' n c bA ST.b-Int)) x (mvF (fw int) y₀) (evsOf tp) fs
  op-pure-int {n = n} {c = c} {bA = bA} {x = x} {y₀ = y₀} {tp = tp} ep nc (w , sm , tr) p wt fs lg =
    subst (λ m → OpValM (sig si) m x (mvF (fw int) y₀) (evsOf tp) fs) (sym nc) body
    where
      si = mk-info' n c bA ST.b-Int
      rp = ret-path (subst (λ T → OpPath (fmapT (fromV ST.b-Int) T) tp (inj₁ y₀)) tr p)
      body : OpValM (sig si) nothing x (mvF (fw int) y₀) (evsOf tp) fs
      body d wx px sx =
        trans (cong (λ e → exec-sigop-halts-of e si st) ep) (cong unread? (arg-dec bA fs d _ px sx)) ,
        trans (cong (λ e → sigop-events-of e si st) ep) (cong evsOf (sym (proj₁ rp))) ,
        _ , vbase ,
        inj₂ (cong (_∷ []) (trans (cong wordOf (proj₂ rp)) (trans (w-int w)
          (sym (trans (cong (λ e → exec-sigop-output-of e si st) ep)
                 (trans (arg-in si fits-int fs d wx px sx)
                        (cong (AbstractExec.res-sv {Mach} fits-int) sm)))))))
        where st = arg (sig si) fs d wx

  op-pure-float : ∀ {A} {n} {c : SigOpSem A ST.Float} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
                → effect-of c ≡ Pure → cmp-of c ≡ nothing → PureAgree n c bA ST.b-Float (toV bA (toF (flatB bA) (er x)))
                → OpPath (opF (sig (mk-info' n c bA ST.b-Float)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
                → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
                → OpVal (sig (mk-info' n c bA ST.b-Float)) x (mvF (fw float) y₀) (evsOf tp) fs
  op-pure-float {n = n} {c = c} {bA = bA} {x = x} {y₀ = y₀} {tp = tp} ep nc (w , sm , tr) p wt fs lg =
    subst (λ m → OpValM (sig si) m x (mvF (fw float) y₀) (evsOf tp) fs) (sym nc) body
    where
      si = mk-info' n c bA ST.b-Float
      rp = ret-path (subst (λ T → OpPath (fmapT (fromV ST.b-Float) T) tp (inj₁ y₀)) tr p)
      body : OpValM (sig si) nothing x (mvF (fw float) y₀) (evsOf tp) fs
      body d wx px sx =
        trans (cong (λ e → exec-sigop-halts-of e si st) ep) (cong unread? (arg-dec bA fs d _ px sx)) ,
        trans (cong (λ e → sigop-events-of e si st) ep) (cong evsOf (sym (proj₁ rp))) ,
        _ , vbase ,
        inj₂ (cong (_∷ []) (trans (cong wordOf (proj₂ rp)) (trans (w-float w)
          (sym (trans (cong (λ e → exec-sigop-output-of e si st) ep)
                 (trans (arg-in si fits-float fs d wx px sx)
                        (cong (AbstractExec.res-sv {Mach} fits-float) sm)))))))
        where st = arg (sig si) fs d wx

  op-pure-unit : ∀ {A} {n} {c : SigOpSem A ST.Unit} {bA : ST.Base ST.∅ₖ A} {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
               → effect-of c ≡ Pure → cmp-of c ≡ nothing → PureAgree n c bA ST.b-Unit (toV bA (toF (flatB bA) (er x)))
               → OpPath (opF (sig (mk-info' n c bA ST.b-Unit)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
               → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
               → OpVal (sig (mk-info' n c bA ST.b-Unit)) x (mvF funit y₀) (evsOf tp) fs
  op-pure-unit {n = n} {c = c} {bA = bA} {x = x} {y₀ = y₀} {tp = tp} ep nc (w , sm , tr) p wt fs lg =
    subst (λ m → OpValM (sig si) m x (mvF funit y₀) (evsOf tp) fs) (sym nc) body
    where
      si = mk-info' n c bA ST.b-Unit
      rp = ret-path (subst (λ T → OpPath (fmapT (fromV ST.b-Unit) T) tp (inj₁ y₀)) tr p)
      body : OpValM (sig si) nothing x (mvF funit y₀) (evsOf tp) fs
      body d wx px sx =
        trans (cong (λ e → exec-sigop-halts-of e si st) ep) (cong unread? (arg-dec bA fs d _ px sx)) ,
        trans (cong (λ e → sigop-events-of e si st) ep) (cong evsOf (sym (proj₁ rp))) ,
        [] , vone , inj₁ refl
        where st = arg (sig si) fs d wx

  -- ★ the per-op facts, by the op's contract. What stays owed, narrowed: an answer of a
  -- structured type (a product, or a sum that is not a compare's) has no machine
  -- semantics yet (master owes it too: `structured-pure-sigop-output`). An undeclared FFI
  -- op stops where the machine goes on: excluded by linkedness (D448, `Dispatch.decl`).
  -- ★ D449: AN ANSWER IN MEMORY (a product, a sum), as every other value's: the sigop writes
  -- its words at the destination `Output` holds (`sigop-store`), the image's (`AnsWrite`)
  open Agree {Mach} U wordOf using (OpValN; argD)
  open Once.LinCore.ArgDecode.Dec fmt ans bw {Mach} U wordOf w-int w-float using (arg-decD)
  open Once.LinCore.AnsWrite.Wr fmt ans bw {Mach} U wordOf w-int w-float using (st-words)
  open AbstractExec {Mach} using (sigop-answer; sigop-answer-of; pure-ans-at; res-just; call-ans-at; call-sigop-dec)

  op-mem-pure : ∀ {A B} {n} {c : SigOpSem A B} {bA : ST.Base ST.∅ₖ A} (bB : ST.Base ST.∅ₖ B) {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
              → inMem bB ≡ true → in-memory? B ≡ true
              → effect-of c ≡ Pure → cmp-of c ≡ nothing → PureAgree n c bA bB (toV bA (toF (flatB bA) (er x)))
              → OpPath (opF (sig (mk-info' n c bA bB)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
              → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
              → OpVal (sig (mk-info' n c bA bB)) x (mvF (flatB bB) y₀) (evsOf tp) fs
  op-mem-pure {B = B} {n = n} {c = c} {bA = bA} bB {x = x} {y₀ = y₀} {tp = tp} ik im ep nc (w , sm , tr) p wt fs lg =
    subst (λ m → OpValM (sig si) m x (mvF (flatB bB) y₀) (evsOf tp) fs) (sym nc)
      (subst (λ k → OpValN k (sig si) x (mvF (flatB bB) y₀) (evsOf tp) fs) (sym ik) body)
    where
      si = mk-info' n c bA bB
      rp = ret-path (subst (λ T → OpPath (fmapT (fromV bB) T) tp (inj₁ y₀)) tr p)
      body : OpValN true (sig si) x (mvF (flatB bB) y₀) (evsOf tp) fs
      body d dst wx px sx =
        trans (cong (λ e → exec-sigop-halts-of e si st) ep) (cong unread? dec) ,
        trans (cong (λ e → sigop-events-of e si st) ep) (cong evsOf (sym (proj₁ rp))) ,
        wd (st-words bB (in-memory? B) im (sigop-answer si st) w ans≡ cf dst st {h = LocState.heapMem (floc fs)})
        where
          cf = AllocState.current-frame (FlatMachine.FlatState.falloc fs)
          st = argD (sig si) fs d dst wx
          dec = arg-decD bA fs d (argV bA fs d wx) (SV-Ptr (AtStack cf dst)) px sx
          ans≡ : sigop-answer si st ≡ just w
          ans≡ = trans (cong (λ e → sigop-answer-of e si st) ep)
                   (trans (cong (pure-ans-at si) dec) (cong res-just sm))
          wd : _ → _
          wd (wy , pw , sy) = wy , subst (λ z → VW (LocState.heapMem (floc fs)) (mvF (flatB bB) z) wy) (sym (proj₂ rp)) pw , sy

  private
    ans-mem : ∀ {A B} (si : SigOpInfo A B) (st : LocState Mach) {a b L} (u : Dec (B ≡ ST.Unit)) (nu : B ≡ ST.Unit → ⊥)
            → LocState.ev-log st ≡ L
            → (D : Dec (TM.callKey (TM.callOp (SigOpInfo.name si) A (SigOpInfo.baseA si) B) ∈ TM.calls ι))
            → TM.callAnswer-at ι L (TM.callOp (SigOpInfo.name si) A (SigOpInfo.baseA si) B) a u D ≡ just b
            → call-ans-at si st D (just a) ≡ just (Once.IR.Semantics.Boundary.atTarget fmt B b)
    ans-mem si st (yes eq) nu lg D e = ⊥-elim (nu eq)
    ans-mem si st (no _) nu refl (yes p) refl = refl
    ans-mem si st (no _) nu lg (no _) ()

  op-mem-calls : ∀ {A B} {n} {bA : ST.Base ST.∅ₖ A} (bB : ST.Base ST.∅ₖ B) {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
               → inMem bB ≡ true → in-memory? B ≡ true → (B ≡ ST.Unit → ⊥)
               → OpPath (opF (sig (mk-info' n callsV bA bB)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
               → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
               → OpVal (sig (mk-info' n callsV bA bB)) x (mvF (flatB bB) y₀) (evsOf tp) fs
  op-mem-calls {A} {B} {n = n} {bA = bA} bB {x = x} {y₀ = y₀} {tp = tp} {L = L} ik im nu (p-call p-ret) (h₁ , e , w) fs lg =
    subst (λ k → OpValN k (sig si) x (mvF (flatB bB) y₀) (evsOf tp) fs) (sym ik) body
    where
      si = mk-info' n callsV bA bB
      body : OpValN true (sig si) x (mvF (flatB bB) y₀) (evsOf tp) fs
      body d dst wx px sx =
        refl , cong (events-at-arg si) dec ,
        wd (st-words bB (in-memory? B) im (sigop-answer si st) _ ans≡ cf dst st {h = LocState.heapMem (floc fs)})
        where
          cf = AllocState.current-frame (FlatMachine.FlatState.falloc fs)
          st = argD (sig si) fs d dst wx
          dec = arg-decD bA fs d (argV bA fs d wx) (SV-Ptr (AtStack cf dst)) px sx
          ans≡ = trans (cong (call-ans-at si st (call-sigop-dec si)) dec)
                   (ans-mem si st (isUnit? B) nu lg (TM.callKey (TM.callOp n A bA B) Once.Contract.∈K? TM.calls ι)
                     (proj₁ (answered {h = L} {o = TM.callOp n A bA B} {a = toV bA (toF (flatB bA) (er x))} e)))
          wd : _ → _
          wd (wy , pw , sy) = wy , pw , sy

  open import Once.Res using (Res; stopped; mapRes)
  open import Once.SigOp.Info using (blockV; primV; ffiV)
  open import Once.Arith.Prim using (ArithPrim; p-add; p-sub; p-mul; p-div; p-mod; p-neg; p-fadd; p-fsub; p-fmul; p-fdiv; p-i2f; p-cmp; p-fneg; p-fcmp)
  open import Once.Arith.Type using (NInt; NFloat)

  OpValAt : ∀ {A B} n (c : SigOpSem A B) (bA : ST.Base ST.∅ₖ A) (bB : ST.Base ST.∅ₖ B) → Set
  OpValAt n c bA bB = ∀ {x : MV ⌜ flatB bA ⌝} {y₀ tp L L′}
    → OpPath (opF (sig (mk-info' n c bA bB)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
    → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
    → OpVal (sig (mk-info' n c bA bB)) x (mvF (flatB bB) y₀) (evsOf tp) fs

  OpHaltAt : ∀ {A B} n (c : SigOpSem A B) (bA : ST.Base ST.∅ₖ A) (bB : ST.Base ST.∅ₖ B) → Set
  OpHaltAt n c bA bB = ∀ {x : MV ⌜ flatB bA ⌝} {tp L L′}
    → OpPath (opF (sig (mk-info' n c bA bB)) (toF (flatB bA) (er x))) tp (inj₂ Once.LinCore.Events.halted)
    → WTr Wι L tp L′ → ∀ fs → LocState.ev-log (floc fs) ≡ L
    → OpHalt (sig (mk-info' n c bA bB)) x (evsOf tp) fs

  -- ★ a compare (D445): its code runs the compare's block, whose 0/1 word, read as a tag, is the
  -- primitive's truth (true = inr, D263)
  open import Once.Arith.SigOp.Compare using (cmp-block-info)
  open import Once.Arith.CmpOp using (cmp-word; fcmp-word-at)
  open import Once.Spec.Theory using (Has; Sym; compare; module Models; ⟦_⟧ₛ)
  open import Once.Spec.Float.Encoding using (decode)
  open import Once.Spec.Numerics using (module TargetNum)
  open import Data.Bool using (Bool; true; false; if_then_else_)

  private
    tag : ∀ {rd} (b : Bool)
        → VW rd (mvF (flatB (ST.b-+ ST.b-Unit ST.b-Unit)) (fromV (ST.b-+ ST.b-Unit ST.b-Unit) (Once.Semantics.Machine.Value.eraseᵍ {0} (Once.Arith.Prim.bool b))))
             (sv-nz (SV-Lit {Mach} fits-int (if b then 1 else 0)) ∷ [])
    tag false = vinl vone refl
    tag true  = vinr vone refl

  op-cmp : ∀ n o → OpValAt n (primV (p-cmp o)) (ST.b-* ST.b-Int ST.b-Int) (ST.b-+ ST.b-Unit ST.b-Unit)
  op-cmp n o {x = mpair (mbase i) (mbase j)} p-ret w fs lg d wx px sx =
    cong unread? (arg-dec (ST.b-* ST.b-Int ST.b-Int) fs d (argV (ST.b-* ST.b-Int ST.b-Int) fs d wx) px sx) , refl , _ ,
    arg-in (cmp-block-info (Once.Arith.SigOp.Compare.int-c o)) fits-int fs d wx px sx ,
    tag (cmp-word (TargetNum.int-bits fmt) o i j)

  -- a `Float` compare: the block's 0/1 word is the format's truth on the decoded operands
  op-fcmp : ∀ n {U} (h : Has Once.Spec.Theory.float U) (o : Sym U compare)
          → OpValAt n (primV (p-fcmp h o)) (ST.b-* ST.b-Float ST.b-Float) (ST.b-+ ST.b-Unit ST.b-Unit)
  op-fcmp n h o {x = mpair (mbase a) (mbase b)} p-ret w fs lg d wx px sx =
    cong unread? (arg-dec (ST.b-* ST.b-Float ST.b-Float) fs d (argV (ST.b-* ST.b-Float ST.b-Float) fs d wx) px sx) , refl , _ ,
    trans (arg-in (cmp-block-info (Once.Arith.SigOp.Compare.flt-c (Once.Arith.CmpOp.fcmp h o))) fits-int fs d wx px sx)
          (cong (λ t → SV-Lit {Mach} fits-int (if t then 1 else 0)) (fcmp-word-at h o fmt a b)) ,
    tag (⟦ o ⟧ₛ (Models.structure fmt h) (decode (TargetNum.float-format fmt) a , decode (TargetNum.float-format fmt) b))

  private
    res-ret : ∀ {X Z : Set} (r : Res X) {k : X → Z} {tp y₀} → OpPath (fmapT k (TM.resT r)) tp (inj₁ y₀)
            → Σ X λ w → r ≡ returns w
    res-ret (returns w) p = w , refl
    res-ret stopped ()

    res-halt : ∀ {X Z : Set} (r : Res X) {k : X → Z} {tp} → OpPath (fmapT k (TM.resT r)) tp (inj₂ Once.LinCore.Events.halted)
             → r ≡ stopped
    res-halt (returns w) ()
    res-halt stopped p = refl

    map-stopped : ∀ {X Y : Set} {g : X → Y} (r : Res X) → mapRes g r ≡ stopped → r ≡ stopped
    map-stopped (returns w) ()
    map-stopped stopped e = refl

  -- an undeclared FFI value op stops; a declared one answers
  open import Once.Denotation.Program using (Declared-at)
  open Univ using (ops)
  open import Data.Empty using (⊥-elim)
  private
    Σι = TM.Interp.sig ι
    declared-ret : ∀ {k} (dk : Dec (k ∈ TM.pures ι)) {a} → k ∈ TM.pures ι → TM.pureHalf-at ι k dk a ≡ stopped → ⊥
    declared-ret (yes _) m ()
    declared-ret (no ¬m) m _ = ¬m m

  module Dispatch (decl : ∀ {s} → s ∈ ops U → Declared-at Σι (info s) (SigOpInfo.sem (info s))) where
    private
      pure-at : ∀ {A B} n (c : SigOpSem A B) bA (bB : ST.Base ST.∅ₖ B) → effect-of c ≡ Pure → cmp-of c ≡ nothing
              → (∀ {x : MV ⌜ flatB bA ⌝} {y₀ tp} → OpPath (opF (sig (mk-info' n c bA bB)) (toF (flatB bA) (er x))) tp (inj₁ y₀)
                 → PureAgree n c bA bB (toV bA (toF (flatB bA) (er x))))
              → OpValAt n c bA bB
      pure-at n c bA (ST.b-var {i = ()} _) ep nc pa
      pure-at n c bA ST.b-Unit ep nc pa {x} p = op-pure-unit {n = n} {c = c} {bA = bA} {x = x} ep nc (pa {x} p) p
      pure-at n c bA ST.b-Void ep nc pa {y₀ = ()} p
      pure-at n c bA ST.b-Int ep nc pa {x} p = op-pure-int {n = n} {c = c} {bA = bA} {x = x} ep nc (pa {x} p) p
      pure-at n c bA ST.b-Float ep nc pa {x} p = op-pure-float {n = n} {c = c} {bA = bA} {x = x} ep nc (pa {x} p) p
      pure-at n c bA bB@(ST.b-* b₁ b₂) ep nc pa {x} p = op-mem-pure {n = n} {c = c} {bA = bA} bB {x = x} refl refl ep nc (pa {x} p) p
      pure-at n c bA bB@(ST.b-+ b₁ b₂) ep nc pa {x} p = op-mem-pure {n = n} {c = c} {bA = bA} bB {x = x} refl refl ep nc (pa {x} p) p

      prim-at : ∀ {A B} n (p : ArithPrim A B) bA bB → cmp-of (primV p) ≡ nothing → OpValAt n (primV p) bA bB
      prim-at n p bA bB nc = pure-at n (primV p) bA bB refl nc (λ _ → _ , refl , refl)

      calls-at : ∀ {A B} n bA (bB : ST.Base ST.∅ₖ B) → OpValAt {A} n callsV bA bB
      calls-at n bA (ST.b-var {i = ()} _)
      calls-at n bA ST.b-Unit = op-calls-unit
      calls-at n bA ST.b-Void {y₀ = ()} p
      calls-at n bA ST.b-Int = op-calls-int
      calls-at n bA ST.b-Float = op-calls-float
      calls-at n bA bB@(ST.b-* b₁ b₂) {x} p = op-mem-calls {n = n} {bA = bA} bB {x = x} refl refl (λ ()) p
      calls-at n bA bB@(ST.b-+ b₁ b₂) {x} p = op-mem-calls {n = n} {bA = bA} bB {x = x} refl refl (λ ()) p

    val-at : ∀ {A B} n (c : SigOpSem A B) bA bB → OpValAt n c bA bB
    val-at n (blockV e refl refl) bA bB = pure-at n (blockV e refl refl) bA bB refl refl (λ _ → _ , refl , refl)
    val-at n (primV (p-cmp o)) (ST.b-* ST.b-Int ST.b-Int) (ST.b-+ ST.b-Unit ST.b-Unit) = op-cmp n o
    val-at n (primV (p-fcmp h o)) (ST.b-* ST.b-Float ST.b-Float) (ST.b-+ ST.b-Unit ST.b-Unit) = op-fcmp n h o
    val-at n (primV p-add) bA bB = prim-at n p-add bA bB refl
    val-at n (primV p-sub) bA bB = prim-at n p-sub bA bB refl
    val-at n (primV p-mul) bA bB = prim-at n p-mul bA bB refl
    val-at n (primV p-div) bA bB = prim-at n p-div bA bB refl
    val-at n (primV p-mod) bA bB = prim-at n p-mod bA bB refl
    val-at n (primV p-neg) bA bB = prim-at n p-neg bA bB refl
    val-at n (primV p-fadd) bA bB = prim-at n p-fadd bA bB refl
    val-at n (primV p-fsub) bA bB = prim-at n p-fsub bA bB refl
    val-at n (primV p-fmul) bA bB = prim-at n p-fmul bA bB refl
    val-at n (primV p-fdiv) bA bB = prim-at n p-fdiv bA bB refl
    val-at n (primV p-i2f) bA bB = prim-at n p-i2f bA bB refl
    val-at n (primV p-fneg) bA bB = prim-at n p-fneg bA bB refl
    val-at {A} {B} n ffiV bA bB = pure-at n ffiV bA bB refl refl λ p →
      let (w , e) = res-ret (mapRes (Once.IR.Semantics.Boundary.atTarget fmt B) (ans n A B _)) p
      in w , e , cong TM.resT e
    val-at n callsV bA bB = calls-at n bA bB
    val-at n (emitsV refl) bA ST.b-Unit = op-emits
    val-at n (haltsV refl) bA bB ()

    halt-at : ∀ {A B} n (c : SigOpSem A B) bA bB → Declared-at Σι (mk-info' n c bA bB) c → OpHaltAt n c bA bB
    halt-at n (blockV e refl refl) bA bB dc ()
    halt-at n (primV p) bA bB dc ()
    halt-at {A} {B} n ffiV bA bB dc p = ⊥-elim (declared-ret _ dc (map-stopped (ans n A B _) (res-halt _ p)))
    halt-at n callsV bA bB dc (p-call ())
    halt-at n (emitsV refl) bA bB dc (p-call ())
    halt-at n (haltsV refl) bA ST.b-Void dc = op-halts

    -- ★ FlatTop's per-op facts
    o-op : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {y₀ tp L L′}
         → OpPath (opF s (toF (sdom s) (er x))) tp (inj₁ y₀) → WTr Wι L tp L′
         → ∀ fs → LocState.ev-log (floc fs) ≡ L
         → OpVal s x (mvF (scod s) y₀) (evsOf tp) fs
    o-op {sig (mk-info' n c bA bB)} = val-at n c bA bB

    o-opend : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {tp L L′} → s ∈ ops U
            → OpPath (opF s (toF (sdom s) (er x))) tp (inj₂ Once.LinCore.Events.halted) → WTr Wι L tp L′
            → ∀ fs → LocState.ev-log (floc fs) ≡ L
            → OpHalt s x (evsOf tp) fs
    o-opend {sig (mk-info' n c bA bB)} m = halt-at n c bA bB (decl m)

  -- ★ LINKED (D448): the world answers a declared op's call, so the run never cuts at a program's op
  module Linked (decl : ∀ {s} → s ∈ ops U → Declared-at Σι (info s) (SigOpInfo.sem (info s))) where
    private
      answered-at : ∀ {h o a} {X : Set} {f : _ → X} (u : Dec (TM.CallOp.ccod o ≡ ST.Unit)) (dk : Dec (TM.callKey o ∈ TM.calls ι))
                  → TM.callKey o ∈ TM.calls ι → Data.Maybe.map f (TM.callAnswer-at ι h o a u dk) ≡ nothing → ⊥
      answered-at (yes _) dk m ()
      answered-at (no _) (yes _) m ()
      answered-at (no _) (no ¬m) m _ = ¬m m

      res-cut : ∀ {X Z : Set} (r : Res X) {k : X → Z} {t} {p : OpPath (fmapT k (TM.resT r)) t (inj₂ Once.LinCore.Events.exhausted)}
              → CutAt Wι (fmapT k (TM.resT r)) p → ⊥
      res-cut (returns w) ()
      res-cut stopped ()

      cut-at : ∀ {A B} n (c : SigOpSem A B) bA bB → Declared-at Σι (mk-info' n c bA bB) c
             → ∀ {x : MV ⌜ flatB bA ⌝} {t} {p : OpPath (opF (sig (mk-info' n c bA bB)) (toF (flatB bA) (er x))) t (inj₂ Once.LinCore.Events.exhausted)}
             → CutAt Wι _ p → ⊥
      cut-at n (blockV e refl refl) bA bB d ()
      cut-at n (primV p) bA bB d ()
      cut-at {A} {B} n ffiV bA bB d cu = res-cut (mapRes (Once.IR.Semantics.Boundary.atTarget fmt B) (ans n A B _)) cu
      cut-at {A} {B} n callsV bA bB d (c-here σ e) =
        answered-at {h = σ} {o = TM.callOp n A bA B} (Once.Type.Core.isUnit? B) (TM.callKey (TM.callOp n A bA B) Once.Contract.∈K? TM.calls ι) d e
      cut-at n callsV bA bB d (c-call ())
      cut-at n (emitsV refl) bA bB d (c-here σ ())
      cut-at n (emitsV refl) bA bB d (c-call ())
      cut-at n (haltsV refl) bA bB d ()

    no-cut : ∀ {s : Sig} {x : MV ⌜ sdom s ⌝} {t} {p : OpPath (opF s (toF (sdom s) (er x))) t (inj₂ Once.LinCore.Events.exhausted)}
           → CutOp Wι {s} {x} {t} p → s ∈ ops U → ⊥
    no-cut {sig (mk-info' n c bA bB)} {x = x} {p = p} cu m = cut-at n c bA bB (decl m) {x = x} {p = p} cu
