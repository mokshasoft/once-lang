-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.StepKinds — plan 0.146 B1.4b: AN IMAGE STEP BY ITS KIND.
--
-- A step's kind is its code's head (`LocalC`, `CoveredC`: decided on the
-- code, never by a case split on the step). The one case split on a step
-- (`covered-elim`) lives here, in a module with a small signature: a split
-- of `StepI` unifies its thirteen indices for each of its constructors, and
-- costs tens of seconds in a large module. Its users give their cases as
-- functions (no index unification at the use).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.StepKinds
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; _∷ˢ_; Slots; Cfg; _∥_)
open import Once.LinCore.Image fmt ans bw
open import Once.LinCore.ImageRun fmt ans bw

------------------------------------------------------------------------
-- 1. WHICH STEPS ARE LOCAL: they stay in their root's code.
------------------------------------------------------------------------

-- a primitive other than a SigOp (whose lemma is owed)
NotOp : ∀ {Γ A B} → LTm Γ A B → Set
NotOp (lop s) = ⊥
{-# CATCHALL #-}
NotOp _       = ⊤

-- by the code: its first instruction
LocalI : ∀ {sh sh′} → Insᴵ sh sh′ → Set
LocalI unpair       = ⊤
LocalI pair         = ⊤
LocalI swap         = ⊤
LocalI unit         = ⊤
LocalI (prim ds g)  = NotOp g
LocalI untag        = ⊤
LocalI untag₁       = ⊤
LocalI tag₁         = ⊤
LocalI elend        = ⊤
LocalI eunlend      = ⊤
LocalI elift        = ⊤
LocalI efst         = ⊤
LocalI esnd         = ⊤
LocalI eout         = ⊤
LocalI eoutq        = ⊤
LocalI eapp         = ⊤
LocalI epop         = ⊤
LocalI eword        = ⊤
{-# CATCHALL #-}
LocalI _            = ⊥

LocalC : ∀ {sh U} → Codeᴵ sh U → Set
LocalC (i ⨾ k)       = LocalI i
LocalC (case _ _)    = ⊤
LocalC (ecase _ _)   = ⊤
LocalC end           = ⊥
LocalC halted        = ⊥

Local : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
      → StepI c r m n t c′ r′ m′ n′ → Set
Local {c = c} _ = LocalC c

-- local, and not a `case` (whose branches are also a loop's dispatch)
StraightC : ∀ {sh U} → Codeᴵ sh U → Set
StraightC (i ⨾ k)     = LocalI i
StraightC (case _ _)  = ⊥
StraightC (ecase _ _) = ⊤
StraightC end         = ⊥
StraightC halted      = ⊥

straight-local : ∀ {sh U} (c : Codeᴵ sh U) → StraightC c → LocalC c
straight-local (i ⨾ k)     l = l
straight-local (ecase _ _) l = l

------------------------------------------------------------------------
-- 2. WHICH STEPS THE WORD LAYER COVERS: the local ones, a loop's turn, a
-- body's end, a call, a return.
------------------------------------------------------------------------

CoveredI : ∀ {sh sh′} → Insᴵ sh sh′ → Set
CoveredI (loop _) = ⊤
CoveredI (call _) = ⊤
{-# CATCHALL #-}
CoveredI i = LocalI i

CoveredC : ∀ {sh U} → Codeᴵ sh U → Set
CoveredC (i ⨾ k)     = CoveredI i
CoveredC (case _ _)  = ⊤
CoveredC (ecase _ _) = ⊤
CoveredC end         = ⊤
CoveredC halted      = ⊥

Covered : ∀ {T sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
        → StepI c r m n t c′ r′ m′ n′ → Set
Covered {c = c} _ = CoveredC c

------------------------------------------------------------------------
-- 3. ★ A COVERED STEP, BY ITS KIND (the one split on a step).
------------------------------------------------------------------------

module _ {T : Sh}
         (P : ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m : Cfg sh} {n : ℕ} {t}
                {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ : Cfg sh′} {n′ : ℕ} → StepI c r m n t c′ r′ m′ n′ → Set) where

  covered-elim :
      (loc : ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
             (st : StepI c r m n t c′ r′ m′ n′) → StraightC c → P st)
    → (cs₁ : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {a : MV A} {os : Stk S} {n}
             → P (i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n}))
    → (cs₂ : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {b : MV B} {os : Stk S} {n}
             → P (i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n}))
    → (lp  : ∀ {E Es A B S U} {body : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) U}
               {r : Ret U T} {m : Cfg (E ∷ Es ∣ A ∷ S)} {n}
             → P (i-loop {body = body} {k = k} {r = r} {m = m} {n = n}))
    → (rti : ∀ {sh U} {k : Codeᴵ sh U} {r : Ret U T} {m : Cfg sh} {n}
             → P (i-reti {k = k} {r = r} {m = m} {n = n}))
    → (cl  : ∀ {σ Es S U} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T}
               {es : Slots (top σ ⊳ Es)} {a : MV (dom σ)} {os : Stk S} {n}
             → P (i-call {κ = κ} {k = k} {r = r} {es = es} {a = a} {os = os} {n = n}))
    → (rt  : ∀ {t Es B S U} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots (t ⊳ Es)} {os : Stk S}
               {e′ : Slots (t ⊳ [])} {b : MV B} {n}
             → P (i-ret {k = k} {r = r} {es = es} {os = os} {e′ = e′} {b = b} {n = n}))
    → ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
      (st : StepI c r m n t c′ r′ m′ n′) → CoveredC c → P st
  covered-elim loc cs₁ cs₂ lp rti cl rt i-loop          _ = lp
  covered-elim loc cs₁ cs₂ lp rti cl rt i-reti          _ = rti
  covered-elim loc cs₁ cs₂ lp rti cl rt i-call          _ = cl
  covered-elim loc cs₁ cs₂ lp rti cl rt i-ret           _ = rt
  covered-elim loc cs₁ cs₂ lp rti cl rt i-case₁         _ = cs₁
  covered-elim loc cs₁ cs₂ lp rti cl rt i-case₂         _ = cs₂
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-unpair      v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-pair        v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-swap        v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-unit        v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-prim _)    v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-untag       v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-untag₁      v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-tag₁        v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-elend       v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-eunlend     v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-elift       v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-efst _)    v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-esnd _)    v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-eout _)    v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-eoutq _)   v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-ecase₁ _)  v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-ecase₂ _)  v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-eapp _)    v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@i-epop        v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt st@(i-eword _)   v = loc st v
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-opend _)      ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-icall          ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-icallω _)     ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-iobs           ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-ccopy _)      ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-ncopy _)      ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-cfree          ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-nfree          ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-open1          ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-openω _)      ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-nopen          ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-copen _)      ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-copenν _)     ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-reclose _)    ()
  covered-elim loc cs₁ cs₂ lp rti cl rt (i-recloseν _)   ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-fopen          ()
  covered-elim loc cs₁ cs₂ lp rti cl rt i-fopenν         ()
