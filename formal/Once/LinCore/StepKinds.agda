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
open import Level using (Level)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.IR.Semantics.Trace using (FFIAnswers)
open import Once.LinCore.Flat using (Base)

module Once.LinCore.StepKinds
  (fmt : TargetNum) (ans : FFIAnswers)
  (bw : Base → ℕ)
  where

open import Once.LinCore.NbEPLinCore fmt ans
open import Once.LinCore.Events fmt ans bw
open import Once.LinCore.Machine fmt ans bw using (Sh; _∣_; Stk; _∷ˢ_; Slots; Cfg; _∥_; see)
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
-- a primitive: an op (D426: relative to the machine's world), or a local one
data PrimCov {Γ} : ∀ {A B} → LTm Γ A B → Set where
  pc-op  : ∀ {s : Sig} → PrimCov (lop s)
  pc-loc : ∀ {A B} {g : LTm Γ A B} → NotOp g → PrimCov g

CoveredI (loop _) = ⊤
CoveredI (prim _ g) = PrimCov g
CoveredI (call _) = ⊤
-- a dispatch through a one-shot cell's code word, and its trampoline's cell part (D421)
CoveredI icall    = ⊤
CoveredI open1    = ⊤
-- an observation's dispatch (at the empty table, D423) and its trampoline's cell part
CoveredI (iobs _) = ⊤
CoveredI nopen    = ⊤
-- a free's dispatch (a closure's, a ν's) and its trampoline's cell part (D417)
CoveredI cfree    = ⊤
CoveredI nfree    = ⊤
CoveredI fopen    = ⊤
-- a many-use dispatch and its trampoline's cell part (D425)
CoveredI icallω   = ⊤
CoveredI openω    = ⊤
-- a copy's dispatch (a closure's, a ν's) and its trampoline's cell part and fresh cell (D417)
CoveredI ccopy    = ⊤
CoveredI ncopy    = ⊤
CoveredI copen    = ⊤
CoveredI reclose  = ⊤
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
-- 3. ★ THE SPLITS ON A STEP, as eliminators. Their cases come as one
-- record: a split unifies a step's indices with the whole clause context,
-- and a record variable keeps that context small (the cases as 22 separate
-- arguments made one split 48 s, as one record ~6 s).
------------------------------------------------------------------------

module _ {ℓ : Level} {T : Sh} where

  -- what a split gives, by the step
  Motive : Set (Level.suc ℓ)
  Motive = ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m : Cfg sh} {n : ℕ} {t}
             {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ : Cfg sh′} {n′ : ℕ} → StepI c r m n t c′ r′ m′ n′ → Set ℓ

  -- a covered step, by its kind: a straight step, a `case` (a loop's
  -- dispatch too), a loop's turn, a body's end, a call, a return
  record CoveredCases : Set (Level.suc ℓ) where
    field
      P   : Motive
      loc : ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
            (st : StepI c r m n t c′ r′ m′ n′) → StraightC c → P st
      cs₁ : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {a : MV A} {os : Stk S} {n}
          → P (i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n})
      cs₂ : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {b : MV B} {os : Stk S} {n}
          → P (i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n})
      lp  : ∀ {E Es A B S U} {body : Codeᴵ (E ∷ Es ∣ A ∷ S) (E ∷ Es ∣ (B ⊕t A) ∷ S)} {k : Codeᴵ (E ∷ Es ∣ B ∷ S) U}
              {r : Ret U T} {m : Cfg (E ∷ Es ∣ A ∷ S)} {n}
          → P (i-loop {body = body} {k = k} {r = r} {m = m} {n = n})
      rti : ∀ {sh U} {k : Codeᴵ sh U} {r : Ret U T} {m : Cfg sh} {n}
          → P (i-reti {k = k} {r = r} {m = m} {n = n})
      cl  : ∀ {σ Es S U} {κ : Key σ} {k : Codeᴵ (top σ ⊳ Es ∣ cod σ ∷ S) U} {r : Ret U T}
              {es : Slots (top σ ⊳ Es)} {a : MV (dom σ)} {os : Stk S} {n}
          → P (i-call {κ = κ} {k = k} {r = r} {es = es} {a = a} {os = os} {n = n})
      rt  : ∀ {t Es B S U} {k : Codeᴵ (t ⊳ Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots (t ⊳ Es)} {os : Stk S}
              {e′ : Slots (t ⊳ [])} {b : MV B} {n}
          → P (i-ret {k = k} {r = r} {es = es} {os = os} {e′ = e′} {b = b} {n = n})
      ic  : ∀ {Es g X A B S U} {k : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {i} {lam : Lam once g X A B}
              {x : MV X} {a : MV A} {os : Stk S} {n}
          → P (i-icall {k = k} {r = r} {es = es} {i = i} {lam = lam} {x = x} {a = a} {os = os} {n = n})
      op1 : ∀ {Es g X A B S U} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) U} {r : Ret U T} {es : Slots Es} {i} {lam : Lam once g X A B}
              {x : MV X} {a : MV A} {os : Stk S} {n}
          → P (i-open1 {k = k} {r = r} {es = es} {i = i} {lam = lam} {x = x} {a = a} {os = os} {n = n})
      nop : ∀ {Es F S S′ U} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) U} {r : Ret U T} {es : Slots Es} {i}
              {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
          → P (i-nopen {k = k} {r = r} {es = es} {i = i} {p = p} {os = os} {n = n})
      iob : ∀ {Γ} {ds : Defs Γ} {Es F S S′ U} {k : Codeᴵ (Es ∣ LF∙ F (Nu F) ∷ S′) U} {r : Ret U T} {es : Slots Es} {i}
              {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
          → P (i-iobs {ds = ds} {k = k} {r = r} {es = es} {i = i} {p = p} {os = os} {n = n})
      cf  : ∀ {Es kd g X A B S U} {c : Codeᴵ (Es ∣ One ∷ S) U} {r : Ret U T} {es : Slots Es} {i} {lam : Lam kd g X A B}
              {x : MV X} {os : Stk S} {n}
          → P (i-cfree {c = c} {r = r} {es = es} {i = i} {lam = lam} {x = x} {os = os} {n = n})
      nf  : ∀ {Es F S S′ U} {c : Codeᴵ (Es ∣ One ∷ S′) U} {r : Ret U T} {es : Slots Es} {i}
              {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
          → P (i-nfree {c = c} {r = r} {es = es} {i = i} {p = p} {os = os} {n = n})
      fo  : ∀ {Es kd g X A B S U} {k : Codeᴵ (Es ∣ X ∷ S) U} {r : Ret U T} {es : Slots Es} {i} {lam : Lam kd g X A B}
              {x : MV X} {os : Stk S} {n}
          → P (i-fopen {k = k} {r = r} {es = es} {i = i} {lam = lam} {x = x} {os = os} {n = n})
      foν : ∀ {Es F S S′ U} {k : Codeᴵ (Es ∣ (Coalg F S ⊗t S) ∷ S′) U} {r : Ret U T} {es : Slots Es} {i}
              {p : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
          → P (i-fopenν {k = k} {r = r} {es = es} {i = i} {p = p} {os = os} {n = n})
      icω : ∀ {Es g X A B S U} {k : Codeᴵ (Fn many g A B ∷ Es ∣ B ∷ S) U} {r : Ret U T}
              {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {a : MV A} {os : Stk S} {n}
              (eq : see es ≡ mfn i lam x)
          → P (i-icallω {k = k} {r = r} {lam = lam} {i = i} {x = x} {es = es} {a = a} {os = os} {n = n} eq)
      opω : ∀ {Es g X A B S U} {k : Codeᴵ (X ∷ Fn many g A B ∷ Es ∣ S) U} {r : Ret U T}
              {lam : Lam many g X A B} {i x} {es : Slots (Fn many g A B ∷ Es)} {os : Stk S} {n}
              (eq : see es ≡ mfn i lam x)
          → P (i-openω {k = k} {r = r} {lam = lam} {i = i} {x = x} {es = es} {os = os} {n = n} eq)
      cc  : ∀ {Es kd g X A B S U} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) U} {r : Ret U T}
              {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} {n}
              (eq : see es ≡ mfn i lam x)
          → P (i-ccopy {k = k} {r = r} {lam = lam} {i = i} {x = x} {es = es} {os = os} {n = n} eq)
      nc  : ∀ {Es F S S′ U} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S′) U} {r : Ret U T} {i} {p : MV (Coalg F S ⊗t S)}
              {es : Slots (Nu F ∷ Es)} {os : Stk S′} {n}
              (eq : see es ≡ mnu i p)
          → P (i-ncopy {k = k} {r = r} {i = i} {p = p} {es = es} {os = os} {n = n} eq)
      co  : ∀ {Es kd g X A B S U} {k : Codeᴵ (X ∷ Fn kd g A B ∷ Es ∣ S) U} {r : Ret U T}
              {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {os : Stk S} {n}
              (eq : see es ≡ mfn i lam x)
          → P (i-copen {k = k} {r = r} {lam = lam} {i = i} {x = x} {es = es} {os = os} {n = n} eq)
      coν : ∀ {Es F S S′ U} {k : Codeᴵ ((Coalg F S ⊗t S) ∷ Nu F ∷ Es ∣ S′) U} {r : Ret U T}
              {i} {p : MV (Coalg F S ⊗t S)} {es : Slots (Nu F ∷ Es)} {os : Stk S′} {n}
              (eq : see es ≡ mnu i p)
          → P (i-copenν {k = k} {r = r} {i = i} {p = p} {es = es} {os = os} {n = n} eq)
      rc  : ∀ {Es kd g X A B S U} {k : Codeᴵ (Fn kd g A B ∷ Es ∣ Fn kd g A B ∷ S) U} {r : Ret U T}
              {lam : Lam kd g X A B} {i x} {es : Slots (Fn kd g A B ∷ Es)} {x′ : MV X} {os : Stk S} {n}
              (eq : see es ≡ mfn i lam x)
          → P (i-reclose {k = k} {r = r} {lam = lam} {i = i} {x = x} {es = es} {x′ = x′} {os = os} {n = n} eq)
      rcν : ∀ {Es F S S′ U} {k : Codeᴵ (Nu F ∷ Es ∣ Nu F ∷ S′) U} {r : Ret U T}
              {i} {p : MV (Coalg F S ⊗t S)} {es : Slots (Nu F ∷ Es)} {p′ : MV (Coalg F S ⊗t S)} {os : Stk S′} {n}
              (eq : see es ≡ mnu i p)
          → P (i-recloseν {k = k} {r = r} {i = i} {p = p} {es = es} {p′ = p′} {os = os} {n = n} eq)
      op  : ∀ {Γ} {ds : Defs Γ} {Es} {s : Sig} {S U} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) U} {r : Ret U T} {es : Slots Es}
              {x : MV ⌜ sdom s ⌝} {w : MV ⌜ scod s ⌝} {os : Stk S} {n n′ t}
              (run : Run ds (lop s) mone x n (gives w n′) t)
          → P (i-prim {ds = ds} {g = lop s} {k = k} {r = r} {es = es} {v = x} {w = w} {os = os} {n = n} {n′ = n′} run)
      ope : ∀ {Γ} {ds : Defs Γ} {Es} {s : Sig} {S U} {k : Codeᴵ (Es ∣ ⌜ scod s ⌝ ∷ S) U} {r : Ret U T} {es : Slots Es}
              {x : MV ⌜ sdom s ⌝} {os : Stk S} {n t w}
              (p : OpPath (opF s (toF (sdom s) (er x))) t (inj₂ w))
          → P (i-opend {ds = ds} {s = s} {k = k} {r = r} {es = es} {x = x} {os = os} {n = n} p)

  covered-elim : (C : CoveredCases) → ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
                 (st : StepI c r m n t c′ r′ m′ n′) → CoveredC c → CoveredCases.P C st
  covered-elim C i-loop          _ = CoveredCases.lp C
  covered-elim C i-reti          _ = CoveredCases.rti C
  covered-elim C i-call          _ = CoveredCases.cl C
  covered-elim C i-ret           _ = CoveredCases.rt C
  covered-elim C i-case₁         _ = CoveredCases.cs₁ C
  covered-elim C i-case₂         _ = CoveredCases.cs₂ C
  covered-elim C st@i-unpair      v = CoveredCases.loc C st v
  covered-elim C st@i-pair        v = CoveredCases.loc C st v
  covered-elim C st@i-swap        v = CoveredCases.loc C st v
  covered-elim C st@i-unit        v = CoveredCases.loc C st v
  covered-elim C st@(i-prim _)    (pc-loc v) = CoveredCases.loc C st v
  covered-elim C (i-prim run)     pc-op      = CoveredCases.op C run
  covered-elim C st@i-untag       v = CoveredCases.loc C st v
  covered-elim C st@i-untag₁      v = CoveredCases.loc C st v
  covered-elim C st@i-tag₁        v = CoveredCases.loc C st v
  covered-elim C st@i-elend       v = CoveredCases.loc C st v
  covered-elim C st@i-eunlend     v = CoveredCases.loc C st v
  covered-elim C st@i-elift       v = CoveredCases.loc C st v
  covered-elim C st@(i-efst _)    v = CoveredCases.loc C st v
  covered-elim C st@(i-esnd _)    v = CoveredCases.loc C st v
  covered-elim C st@(i-eout _)    v = CoveredCases.loc C st v
  covered-elim C st@(i-eoutq _)   v = CoveredCases.loc C st v
  covered-elim C st@(i-ecase₁ _)  v = CoveredCases.loc C st v
  covered-elim C st@(i-ecase₂ _)  v = CoveredCases.loc C st v
  covered-elim C st@(i-eapp _)    v = CoveredCases.loc C st v
  covered-elim C st@i-epop        v = CoveredCases.loc C st v
  covered-elim C st@(i-eword _)   v = CoveredCases.loc C st v
  covered-elim C (i-opend p)      pc-op      = CoveredCases.ope C p
  covered-elim C (i-opend _)      (pc-loc ())
  covered-elim C i-icall          _ = CoveredCases.ic C
  covered-elim C (i-icallω {es = es} eq) _ = CoveredCases.icω C {es = es} eq
  covered-elim C i-iobs           _ = CoveredCases.iob C
  covered-elim C (i-ccopy {es = es} eq)  _ = CoveredCases.cc C {es = es} eq
  covered-elim C (i-ncopy {es = es} eq)  _ = CoveredCases.nc C {es = es} eq
  covered-elim C i-cfree          _ = CoveredCases.cf C
  covered-elim C i-nfree          _ = CoveredCases.nf C
  covered-elim C i-open1          _ = CoveredCases.op1 C
  covered-elim C (i-openω {es = es} eq)  _ = CoveredCases.opω C {es = es} eq
  covered-elim C i-nopen          _ = CoveredCases.nop C
  covered-elim C (i-copen {es = es} eq)  _ = CoveredCases.co C {es = es} eq
  covered-elim C (i-copenν {es = es} eq) _ = CoveredCases.coν C {es = es} eq
  covered-elim C (i-reclose {es = es} eq) _ = CoveredCases.rc C {es = es} eq
  covered-elim C (i-recloseν {es = es} eq) _ = CoveredCases.rcν C {es = es} eq
  covered-elim C i-fopen          _ = CoveredCases.fo C
  covered-elim C i-fopenν         _ = CoveredCases.foν C

  -- a local step, by its constructor
  record LocalCases : Set (Level.suc ℓ) where
    field
      P       : Motive
      unpair′ : ∀ {Es A B S U} {k : Codeᴵ (Es ∣ A ∷ B ∷ S) U} {r : Ret U T} {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {n}
              → P (i-unpair {k = k} {r = r} {es = es} {a = a} {b = b} {os = os} {n = n})
      pair′ : ∀ {Es A B S U} {k : Codeᴵ (Es ∣ (A ⊗t B) ∷ S) U} {r : Ret U T} {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {n}
            → P (i-pair {k = k} {r = r} {es = es} {a = a} {b = b} {os = os} {n = n})
      swap′ : ∀ {Es A B S U} {k : Codeᴵ (Es ∣ B ∷ A ∷ S) U} {r : Ret U T} {es : Slots Es} {a : MV A} {b : MV B} {os : Stk S} {n}
            → P (i-swap {k = k} {r = r} {es = es} {a = a} {b = b} {os = os} {n = n})
      unit′ : ∀ {Es S U} {k : Codeᴵ (Es ∣ One ∷ S) U} {r : Ret U T} {es : Slots Es} {os : Stk S} {n}
            → P (i-unit {k = k} {r = r} {es = es} {os = os} {n = n})
      prim′ : ∀ {Γ} {ds : Defs Γ} {Es A B S U} {g : LTm Γ A B} {k : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es}
                {v : MV A} {w : MV B} {os : Stk S} {n n′ t} (run : Run ds g mone v n (gives w n′) t) → NotOp g
            → P (i-prim {k = k} {r = r} {es = es} {os = os} run)
      untag′ : ∀ {Es l X A S U} {k : Codeᴵ (Es ∣ (X ⊗t A) ∷ S) U} {r : Ret U T} {es : Slots Es} {x : MV X} {a : MV A} {os : Stk S} {n}
             → P (i-untag {l = l} {k = k} {r = r} {es = es} {x = x} {a = a} {os = os} {n = n})
      untag₁′ : ∀ {Es l X S U} {k : Codeᴵ (Es ∣ X ∷ S) U} {r : Ret U T} {es : Slots Es} {x : MV X} {os : Stk S} {n}
              → P (i-untag₁ {l = l} {k = k} {r = r} {es = es} {x = x} {os = os} {n = n})
      tag₁′ : ∀ {Es l X S U} {k : Codeᴵ (Es ∣ Ct l X ∷ S) U} {r : Ret U T} {es : Slots Es} {x : MV X} {os : Stk S} {n}
            → P (i-tag₁ {k = k} {r = r} {es = es} {x = x} {os = os} {n = n})
      case₁′ : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {a : MV A} {os : Stk S} {n}
             → P (i-case₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {a = a} {os = os} {n = n})
      case₂′ : ∀ {Es A B S U} {c₁ : Codeᴵ (Es ∣ A ∷ S) U} {c₂ : Codeᴵ (Es ∣ B ∷ S) U} {r : Ret U T} {es : Slots Es} {b : MV B} {os : Stk S} {n}
             → P (i-case₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {b = b} {os = os} {n = n})
      elend′ : ∀ {E Es X A S U} {k : Codeᴵ ((E ⊗t X) ∷ E ∷ Es ∣ A ∷ S) U} {r : Ret U T} {es : Slots (E ∷ Es)} {x : MV X} {a : MV A} {os : Stk S} {n}
             → P (i-elend {k = k} {r = r} {es = es} {x = x} {a = a} {os = os} {n = n})
      eunlend′ : ∀ {E Es X B S U} {k : Codeᴵ (E ∷ Es ∣ (X ⊗t B) ∷ S) U} {r : Ret U T} {e : MV E} {es : Slots (E ∷ Es)}
                   {x : MV X} {w : MV B} {os : Stk S} {n}
               → P (i-eunlend {k = k} {r = r} {e = e} {es = es} {x = x} {w = w} {os = os} {n = n})
      elift′ : ∀ {Es S U} {k : Codeᴵ (One ∷ Es ∣ S) U} {r : Ret U T} {es : Slots Es} {os : Stk S} {n}
             → P (i-elift {k = k} {r = r} {es = es} {os = os} {n = n})
      efst′ : ∀ {E₁ E₂ Es S U} {k : Codeᴵ (E₁ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) U} {r : Ret U T} {e₁ : MV E₁} {e₂ : MV E₂}
                {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S} {n} (eq : see es ≡ mpair e₁ e₂)
            → P (i-efst {k = k} {r = r} {es = es} {os = os} {n = n} eq)
      esnd′ : ∀ {E₁ E₂ Es S U} {k : Codeᴵ (E₂ ∷ (E₁ ⊗t E₂) ∷ Es ∣ S) U} {r : Ret U T} {e₁ : MV E₁} {e₂ : MV E₂}
                {es : Slots ((E₁ ⊗t E₂) ∷ Es)} {os : Stk S} {n} (eq : see es ≡ mpair e₁ e₂)
            → P (i-esnd {k = k} {r = r} {es = es} {os = os} {n = n} eq)
      eout′ : ∀ {F Es S U} {k : Codeᴵ (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) U} {r : Ret U T} {i v} {es : Slots (μt F ∷ Es)} {os : Stk S} {n}
                (eq : see es ≡ mmu i v)
            → P (i-eout {k = k} {r = r} {es = es} {os = os} {n = n} eq)
      eoutq′ : ∀ {F Es S U} {k : Codeᴵ (LF∙ F (μt F) ∷ μt F ∷ Es ∣ S) U} {r : Ret U T} {i v} {es : Slots (μt F ∷ Es)} {os : Stk S} {n}
                 (eq : see es ≡ mmu i v)
             → P (i-eoutq {k = k} {r = r} {es = es} {os = os} {n = n} eq)
      ecase₁′ : ∀ {E₁ E₂ Es S U} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U}
                  {r : Ret U T} {e : MV E₁} {es : Slots ((E₁ ⊕t E₂) ∷ Es)} {os : Stk S} {n} (eq : see es ≡ minl e)
              → P (i-ecase₁ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {os = os} {n = n} eq)
      ecase₂′ : ∀ {E₁ E₂ Es S U} {c₁ : Codeᴵ (E₁ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U} {c₂ : Codeᴵ (E₂ ∷ (E₁ ⊕t E₂) ∷ Es ∣ S) U}
                  {r : Ret U T} {e : MV E₂} {es : Slots ((E₁ ⊕t E₂) ∷ Es)} {os : Stk S} {n} (eq : see es ≡ minr e)
              → P (i-ecase₂ {c₁ = c₁} {c₂ = c₂} {r = r} {es = es} {os = os} {n = n} eq)
      eapp′ : ∀ {l X Es S U} {k : Codeᴵ (X ∷ Ct l X ∷ Es ∣ S) U} {r : Ret U T} {x : MV X} {es : Slots (Ct l X ∷ Es)} {os : Stk S} {n}
                (eq : see es ≡ mct x)
            → P (i-eapp {k = k} {r = r} {es = es} {os = os} {n = n} eq)
      epop′ : ∀ {E Es S U} {k : Codeᴵ (Es ∣ S) U} {r : Ret U T} {e : MV E} {es : Slots Es} {os : Stk S} {n}
            → P (i-epop {k = k} {r = r} {e = e} {es = es} {os = os} {n = n})
      eword′ : ∀ {b Es S U} {k : Codeᴵ (Bt b ∷ Es ∣ Bt b ∷ S) U} {r : Ret U T} {x} {es : Slots (Bt b ∷ Es)} {os : Stk S} {n}
                 (eq : see es ≡ mbase x)
             → P (i-eword {k = k} {r = r} {es = es} {os = os} {n = n} eq)

  local-elim : (C : LocalCases) → ∀ {sh U sh′ U′} {c : Codeᴵ sh U} {r : Ret U T} {m n t} {c′ : Codeᴵ sh′ U′} {r′ : Ret U′ T} {m′ n′}
               (st : StepI c r m n t c′ r′ m′ n′) → LocalC c → LocalCases.P C st
  local-elim C i-unpair                  _ = LocalCases.unpair′ C
  local-elim C i-pair                    _ = LocalCases.pair′ C
  local-elim C i-swap                    _ = LocalCases.swap′ C
  local-elim C i-unit                    _ = LocalCases.unit′ C
  local-elim C (i-prim run)              l = LocalCases.prim′ C run l
  local-elim C i-untag                   _ = LocalCases.untag′ C
  local-elim C i-untag₁                  _ = LocalCases.untag₁′ C
  local-elim C i-tag₁                    _ = LocalCases.tag₁′ C
  local-elim C i-case₁                   _ = LocalCases.case₁′ C
  local-elim C i-case₂                   _ = LocalCases.case₂′ C
  local-elim C i-elend                   _ = LocalCases.elend′ C
  local-elim C i-eunlend                 _ = LocalCases.eunlend′ C
  local-elim C i-elift                   _ = LocalCases.elift′ C
  local-elim C (i-efst {es = es} eq)     _ = LocalCases.efst′ C {es = es} eq
  local-elim C (i-esnd {es = es} eq)     _ = LocalCases.esnd′ C {es = es} eq
  local-elim C (i-eout {es = es} eq)     _ = LocalCases.eout′ C {es = es} eq
  local-elim C (i-eoutq {es = es} eq)    _ = LocalCases.eoutq′ C {es = es} eq
  local-elim C (i-ecase₁ {es = es} eq)   _ = LocalCases.ecase₁′ C {es = es} eq
  local-elim C (i-ecase₂ {es = es} eq)   _ = LocalCases.ecase₂′ C {es = es} eq
  local-elim C (i-eapp {es = es} eq)     _ = LocalCases.eapp′ C {es = es} eq
  local-elim C i-epop                    _ = LocalCases.epop′ C
  local-elim C (i-eword {es = es} eq)    _ = LocalCases.eword′ C {es = es} eq
  local-elim C (i-opend _)    ()
  local-elim C i-loop         ()
  local-elim C i-call         ()
  local-elim C i-ret          ()
  local-elim C i-reti         ()
  local-elim C i-icall        ()
  local-elim C (i-icallω _)   ()
  local-elim C i-iobs         ()
  local-elim C (i-ccopy _)    ()
  local-elim C (i-ncopy _)    ()
  local-elim C i-cfree        ()
  local-elim C i-nfree        ()
  local-elim C i-open1        ()
  local-elim C (i-openω _)    ()
  local-elim C i-nopen        ()
  local-elim C (i-copen _)    ()
  local-elim C (i-copenν _)   ()
  local-elim C (i-reclose _)  ()
  local-elim C (i-recloseν _) ()
  local-elim C i-fopen        ()
  local-elim C i-fopenν       ()

