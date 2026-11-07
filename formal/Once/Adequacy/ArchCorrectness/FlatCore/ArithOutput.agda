-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.ArithOutput  (plan 0.123 α′ (f3c, f3d))
--
-- WHAT AN ARITH SIGOP'S STEP WRITES, arch-free. At a non-faulting step the
-- argument decoded (D392); a scalar one is the literal in `Input1` (D398), a
-- compound one the value behind its pointer. The Pure output is then the
-- block's meaning at that value (`block-output`), and the value's `Int` leaves
-- are words (`input-words`, from the store invariant, D397).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics; fs-numerics; fs-ffi)

module Once.Adequacy.ArchCorrectness.FlatCore.ArithOutput (FS : FrameSemantics) where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Once.Spec.Type using (Type; Int; Float; Base; ∅ₖ; b-var; b-Unit; b-Void; b-Int; b-Float; b-*; b-+)
open import Once.Type using (FitsInReg; fits-int; fits-float)
open import Once.CCC.Machine.SMCore
open AbstractExec {FS}
open LocState using (regs)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo; blockV; effect-of; semM-of)
open SigOpInfo using (sem; baseA; name)
open import Once.Arith.Type using (NInt; NFloat)
open import Once.Arith.Machine.IR using (MArithIR; shape-as-type)
open import Once.Arith.SigOp.BlockSem using (block-semM)
open import Once.SigOp.Words using (Words)
open import Once.CCC.Machine.FlatStoreWF FS using (StoreWF; module StoreWF; IMfs; WordsM; readTyped-words; sv-below)
open StoreWF using (wf-regs)

------------------------------------------------------------------------
-- The Pure output reads the argument that decoded.
------------------------------------------------------------------------
decode-out : ∀ {A B} (si : SigOpInfo A B) (ls : LocState FS) (fitB : FitsInReg B) (bt : Base ∅ₖ A)
             (sv : StoredValue FS) → readReg (regs ls) Input1 ≡ sv → ∀ {a}
           → decode-at bt sv ls ≡ just a
           → pure-sigop-out-aux si ls (just fitB) (sv-as-loc sv) ≡ pure-sigop-out-val si fitB (just a)
decode-out si ls fitB (b-var {i = ()} _)
decode-out si ls fitB b-Unit  (SV-Ptr loc)          e refl = refl
decode-out si ls fitB b-Unit  (SV-Tag t)            e refl = refl
decode-out si ls fitB b-Unit  (SV-Lit p v)          e refl = refl
decode-out si ls fitB b-Unit  (SV-Code c)           e refl = refl
decode-out si ls fitB b-Void  (SV-Ptr loc)          e ()
decode-out si ls fitB b-Void  (SV-Tag t)            e ()
decode-out si ls fitB b-Void  (SV-Lit p v)          e ()
decode-out si ls fitB b-Void  (SV-Code c)           e ()
decode-out si ls fitB b-Int   (SV-Lit fits-int v)   e refl rewrite e = refl
decode-out si ls fitB b-Int   (SV-Lit fits-float v) e ()
decode-out si ls fitB b-Int   (SV-Ptr loc)          e ()
decode-out si ls fitB b-Int   (SV-Tag t)            e ()
decode-out si ls fitB b-Int   (SV-Code c)           e ()
decode-out si ls fitB b-Float (SV-Lit fits-float v) e refl rewrite e = refl
decode-out si ls fitB b-Float (SV-Lit fits-int v)   e ()
decode-out si ls fitB b-Float (SV-Ptr loc)          e ()
decode-out si ls fitB b-Float (SV-Tag t)            e ()
decode-out si ls fitB b-Float (SV-Code c)           e ()
decode-out si ls fitB (b-* _ _) (SV-Ptr loc)        e d = cong (pure-sigop-out-val si fitB) d
decode-out si ls fitB (b-* _ _) (SV-Lit p v)        e ()
decode-out si ls fitB (b-* _ _) (SV-Tag t)          e ()
decode-out si ls fitB (b-* _ _) (SV-Code c)         e ()
decode-out si ls fitB (b-+ _ _) (SV-Ptr loc)        e d = cong (pure-sigop-out-val si fitB) d
decode-out si ls fitB (b-+ _ _) (SV-Lit p v)        e ()
decode-out si ls fitB (b-+ _ _) (SV-Tag t)          e ()
decode-out si ls fitB (b-+ _ _) (SV-Code c)         e ()

------------------------------------------------------------------------
-- An `Int` block's output is its meaning at the decoded argument.
------------------------------------------------------------------------
block-output : ∀ {sh} (si : SigOpInfo (shape-as-type sh) Int) (e : MArithIR sh NInt)
             → sem si ≡ blockV e refl refl → (ls : LocState FS) → ∀ {a}
             → decode-at (baseA si) (readReg (regs ls) Input1) ls ≡ just a
             → exec-sigop-output si ls ≡ SV-Lit fits-int (block-semM e (fs-numerics FS) a)
block-output {sh} si e eq ls {a} d =
  trans (cong (λ s′ → exec-sigop-output-of (effect-of s′) si ls) eq)
    (trans (decode-out si ls fits-int (baseA si) (readReg (regs ls) Input1) refl d)
           (cong (λ s′ → res-sv fits-int (semM-of (fs-ffi FS) (name si) s′ (fs-numerics FS) a)) eq))

-- …and a `Float` block's.
block-output-flt : ∀ {sh} (si : SigOpInfo (shape-as-type sh) Float) (e : MArithIR sh NFloat)
                 → sem si ≡ blockV e refl refl → (ls : LocState FS) → ∀ {a}
                 → decode-at (baseA si) (readReg (regs ls) Input1) ls ≡ just a
                 → exec-sigop-output si ls ≡ SV-Lit fits-float (block-semM e (fs-numerics FS) a)
block-output-flt {sh} si e eq ls {a} d =
  trans (cong (λ s′ → exec-sigop-output-of (effect-of s′) si ls) eq)
    (trans (decode-out si ls fits-float (baseA si) (readReg (regs ls) Input1) refl d)
           (cong (λ s′ → res-sv fits-float (semM-of (fs-ffi FS) (name si) s′ (fs-numerics FS) a)) eq))

------------------------------------------------------------------------
-- The decoded argument's `Int` leaves are words (the store invariant, D397).
------------------------------------------------------------------------
input-words : ∀ {n ls} → StoreWF n ls → ∀ {A} (bt : Base ∅ₖ A) (sv : StoredValue FS)
            → readReg (regs ls) Input1 ≡ sv → ∀ {a}
            → decode-at bt sv ls ≡ just a → Words IMfs A a
input-words wf (b-var {i = ()} _)
input-words wf b-Unit  sv                    e refl = _
input-words wf b-Void  (SV-Ptr loc)          e ()
input-words wf b-Void  (SV-Tag t)            e ()
input-words wf b-Void  (SV-Lit p v)          e ()
input-words wf b-Void  (SV-Code c)           e ()
input-words {n} wf b-Int (SV-Lit fits-int v) e refl = subst (sv-below n) e (wf-regs wf Input1)
input-words wf b-Int   (SV-Lit fits-float v) e ()
input-words wf b-Int   (SV-Ptr loc)          e ()
input-words wf b-Int   (SV-Tag t)            e ()
input-words wf b-Int   (SV-Code c)           e ()
input-words wf b-Float sv                    e d = _
input-words {ls = ls} wf (b-* {A} {B} _ _) (SV-Ptr loc) e d =
  subst (WordsM (A Once.Spec.Type.* B)) d (readTyped-words wf (A Once.Spec.Type.* B) loc)
  where import Once.Spec.Type
input-words wf (b-* _ _) (SV-Lit p v)        e ()
input-words wf (b-* _ _) (SV-Tag t)          e ()
input-words wf (b-* _ _) (SV-Code c)         e ()
input-words wf (b-+ _ _) (SV-Ptr loc)        e d = _
input-words wf (b-+ _ _) (SV-Lit p v)        e ()
input-words wf (b-+ _ _) (SV-Tag t)          e ()
input-words wf (b-+ _ _) (SV-Code c)         e ()
