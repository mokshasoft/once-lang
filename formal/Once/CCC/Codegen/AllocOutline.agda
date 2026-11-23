-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocOutline — the outlined program runs as the program
-- does (D480, plan 0.146 §5 item 8 c).
--
-- `AllocExpand.outline ks P` is `P` with its allocations and frees called, in
-- place, and their primitive routines right after the start, jumped over. Past
-- the start, a state of `P` and one of the outlined program are one state, the
-- latter's pcs shifted by the routines' length (`Flat.Shifted`). This module:
--
--   * relocation between ANY two programs whose lookups agree, up to the shift,
--     at the targets an instruction uses (`Agree`; Flat's `shifted-instr` is the
--     case of a program and its suffix, where every target agrees);
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocOutline {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
import Data.Maybe
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.CCC.Label using (LabelId; EntryId; e-thunk; e-fn)
open import Once.Spec.Name using (CanonicalName)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack)
open import Once.Memory.HeapAddress using (sucHL)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS}
open FlatState
open LocState

------------------------------------------------------------------------
-- Relocation between two programs, at the targets an instruction uses
------------------------------------------------------------------------

-- what an instruction looks up, agreeing up to `d` (`p` the shifted program)
Agree : ℕ → AbstractInstr → AbstractTrace → AbstractTrace → Set
Agree d (instr-ctrl (c-jmp m))             p p′ = find-label p m ≡ Data.Maybe.map (d +_) (find-label p′ m)
Agree d (instr-ctrl (c-branch-tag-zero m)) p p′ = find-label p m ≡ Data.Maybe.map (d +_) (find-label p′ m)
Agree d (instr-ctrl (c-call-fn f))         p p′ = find-fn p f ≡ Data.Maybe.map (d +_) (find-fn p′ f)
Agree d instr-call-closure                 p p′ = ∀ tg → find-thunk p tg ≡ Data.Maybe.map (d +_) (find-thunk p′ tg)
{-# CATCHALL #-}
Agree d _                                  p p′ = ⊤

shifted-call-codeᵍ : ∀ (d : ℕ) (mv : Maybe (StoredValue FS))
                      (p p′ : AbstractTrace) (fs fs' : FlatState)
                  → (∀ tg → find-thunk p tg ≡ Data.Maybe.map (d +_) (find-thunk p′ tg))
                  → Shifted d fs fs'
                  → Shifted d (do-call-code p mv fs) (do-call-code p′ mv fs')
shifted-call-codeᵍ d (just (SV-Code ℓ))  p p′ fs fs' ft sh =
  shifted-call-at d (find-thunk p ℓ) (find-thunk p′ ℓ) fs fs' sh (ft ℓ)
shifted-call-codeᵍ d (just (SV-Tag _))   p p′ fs fs' _ sh = shifted-fault d fs fs' sh
shifted-call-codeᵍ d (just (SV-Lit _ _)) p p′ fs fs' _ sh = shifted-fault d fs fs' sh
shifted-call-codeᵍ d (just (SV-Ptr _))   p p′ fs fs' _ sh = shifted-fault d fs fs' sh
shifted-call-codeᵍ d nothing             p p′ fs fs' _ sh = shifted-fault d fs fs' sh

shifted-call-svᵍ : ∀ (d : ℕ) (sv : StoredValue FS)
                    (p p′ : AbstractTrace) (fs fs' : FlatState)
                → (∀ tg → find-thunk p tg ≡ Data.Maybe.map (d +_) (find-thunk p′ tg))
                → Shifted d fs fs'
                → Shifted d (do-call-sv p sv fs) (do-call-sv p′ sv fs')
shifted-call-svᵍ d (SV-Ptr (AtDynamic hl)) p p′ fs fs' ft sh@(lo , _) =
  subst (λ mv → Shifted d (do-call-code p (heapMem (floc fs) (sucHL hl)) fs)
                          (do-call-code p′ mv fs'))
        (cong (λ L → heapMem L (sucHL hl)) lo)
        (shifted-call-codeᵍ d (heapMem (floc fs) (sucHL hl)) p p′ fs fs' ft sh)
shifted-call-svᵍ d (SV-Ptr (AtStack _ _)) p p′ fs fs' _ sh = shifted-fault d fs fs' sh
shifted-call-svᵍ d (SV-Tag _)             p p′ fs fs' _ sh = shifted-fault d fs fs' sh
shifted-call-svᵍ d (SV-Lit _ _)           p p′ fs fs' _ sh = shifted-fault d fs fs' sh
shifted-call-svᵍ d (SV-Code _)            p p′ fs fs' _ sh = shifted-fault d fs fs' sh

shifted-call-closureᵍ : ∀ (d : ℕ) (p p′ : AbstractTrace) (fs fs' : FlatState)
                     → (∀ tg → find-thunk p tg ≡ Data.Maybe.map (d +_) (find-thunk p′ tg))
                     → Shifted d fs fs'
                     → Shifted d (do-call p fs) (do-call p′ fs')
shifted-call-closureᵍ d p p′ fs fs' ft sh@(_ , _ , _ , _ , _ , cl) =
  subst (λ sv → Shifted d (do-call-sv p (fclosure fs) fs)
                          (do-call-sv p′ sv fs'))
        cl (shifted-call-svᵍ d (fclosure fs) p p′ fs fs' ft sh)

-- ★ one step of either program keeps them shifted, given what the step looks up
shifted-instrᵍ : ∀ (d : ℕ) (i : AbstractInstr) (p p′ : AbstractTrace) (fs fs' : FlatState)
               → Agree d i p p′
               → Shifted d fs fs'
               → Shifted d (flat-exec-instr i p fs) (flat-exec-instr i p′ fs')
shifted-instrᵍ d mov-to-output                          p p′ fs fs' _ sh = shifted-straight d mov-to-output fs fs' sh
shifted-instrᵍ d mov-to-input                           p p′ fs fs' _ sh = shifted-straight d mov-to-input fs fs' sh
shifted-instrᵍ d load-indirect                          p p′ fs fs' _ sh = shifted-straight d load-indirect fs fs' sh
shifted-instrᵍ d load-indirect-suc                      p p′ fs fs' _ sh = shifted-straight d load-indirect-suc fs fs' sh
shifted-instrᵍ d (load-from-slot k)                     p p′ fs fs' _ sh = shifted-straight d (load-from-slot k) fs fs' sh
shifted-instrᵍ d (store-at-slot k)                      p p′ fs fs' _ sh = shifted-straight d (store-at-slot k) fs fs' sh
shifted-instrᵍ d store-indirect                         p p′ fs fs' _ sh = shifted-straight d store-indirect fs fs' sh
shifted-instrᵍ d store-indirect-suc                     p p′ fs fs' _ sh = shifted-straight d store-indirect-suc fs fs' sh
shifted-instrᵍ d (lea-slot k)                           p p′ fs fs' _ sh = shifted-straight d (lea-slot k) fs fs' sh
shifted-instrᵍ d (restore-input k)                      p p′ fs fs' _ sh = shifted-straight d (restore-input k) fs fs' sh
shifted-instrᵍ d (instr-reclaim-to k)                   p p′ fs fs' _ sh = shifted-straight d (instr-reclaim-to k) fs fs' sh
shifted-instrᵍ d (worklist-init k)                      p p′ fs fs' _ sh = shifted-straight d (worklist-init k) fs fs' sh
shifted-instrᵍ d (worklist-push k)                      p p′ fs fs' _ sh = shifted-straight d (worklist-push k) fs fs' sh
shifted-instrᵍ d (worklist-pop k)                       p p′ fs fs' _ sh = shifted-straight d (worklist-pop k) fs fs' sh
shifted-instrᵍ d (worklist-check k)                     p p′ fs fs' _ sh = shifted-straight d (worklist-check k) fs fs' sh
shifted-instrᵍ d (instr-sigop k)                        p p′ fs fs' _ sh = shifted-straight d (instr-sigop k) fs fs' sh
shifted-instrᵍ d (instr-load-const k j)                 p p′ fs fs' _ sh = shifted-straight d (instr-load-const k j) fs fs' sh
shifted-instrᵍ d (instr-load-code-addr k)               p p′ fs fs' _ sh = shifted-straight d (instr-load-code-addr k) fs fs' sh
shifted-instrᵍ d instr-save-closure-reg                 p p′ fs fs' _ sh = shifted-save-closure d fs fs' sh
shifted-instrᵍ d (instr-load-tag-lit k)                 p p′ fs fs' _ sh = shifted-straight d (instr-load-tag-lit k) fs fs' sh
shifted-instrᵍ d (instr-alloc-heap k)                   p p′ fs fs' _ sh = shifted-straight d (instr-alloc-heap k) fs fs' sh
shifted-instrᵍ d (instr-reg-op out-nz)                  p p′ fs fs' _ sh@(lo , _) =
  subst (λ v → Shifted d (do-nz v fs) (do-nz (readReg (regs (floc fs')) Output) fs'))
        (sym (cong (λ L → readReg (regs L) Output) lo))
        (shifted-nz d (readReg (regs (floc fs')) Output) fs fs' sh)
shifted-instrᵍ d (instr-free-heap k)                    p p′ fs fs' _ sh = shifted-straight d (instr-free-heap k) fs fs' sh
shifted-instrᵍ d (instr-room k)                         p p′ fs fs' _ sh = shifted-straight d (instr-room k) fs fs' sh
shifted-instrᵍ d (load-at k)                         p p′ fs fs' _ sh = shifted-straight d (load-at k) fs fs' sh
shifted-instrᵍ d (store-at k)                         p p′ fs fs' _ sh = shifted-straight d (store-at k) fs fs' sh
shifted-instrᵍ d (addr-at k)                         p p′ fs fs' _ sh = shifted-straight d (addr-at k) fs fs' sh
shifted-instrᵍ d (load-rec k)                        p p′ fs fs' _ sh = shifted-straight d (load-rec k) fs fs' sh
shifted-instrᵍ d (store-rec k)                       p p′ fs fs' _ sh = shifted-straight d (store-rec k) fs fs' sh
shifted-instrᵍ d (instr-ctrl (c-label _))               p p′ fs fs' _ sh = shifted-label d fs fs' sh
shifted-instrᵍ d (instr-ctrl (c-entry _ b))             p p′ fs fs' _ sh = shifted-thunk d b fs fs' sh
shifted-instrᵍ d (instr-ctrl (c-start b))               p p′ fs fs' _ sh = shifted-thunk d b fs fs' sh
shifted-instrᵍ d (instr-ctrl c-leave)                   p p′ fs fs' _ sh = shifted-leave d fs fs' sh
shifted-instrᵍ d (instr-ctrl (c-call-fn f))             p p′ fs fs' a sh =
  shifted-call-at d (find-fn p f) (find-fn p′ f) fs fs' sh a
shifted-instrᵍ d (instr-ctrl (c-ret b))                 p p′ fs fs' _ sh = shifted-ret d b fs fs' sh
shifted-instrᵍ d (instr-ctrl (c-jmp t))                 p p′ fs fs' a sh =
  shifted-jump d (find-label p t) (find-label p′ t) fs fs' sh a
shifted-instrᵍ d (instr-ctrl (c-branch-tag-zero t))     p p′ fs fs' a sh@(lo , la , _) =
  shifted-test d t p p′ _ _ fs fs' sh
    (cong₂ (λ A L → tag-test (flat-read-tag A L)) la lo) a
shifted-instrᵍ d (instr-alloc-stack k)                  p p′ fs fs' _ sh = shifted-frame d (instr-alloc-stack k) (enter-frame k) fs fs' sh
shifted-instrᵍ d (instr-dealloc-stack k)                p p′ fs fs' _ sh = shifted-frame d (instr-dealloc-stack k) leave-frame fs fs' sh
shifted-instrᵍ d (instr-push-frame k)                   p p′ fs fs' _ sh = shifted-frame d (instr-push-frame k) (enter-frame (suc k)) fs fs' sh
shifted-instrᵍ d instr-pop-frame                        p p′ fs fs' _ sh = shifted-frame d instr-pop-frame leave-frame fs fs' sh
shifted-instrᵍ d instr-call-closure                     p p′ fs fs' a sh =
  shifted-call-closureᵍ d p p′ fs fs' a sh
