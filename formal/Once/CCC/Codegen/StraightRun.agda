-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.StraightRun
--
-- plan 0.123 B.4 α: A STRAIGHT SEGMENT AS ONE CHAIN.
--
-- The flat layout's copies (`FlatLayout.put`/`get`, `FlatCopy.copy-from`)
-- have a length that depends on the type, so a clause can no longer name
-- its states row by row. What it can do is run a straight segment as a
-- whole: the segment's effect is `exec-trace`'s (where `FlatCopy.copy-run`
-- states it), and its chain is `straight-steps`, given only that the text
-- sits at the pc and that the run is still live at its end (a straight
-- instruction never un-halts, so live at the end is live throughout).
------------------------------------------------------------------------

module Once.CCC.Codegen.StraightRun where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Bool using (true; false)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace; module LocState; module AbstractExec)
open LocState using (halted)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)

module StraightRunAPI {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open AbstractExec {FS} using (exec-abstract; exec-trace; exec-trace-cons)

  -- the state a straight segment leaves: `exec-trace`'s data, the pc past it
  after : AbstractTrace → FlatState → FlatState
  after t fs = record fs { floc   = proj₁ (exec-trace t (floc fs) (falloc fs))
                         ; falloc = proj₂ (exec-trace t (floc fs) (falloc fs))
                         ; fpc    = length t + fpc fs }

  -- the text of `t` at `pc` in `prog`
  At : AbstractTrace → ℕ → AbstractTrace → Set
  At prog pc t = ∀ (k : ℕ) (i : AbstractInstr) → fetch t k ≡ just i → fetch prog (k + pc) ≡ just i

  -- a halted state stays where it is
  trace-halted : ∀ (t : AbstractTrace) s alloc → halted s ≡ true → exec-trace t s alloc ≡ (s , alloc)
  trace-halted []      s alloc _  = refl
  trace-halted (i ∷ t) s alloc ht rewrite ht = refl

  after-cons : ∀ (i : AbstractInstr) (t : AbstractTrace) (fs : FlatState)
             → halted (floc fs) ≡ false
             → after (i ∷ t) fs ≡ after t (flat-step-straight i fs)
  after-cons i t fs h =
    cong₂ (λ r p → record fs { floc = proj₁ r ; falloc = proj₂ r ; fpc = p })
          (exec-trace-cons i t (floc fs) (falloc fs) h)
          (sym (+-suc (length t) (fpc fs)))

  straight-steps : ∀ {prog} (t : AbstractTrace) (fs : FlatState)
    → All StraightStep t
    → At prog (fpc fs) t
    → halted (floc fs) ≡ false
    → halted (proj₁ (exec-trace t (floc fs) (falloc fs))) ≡ false
    → FlatSteps prog (length t) fs (after t fs)
  straight-steps []      fs []         sp h he = []
  straight-steps {prog} (i ∷ t) fs (st ∷ sts) sp h he =
    (h , sp 0 i refl)
    ∷ subst (λ x → FlatSteps prog (length t) x (after (i ∷ t) fs)) (sym (st prog fs))
        (subst (FlatSteps prog (length t) fs₁) (sym (after-cons i t fs h))
          (straight-steps t fs₁ sts sp′ h₁ he′))
    where
      fs₁ = flat-step-straight i fs
      he′ : halted (proj₁ (exec-trace t (floc fs₁) (falloc fs₁))) ≡ false
      he′ = subst (λ r → halted (proj₁ r) ≡ false) (exec-trace-cons i t (floc fs) (falloc fs) h) he
      h₁ : halted (floc fs₁) ≡ false
      h₁ with halted (floc fs₁) in eq
      ... | false = refl
      ... | true  = ⊥-elim (true≢false (trans (sym eq)
                      (trans (cong (λ r → halted (proj₁ r)) (sym (trace-halted t (floc fs₁) (falloc fs₁) eq))) he′)))
        where
          true≢false : ¬ (true ≡ false)
          true≢false ()
      sp′ : At prog (fpc fs₁) t
      sp′ k j f = subst (λ p → fetch prog p ≡ just j) (sym (+-suc k (fpc fs))) (sp (suc k) j f)
