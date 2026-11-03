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
open import Data.List using (List; []; _∷_; _++_; length)
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
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)

module StraightRunAPI {FS : FrameSemantics} where
  open FlatMachine {FS}
  open FlatStepsAPI {FS}
  open AbstractExec {FS} using (exec-abstract; exec-trace; exec-trace-cons)
  open FlatEventTrace {FS} using (chain-events; event-of; chain-events-subst-start; chain-events-subst)

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


  -- the step's three facts, named so that a lemma about the chain can name them
  sp-next : ∀ {prog} (i : AbstractInstr) (t : AbstractTrace) (fs : FlatState)
          → At prog (fpc fs) (i ∷ t) → At prog (fpc (flat-step-straight i fs)) t
  sp-next {prog} i t fs sp k j f = subst (λ p → fetch prog p ≡ just j) (sym (+-suc k (fpc fs))) (sp (suc k) j f)

  he-next : ∀ (i : AbstractInstr) (t : AbstractTrace) (fs : FlatState) → halted (floc fs) ≡ false
          → halted (proj₁ (exec-trace (i ∷ t) (floc fs) (falloc fs))) ≡ false
          → halted (proj₁ (exec-trace t (floc (flat-step-straight i fs)) (falloc (flat-step-straight i fs)))) ≡ false
  he-next i t fs h he = subst (λ r → halted (proj₁ r) ≡ false) (exec-trace-cons i t (floc fs) (falloc fs) h) he

  h-next : ∀ (i : AbstractInstr) (t : AbstractTrace) (fs : FlatState)
         → halted (proj₁ (exec-trace t (floc (flat-step-straight i fs)) (falloc (flat-step-straight i fs)))) ≡ false
         → halted (floc (flat-step-straight i fs)) ≡ false
  h-next i t fs he′ with halted (floc (flat-step-straight i fs)) in eq
  ... | false = refl
  ... | true  = ⊥-elim (true≢false (trans (sym eq)
                  (trans (cong (λ r → halted (proj₁ r)) (sym (trace-halted t _ _ eq))) he′)))
    where
      true≢false : ¬ (true ≡ false)
      true≢false ()

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
        (subst (FlatSteps prog (length t) (flat-step-straight i fs)) (sym (after-cons i t fs h))
          (straight-steps {prog = prog} t (flat-step-straight i fs) sts (sp-next {prog} i t fs sp)
             (h-next i t fs (he-next i t fs h he)) (he-next i t fs h he)))

  -- …and it emits nothing when none of its instructions does
  straight-silent : ∀ {prog} (t : AbstractTrace) (fs : FlatState)
    (sts : All StraightStep t) (sp : At prog (fpc fs) t)
    (h : halted (floc fs) ≡ false) (he : halted (proj₁ (exec-trace t (floc fs) (falloc fs))) ≡ false)
    → All (λ i → ∀ fs′ → event-of i fs′ ≡ []) t
    → chain-events (straight-steps {prog} t fs sts sp h he) ≡ []
  straight-silent []      fs []         sp h he []         = refl
  straight-silent {prog} (i ∷ t) fs (st ∷ sts) sp h he (ev ∷ evs) =
    trans (cong (_++ chain-events X′) (ev fs))
      (trans (chain-events-subst-start {prog = prog} (sym (st prog fs)) X)
        (trans (chain-events-subst {prog = prog} (sym (after-cons i t fs h)) Y)
               (straight-silent {prog = prog} t (flat-step-straight i fs) sts (sp-next {prog} i t fs sp)
                  (h-next i t fs (he-next i t fs h he)) (he-next i t fs h he) evs)))
    where
      Y = straight-steps {prog = prog} t (flat-step-straight i fs) sts (sp-next {prog} i t fs sp)
             (h-next i t fs (he-next i t fs h he)) (he-next i t fs h he)
      X = subst (FlatSteps prog (length t) (flat-step-straight i fs)) (sym (after-cons i t fs h)) Y
      X′ = subst (λ x → FlatSteps prog (length t) x (after (i ∷ t) fs)) (sym (st prog fs)) X
