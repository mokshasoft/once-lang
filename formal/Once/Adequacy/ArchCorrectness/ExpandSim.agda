-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.ExpandSim — the arch's theorem for the
-- allocator's expansion of an image (D470/D472, plan 0.146 B1.6 item 3c4).
--
-- An arch (`ArchSim`) runs an emitted image whose flat run shows its program;
-- the allocator's expansion of that image (`AllocExpand.expand`) is an emitted
-- image too (`AllocExpandEmitted`), and its flat run never faults and shows the
-- same (`AllocExpandEvents`: from the start, through the expansion's set-up, then
-- step by step against the image's own run). So the arch runs the expansion,
-- room-checked, with the program's trace.
--
-- The image's run keeps what the step simulation reads (`Keeps`): a reached
-- state (`RunAt`), past the start, with a well-formed store and closure.
------------------------------------------------------------------------

open import Once.Spec.Name using (CanonicalName)
open import Once.Adequacy.ArchCorrectness.Interface using (ArchSim; module ArchSim; FlatShows)
open import Once.Target.Backend using (Backend)

module Once.Adequacy.ArchCorrectness.ExpandSim (o : CanonicalName) {B : Backend} (A : ArchSim o B) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (LabelId; module LabelId)
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.RoomChecks using (room-checks)
open import Once.Denotation.Program using (IRProgram)
open import Once.Spec.Trace using (_⊑ᵗ⟨_⟩_)
open import Once.CCC.FrameSemantics using (fs-numerics; module FrameSemantics)
open import Once.Adequacy.MachineTrace using (module Machine)
open import Once.Denotation.ProgramTrace using (⟦_⟧IRᵗ)

open ArchSim A
open FlatMachine {FS} using (FlatState; module FlatState; fetch; flat-exec-instr)
open FlatState
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (Sound; _∷_; [])
open import Once.Adequacy.ArchCorrectness.FlatCore.RunContext o FS slot-size word-eq
  using (Emitted; module Emitted; RunAt; mkRunAt; module RunAt; reach-start; reach-step; run-sound)
open import Once.Adequacy.ArchCorrectness.FlatCore.RunWF o FS slot-size word-eq
  using (run-step-pc-pos; frame-op-absurd; start-at-zero)
open import Once.CCC.Machine.FlatStoreWF FS using (FlatWF; sv-below; flat-wf-step; cl-step)
import Once.CCC.Codegen.AllocExpandEmitted
import Once.CCC.Codegen.AllocExpandEvents
import Once.CCC.Codegen.AllocExpandDispatch
import Once.CCC.Codegen.AllocExpandStart

module _ (C : Classes) (small : 3 + count C ≤ rec-size)
         (in-range : ∀ k → cls C k < count C) (fits : ∀ k → k ≤ bsz C k)
         (q : IRProgram) (b : ℕ) (tail : AbstractTrace) (env : String → Maybe (Backend.Payload B))
         (Sz : ℕ → Set)
         (uniform  : ∀ k k′ → Sz k → Sz k′ → cls C k ≡ cls C k′ → bsz C k ≡ bsz C k′)
         where
  P : AbstractTrace
  P = instr-ctrl (c-start b) ∷ tail

  E : AbstractTrace
  E = expand C P

  module _ (sz-alloc : ∀ n k → fetch P n ≡ just (instr-alloc-heap k) → Sz k)
           (sz-free  : ∀ n k → fetch P n ≡ just (instr-free-heap k) → Sz k)
           (img      : ∀ n m → fetch P n ≡ just (instr-ctrl (c-label m)) → ImgL m)
           (jmp-lbl  : ∀ n m → fetch P n ≡ just (instr-ctrl (c-jmp m)) → ImgL m)
           (br-lbl   : ∀ n m → fetch P n ≡ just (instr-ctrl (c-branch-tag-zero m)) → ImgL m)
           (no-lrec  : ∀ n k → fetch P n ≡ just (load-rec k) → ⊥)
           (no-srec  : ∀ n k → fetch P n ≡ just (store-rec k) → ⊥)
           (em : Emitted P) (snd : Sound P start) where
    private
      module Ev = Once.CCC.Codegen.AllocExpandEvents {FS}
      module Cd = Once.CCC.Codegen.AllocExpandEmitted.Code {FS} C small in-range fits

    -- what the image's run keeps
    Good : FlatState → Set
    Good fs = RunAt P fs × (fpc fs ≡ 0 → ⊥) × FlatWF fs × sv-below (AllocState.next-heap-ref (falloc fs)) (fclosure fs)

    keeps : Ev.Keeps C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl Good
    keeps = record
      { g-step = λ { {fs} {i} (r , ns , wf , cl) h f →
                     mkRunAt (RunAt.run-em r) (reach-step i fs (RunAt.run-reach r) f h)
                   , run-step-pc-pos P fs i r f , flat-wf-step i P fs wf , cl-step i P fs wf cl }
      ; g-em   = λ { {fs} {i} (r , _) f → frame-op-absurd P fs i (RunAt.run-em r) f }
      ; g-ns   = λ { {fs} {i} (r , ns , _) f b′ e → ns (start-at-zero P (fpc fs) b′ (RunAt.run-em r) (subst (λ j → fetch P (fpc fs) ≡ just j) e f)) }
      ; g-nr   = λ { {fs} {i} _ f → (λ k e → no-lrec (fpc fs) k (subst (λ j → fetch P (fpc fs) ≡ just j) e f))
                                   , (λ k e → no-srec (fpc fs) k (subst (λ j → fetch P (fpc fs) ≡ just j) e f)) }
      ; g-nf   = λ { {fs} {i} (r , _) h f → run-sound r ((h , f) ∷ []) }
      ; g-wf   = λ { (_ , _ , wf , _) → wf }
      ; g-cw   = λ { (_ , _ , _ , cl) → cl }
      }

    -- the image's run past its start
    x : FlatState
    x = flat-exec-instr (instr-ctrl (c-start b)) P start

    r₀ : RunAt P start
    r₀ = mkRunAt em (reach-start start entry-like refl snd)

    G₁ : Good x
    G₁ = mkRunAt em (reach-step (instr-ctrl (c-start b)) start (RunAt.run-reach r₀) refl refl)
       , (λ ()) , flat-wf-step (instr-ctrl (c-start b)) P start entry-wf , cl-step (instr-ctrl (c-start b)) P start entry-wf entry-cl

    S₁ : Once.CCC.Codegen.AllocExpandStart.Start {FS} x
    S₁ = record { s-heap = λ _ → refl ; s-next = refl ; s-free = λ _ → refl ; s-size = λ _ → refl ; s-ret = refl ; s-halt = refl }

    module St = Ev.Start′ C P Sz uniform fits in-range sz-alloc sz-free img jmp-lbl br-lbl keeps start b refl refl refl S₁ refl refl G₁

    -- ★★ THE ARCH RUNS THE EXPANSION, room-checked, with the program's trace: the
    -- expansion is emitted, its flat run never faults (from the start, through the
    -- set-up, against the image's own run) and shows what the image's shows, with
    -- at least its control steps
    sim-exp : ArithTable (room-checks E) env → FlatShows FS P start q
            → Machine.trace (δ env (compile (room-checks E))) init ⊑ᵗ⟨ _≡_ ⟩ ⟦ just q ⟧IRᵗ (fs-numerics FS) (FrameSemantics.fs-interp FS)
    sim-exp tb fl = sim q b (setup C ++ expand-from C 1 tail) env
                        (Cd.Em.emitted o slot-size word-eq P em) tb (St.sound-start refl refl) shows
      where
        shows : FlatShows FS E start q
        shows k = let (N , e , c) = fl k ; (m , ee , ec) = St.ev-start N
                  in m , trans ee e , λ z → Data.Nat.Properties.≤-trans (c z) ec
