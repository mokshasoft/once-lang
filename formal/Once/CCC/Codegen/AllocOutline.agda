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
--   * the routines' names, apart by size and by kind;
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocOutline {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
import Data.Maybe
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.CCC.Label using (LabelId; EntryId; e-thunk; e-fn; _≡ᵇᴵ_; ≡ᵇᴵ-true; _≡ᵇᴱ_; ≡ᵇᴱ-true)
open import Data.Nat.Properties using (+-suc; ≡ᵇ⇒≡)
open import Data.Nat using (_≡ᵇ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.CCC.Label using (≡ᵇᴱ-refl; ≡ᵇᴵ-refl)
open import Once.Spec.Name using (CanonicalName; canonical; module CanonicalName)
open import Data.Char using (Char)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.List.Properties using (++-cancelˡ; ∷-injective)
open import Relation.Nullary using (¬_)
open import Once.Postulates using (toList-++; extensionality)
open import Relation.Nullary using (Dec; yes; no)
open import Once.CCC.FrameSemantics using (module FrameSemantics)
open import Once.Target.Symbol using (showNat)
open import Once.Adequacy.LabelSymbols using (showNat-inj)
open import Once.CCC.Codegen.AllocExpand using (alloc-fn; free-fn; site-call; prim-routine; prim-routines; skip; skip-label; outline)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (AtDynamic; AtStack)
open import Once.Memory.HeapAddress using (sucHL)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Codegen.FlatStepLemmas using (module FlatStepsAPI)
open FlatStepsAPI {FS} using (FlatSteps; []; _∷_)
open import Once.Adequacy.FlatEvents using (module FlatEventTrace)
open FlatEventTrace {FS} using (flat-events; flat-events-step; flat-events-fetch; event-of; flat-events-steps; chain-events
                               ; flat-ctrls; flat-ctrls-step; flat-ctrls-fetch; ctrl-of; chain-ctrls; flat-ctrls-steps)
open import Once.IR.Semantics.Out using (Out; _▹_)
open import Data.Nat using (_≤_; z≤n)
open import Once.CCC.Codegen.AllocExpandEvents {FS} using (ev-unfold; ct-unfold; ev-none; ct-none; ev-halt; ct-halt)
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

------------------------------------------------------------------------
-- The routines' names: apart by size, and an alloc's from a free's
------------------------------------------------------------------------

private
  -- a name's second part
  part₂ : CanonicalName → List String
  part₂ n = CanonicalName.parts n

  second : ∀ {a b c d : String} → a ∷ b ∷ [] ≡ c ∷ d ∷ [] → b ≡ d
  second refl = refl

  head-char : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → a ≡ b
  head-char refl = refl

  tail-chars : ∀ {a b : Char} {as bs : List Char} → a ∷ as ≡ b ∷ bs → as ≡ bs
  tail-chars refl = refl

  -- a size read back from its part: the fixed lead, then its decimal
  part-size : ∀ (c : String) (k k′ : ℕ) → c ++ˢ showNat k ≡ c ++ˢ showNat k′ → k ≡ k′
  part-size c k k′ e =
    showNat-inj (++-cancelˡ (toList c) _ _ (trans (sym (toList-++ c (showNat k))) (trans (cong toList e) (toList-++ c (showNat k′)))))

alloc-fn-inj : ∀ {k k′} → alloc-fn k ≡ alloc-fn k′ → k ≡ k′
alloc-fn-inj {k} {k′} e = part-size "a" k k′ (second (cong part₂ e))

free-fn-inj : ∀ {k k′} → free-fn k ≡ free-fn k′ → k ≡ k′
free-fn-inj {k} {k′} e = part-size "f" k k′ (second (cong part₂ e))

alloc≢free : ∀ k k′ → ¬ alloc-fn k ≡ free-fn k′
alloc≢free k k′ e = a≢f (head-char (trans (sym (toList-++ "a" (showNat k))) (trans (cong toList (second (cong part₂ e))) (toList-++ "f" (showNat k′)))))
  where
    a≢f : ¬ ('a' ≡ 'f')
    a≢f ()

------------------------------------------------------------------------
-- A site, viewed (`site-call`'s catch-all does not reduce on a variable instruction)
------------------------------------------------------------------------

data SiteView : AbstractInstr → Set where
  sv-alloc : ∀ k → SiteView (instr-alloc-heap k)
  sv-free  : ∀ k → SiteView (instr-free-heap k)
  sv-same  : ∀ {i} → site-call i ≡ i → SiteView i

site-view : ∀ i → SiteView i
site-view mov-to-output                      = sv-same refl
site-view mov-to-input                       = sv-same refl
site-view load-indirect                      = sv-same refl
site-view load-indirect-suc                  = sv-same refl
site-view (load-from-slot x)                 = sv-same refl
site-view (store-at-slot x)                  = sv-same refl
site-view store-indirect                     = sv-same refl
site-view store-indirect-suc                 = sv-same refl
site-view (lea-slot x)                       = sv-same refl
site-view (restore-input x)                  = sv-same refl
site-view (instr-alloc-stack x)              = sv-same refl
site-view (instr-dealloc-stack x)            = sv-same refl
site-view (instr-reclaim-to x)               = sv-same refl
site-view (instr-push-frame x)               = sv-same refl
site-view instr-pop-frame                    = sv-same refl
site-view instr-call-closure                 = sv-same refl
site-view (worklist-init x)                  = sv-same refl
site-view (worklist-push x)                  = sv-same refl
site-view (worklist-pop x)                   = sv-same refl
site-view (worklist-check x)                 = sv-same refl
site-view (instr-sigop si)                   = sv-same refl
site-view (instr-load-const p v)             = sv-same refl
site-view (instr-load-code-addr l)           = sv-same refl
site-view instr-save-closure-reg             = sv-same refl
site-view (instr-load-tag-lit n)             = sv-same refl
site-view (instr-alloc-heap k)               = sv-alloc k
site-view (instr-reg-op op)                  = sv-same refl
site-view (instr-free-heap k)                = sv-free k
site-view (instr-room k)                     = sv-same refl
site-view (load-at k)                        = sv-same refl
site-view (store-at k)                       = sv-same refl
site-view (addr-at k)                        = sv-same refl
site-view (load-rec k)                       = sv-same refl
site-view (store-rec k)                      = sv-same refl
site-view (instr-ctrl (c-label l))           = sv-same refl
site-view (instr-ctrl (c-jmp l))             = sv-same refl
site-view (instr-ctrl (c-branch-tag-zero l)) = sv-same refl
site-view (instr-ctrl (c-entry e b))         = sv-same refl
site-view (instr-ctrl (c-call-fn f))         = sv-same refl
site-view (instr-ctrl (c-ret b))             = sv-same refl
site-view (instr-ctrl (c-start b))           = sv-same refl
site-view (instr-ctrl c-leave)               = sv-same refl

-- a site, called, is no label and no entry
label-site : ∀ i → label-of? (site-call i) ≡ label-of? i
label-site i = go (site-view i)
  where go : ∀ {i} → SiteView i → label-of? (site-call i) ≡ label-of? i
        go (sv-alloc k) = refl
        go (sv-free k)  = refl
        go {i} (sv-same e) = cong label-of? e

entry-site : ∀ i → entry-of? (site-call i) ≡ entry-of? i
entry-site i = go (site-view i)
  where go : ∀ {i} → SiteView i → entry-of? (site-call i) ≡ entry-of? i
        go (sv-alloc k) = refl
        go (sv-free k)  = refl
        go {i} (sv-same e) = cong entry-of? e

------------------------------------------------------------------------
-- The scans: called sites keep them; a scan begun `d` later finds `d` later
------------------------------------------------------------------------

fl-map : ∀ xs m i → fl-go (map site-call xs) m i ≡ fl-go xs m i
fl-map []       m i = refl
fl-map (x ∷ xs) m i = trans (cong (λ mo → fl-at mo (map site-call xs) m i) (label-site x)) (at (label-of? x))
  where
    at : ∀ mo → fl-at mo (map site-call xs) m i ≡ fl-at mo xs m i
    at nothing  = fl-map xs m (suc i)
    at (just l) = mt (l ≡ᵇᴵ m)
      where mt : ∀ b → fl-label-match b (map site-call xs) m i ≡ fl-label-match b xs m i
            mt true  = refl
            mt false = fl-map xs m (suc i)

ft-map : ∀ xs e i → ft-go (map site-call xs) e i ≡ ft-go xs e i
ft-map []       e i = refl
ft-map (x ∷ xs) e i = trans (cong (λ mo → ft-at mo (map site-call xs) e i) (entry-site x)) (at (entry-of? x))
  where
    at : ∀ mo → ft-at mo (map site-call xs) e i ≡ ft-at mo xs e i
    at nothing  = ft-map xs e (suc i)
    at (just l) = mt (l ≡ᵇᴱ e)
      where mt : ∀ b → ft-match b (map site-call xs) e i ≡ ft-match b xs e i
            mt true  = refl
            mt false = ft-map xs e (suc i)

fl-shiftᵈ : ∀ xs m d i → fl-go xs m (d + i) ≡ Data.Maybe.map (d +_) (fl-go xs m i)
fl-shiftᵈ []       m d i = refl
fl-shiftᵈ (x ∷ xs) m d i = at (label-of? x)
  where
    nx : fl-go xs m (suc (d + i)) ≡ Data.Maybe.map (d +_) (fl-go xs m (suc i))
    nx = trans (cong (fl-go xs m) (sym (+-suc d i))) (fl-shiftᵈ xs m d (suc i))
    at : ∀ mo → fl-at mo xs m (d + i) ≡ Data.Maybe.map (d +_) (fl-at mo xs m i)
    at nothing  = nx
    at (just l) = mt (l ≡ᵇᴵ m)
      where mt : ∀ b → fl-label-match b xs m (d + i) ≡ Data.Maybe.map (d +_) (fl-label-match b xs m i)
            mt true  = refl
            mt false = nx

ft-shiftᵈ : ∀ xs e d i → ft-go xs e (d + i) ≡ Data.Maybe.map (d +_) (ft-go xs e i)
ft-shiftᵈ []       e d i = refl
ft-shiftᵈ (x ∷ xs) e d i = at (entry-of? x)
  where
    nx : ft-go xs e (suc (d + i)) ≡ Data.Maybe.map (d +_) (ft-go xs e (suc i))
    nx = trans (cong (ft-go xs e) (sym (+-suc d i))) (ft-shiftᵈ xs e d (suc i))
    at : ∀ mo → ft-at mo xs e (d + i) ≡ Data.Maybe.map (d +_) (ft-at mo xs e i)
    at nothing  = nx
    at (just l) = mt (l ≡ᵇᴱ e)
      where mt : ∀ b → ft-match b xs e (d + i) ≡ Data.Maybe.map (d +_) (ft-match b xs e i)
            mt true  = refl
            mt false = nx

-- past a stretch the scan misses, it goes on after it
fl-++ : ∀ xs ys m i → fl-go xs m i ≡ nothing → fl-go (xs ++ ys) m i ≡ fl-go ys m (length xs + i)
fl-++ []       ys m i _ = refl
fl-++ (x ∷ xs) ys m i e = at (label-of? x) e
  where
    nx : fl-go xs m (suc i) ≡ nothing → fl-go (xs ++ ys) m (suc i) ≡ fl-go ys m (suc (length xs + i))
    nx e′ = trans (fl-++ xs ys m (suc i) e′) (cong (fl-go ys m) (+-suc (length xs) i))
    at : ∀ mo → fl-at mo xs m i ≡ nothing → fl-at mo (xs ++ ys) m i ≡ fl-go ys m (suc (length xs + i))
    at nothing  e′ = nx e′
    at (just l) e′ = mt (l ≡ᵇᴵ m) e′
      where mt : ∀ b → fl-label-match b xs m i ≡ nothing → fl-label-match b (xs ++ ys) m i ≡ fl-go ys m (suc (length xs + i))
            mt true  ()
            mt false e″ = nx e″

ft-++ : ∀ xs ys e i → ft-go xs e i ≡ nothing → ft-go (xs ++ ys) e i ≡ ft-go ys e (length xs + i)
ft-++ []       ys e i _ = refl
ft-++ (x ∷ xs) ys e i h = at (entry-of? x) h
  where
    nx : ft-go xs e (suc i) ≡ nothing → ft-go (xs ++ ys) e (suc i) ≡ ft-go ys e (suc (length xs + i))
    nx h′ = trans (ft-++ xs ys e (suc i) h′) (cong (ft-go ys e) (+-suc (length xs) i))
    at : ∀ mo → ft-at mo xs e i ≡ nothing → ft-at mo (xs ++ ys) e i ≡ ft-go ys e (suc (length xs + i))
    at nothing  h′ = nx h′
    at (just l) h′ = mt (l ≡ᵇᴱ e) h′
      where mt : ∀ b → ft-match b xs e i ≡ nothing → ft-match b (xs ++ ys) e i ≡ ft-go ys e (suc (length xs + i))
            mt true  ()
            mt false h″ = nx h″

------------------------------------------------------------------------
-- The jumped-over stretch: no label but the skip label, no entry but the routines'
------------------------------------------------------------------------

-- two that differ compare false
miss-L : ∀ (a b : LabelId) → ¬ a ≡ b → (a ≡ᵇᴵ b) ≡ false
miss-L a b ne = go (a ≡ᵇᴵ b) refl
  where go : ∀ x → (a ≡ᵇᴵ b) ≡ x → (a ≡ᵇᴵ b) ≡ false
        go true  e = ⊥-elim (ne (≡ᵇᴵ-true a b e))
        go false e = e

miss-E : ∀ (a b : EntryId) → ¬ a ≡ b → (a ≡ᵇᴱ b) ≡ false
miss-E a b ne = go (a ≡ᵇᴱ b) refl
  where go : ∀ x → (a ≡ᵇᴱ b) ≡ x → (a ≡ᵇᴱ b) ≡ false
        go true  e = ⊥-elim (ne (≡ᵇᴱ-true a b e))
        go false e = e

-- no routine's name
NotR : EntryId → Set
NotR e = ∀ k → (¬ e-fn (alloc-fn k) ≡ e) × (¬ e-fn (free-fn k) ≡ e)

fl-routines : ∀ ks m i → fl-go (prim-routines ks) m i ≡ nothing
fl-routines []       m i = refl
fl-routines (k ∷ ks) m i = fl-routines ks m (suc (suc (suc (suc (suc (suc i))))))

ft-routines : ∀ ks e i → NotR e → ft-go (prim-routines ks) e i ≡ nothing
ft-routines []       e i _  = refl
ft-routines (k ∷ ks) e i nr =
  trans (cong (λ b → ft-match b (instr-alloc-heap k ∷ instr-ctrl (c-ret 0) ∷ instr-ctrl (c-entry (e-fn (free-fn k)) 0)
                                 ∷ instr-free-heap k ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks) e i)
              (miss-E (e-fn (alloc-fn k)) e (proj₁ (nr k))))
    (trans (cong (λ b → ft-match b (instr-free-heap k ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks) e (suc (suc (suc i))))
                 (miss-E (e-fn (free-fn k)) e (proj₂ (nr k))))
           (ft-routines ks e (suc (suc (suc (suc (suc (suc i)))))) nr))

fl-skip : ∀ ks m i → ¬ skip-label ≡ m → fl-go (skip ks) m i ≡ nothing
fl-skip ks m i ne =
  trans (fl-++ (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ []) m (suc i) (fl-routines ks m (suc i)))
        (cong (λ b → fl-label-match b [] m (length (prim-routines ks) + suc i)) (miss-L skip-label m ne))

ft-skip : ∀ ks e i → NotR e → ft-go (skip ks) e i ≡ nothing
ft-skip ks e i nr = ft-++ (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ []) e (suc i) (ft-routines ks e (suc i) nr)

------------------------------------------------------------------------
-- The routines: where a size's are (its first in `ks`), what they hold
------------------------------------------------------------------------

rpos : List ℕ → ℕ → ℕ
rpos-at : Bool → List ℕ → ℕ → ℕ
rpos []        k = 0
rpos (k′ ∷ ks) k = rpos-at (k′ ≡ᵇ k) ks k
rpos-at true  ks k = 0
rpos-at false ks k = suc (suc (suc (suc (suc (suc (rpos ks k))))))

private
  six : ∀ i r → suc (suc (suc (suc (suc (suc i))))) + r ≡ i + suc (suc (suc (suc (suc (suc r)))))
  six zero    r = refl
  six (suc i) r = cong suc (six i r)

  ne-of : ∀ {k′ k} → (k′ ≡ᵇ k) ≡ false → ¬ k′ ≡ k
  ne-of {k′} {.k′} e refl = ne-refl k′ e
    where ne-refl : ∀ n → (n ≡ᵇ n) ≡ false → Data.Empty.⊥
          ne-refl zero    ()
          ne-refl (suc n) e′ = ne-refl n e′

  in-tail : ∀ {k k′ : ℕ} {ks : List ℕ} → ¬ k′ ≡ k → k ∈ k′ ∷ ks → k ∈ ks
  in-tail ne (here e)  = ⊥-elim (ne (sym e))
  in-tail ne (there p) = p

-- a size's alloc routine: its entry where the scan from the routines' start finds it
ft-alloc : ∀ ks k → k ∈ ks → ∀ rest i → ft-go (prim-routines ks ++ rest) (e-fn (alloc-fn k)) i ≡ just (i + rpos ks k)
ft-alloc []        k () rest i
ft-alloc (k′ ∷ ks) k mem rest i = by (k′ ≡ᵇ k) refl
  where
    by : ∀ c → (k′ ≡ᵇ k) ≡ c → ft-go (prim-routines (k′ ∷ ks) ++ rest) (e-fn (alloc-fn k)) i ≡ just (i + rpos-at c ks k)
    by true  e = trans (cong (λ z → ft-match z (instr-alloc-heap k′ ∷ instr-ctrl (c-ret 0) ∷ instr-ctrl (c-entry (e-fn (free-fn k′)) 0)
                                                 ∷ instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (alloc-fn k)) i)
                               (trans (cong (λ z → e-fn (alloc-fn z) ≡ᵇᴱ e-fn (alloc-fn k)) (≡ᵇ⇒≡ k′ k (subst Data.Bool.T (sym e) tt))) (≡ᵇᴱ-refl (e-fn (alloc-fn k)))))
                         (cong just (sym (Data.Nat.Properties.+-identityʳ i)))
    by false e =
      trans (cong (λ z → ft-match z (instr-alloc-heap k′ ∷ instr-ctrl (c-ret 0) ∷ instr-ctrl (c-entry (e-fn (free-fn k′)) 0)
                                      ∷ instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (alloc-fn k)) i)
                  (miss-E (e-fn (alloc-fn k′)) (e-fn (alloc-fn k)) (λ q → ne-of e (alloc-fn-inj {k′} {k} (e-fn-inj {alloc-fn k′} {alloc-fn k} q)))))
        (trans (cong (λ z → ft-match z (instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (alloc-fn k)) (suc (suc (suc i))))
                     (miss-E (e-fn (free-fn k′)) (e-fn (alloc-fn k)) (λ q → alloc≢free k k′ (sym (e-fn-inj {free-fn k′} {alloc-fn k} q)))))
               (trans (ft-alloc ks k (in-tail (ne-of e) mem) rest (suc (suc (suc (suc (suc (suc i)))))))
                      (cong just (six i (rpos ks k)))))
      where
        e-fn-inj : ∀ {f g} → e-fn f ≡ e-fn g → f ≡ g
        e-fn-inj refl = refl

-- a size's free routine: three past its alloc routine
ft-free : ∀ ks k → k ∈ ks → ∀ rest i → ft-go (prim-routines ks ++ rest) (e-fn (free-fn k)) i ≡ just (suc (suc (suc (i + rpos ks k))))
ft-free []        k () rest i
ft-free (k′ ∷ ks) k mem rest i = by (k′ ≡ᵇ k) refl
  where
    e-fn-inj : ∀ {f g} → e-fn f ≡ e-fn g → f ≡ g
    e-fn-inj refl = refl
    by : ∀ c → (k′ ≡ᵇ k) ≡ c → ft-go (prim-routines (k′ ∷ ks) ++ rest) (e-fn (free-fn k)) i ≡ just (suc (suc (suc (i + rpos-at c ks k))))
    by true  e =
      trans (cong (λ z → ft-match z (instr-alloc-heap k′ ∷ instr-ctrl (c-ret 0) ∷ instr-ctrl (c-entry (e-fn (free-fn k′)) 0)
                                      ∷ instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (free-fn k)) i)
                  (miss-E (e-fn (alloc-fn k′)) (e-fn (free-fn k)) (λ q → alloc≢free k′ k (e-fn-inj {alloc-fn k′} {free-fn k} q))))
        (trans (cong (λ z → ft-match z (instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (free-fn k)) (suc (suc (suc i))))
                     (trans (cong (λ z → e-fn (free-fn z) ≡ᵇᴱ e-fn (free-fn k)) (≡ᵇ⇒≡ k′ k (subst Data.Bool.T (sym e) tt))) (≡ᵇᴱ-refl (e-fn (free-fn k)))))
               (cong (λ z → just (suc (suc (suc z)))) (sym (Data.Nat.Properties.+-identityʳ i))))
    by false e =
      trans (cong (λ z → ft-match z (instr-alloc-heap k′ ∷ instr-ctrl (c-ret 0) ∷ instr-ctrl (c-entry (e-fn (free-fn k′)) 0)
                                      ∷ instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (free-fn k)) i)
                  (miss-E (e-fn (alloc-fn k′)) (e-fn (free-fn k)) (λ q → alloc≢free k′ k (e-fn-inj {alloc-fn k′} {free-fn k} q))))
        (trans (cong (λ z → ft-match z (instr-free-heap k′ ∷ instr-ctrl (c-ret 0) ∷ prim-routines ks ++ rest) (e-fn (free-fn k)) (suc (suc (suc i))))
                     (miss-E (e-fn (free-fn k′)) (e-fn (free-fn k)) (λ q → ne-of e (free-fn-inj {k′} {k} (e-fn-inj {free-fn k′} {free-fn k} q)))))
               (trans (ft-free ks k (in-tail (ne-of e) mem) rest (suc (suc (suc (suc (suc (suc i)))))))
                      (cong (λ z → just (suc (suc (suc z)))) (six i (rpos ks k)))))

-- what a size's routines hold, where they are
record Routines (prog : AbstractTrace) (r k : ℕ) : Set where
  field
    at-ae : fetch prog r ≡ just (instr-ctrl (c-entry (e-fn (alloc-fn k)) 0))
    at-a  : fetch prog (suc r) ≡ just (instr-alloc-heap k)
    at-ar : fetch prog (suc (suc r)) ≡ just (instr-ctrl (c-ret 0))
    at-fe : fetch prog (suc (suc (suc r))) ≡ just (instr-ctrl (c-entry (e-fn (free-fn k)) 0))
    at-f  : fetch prog (suc (suc (suc (suc r)))) ≡ just (instr-free-heap k)
    at-fr : fetch prog (suc (suc (suc (suc (suc r))))) ≡ just (instr-ctrl (c-ret 0))

routines-at : ∀ ks k → k ∈ ks → ∀ rest → Routines (prim-routines ks ++ rest) (rpos ks k) k
routines-at []        k () rest
routines-at (k′ ∷ ks) k mem rest = by (k′ ≡ᵇ k) refl
  where
    by : ∀ c → (k′ ≡ᵇ k) ≡ c → Routines (prim-routines (k′ ∷ ks) ++ rest) (rpos-at c ks k) k
    by true  e = subst (λ z → Routines (prim-routines (z ∷ ks) ++ rest) 0 k) (sym (≡ᵇ⇒≡ k′ k (subst Data.Bool.T (sym e) tt)))
                   (record { at-ae = refl ; at-a = refl ; at-ar = refl ; at-fe = refl ; at-f = refl ; at-fr = refl })
    by false e = record { at-ae = R.at-ae ; at-a = R.at-a ; at-ar = R.at-ar ; at-fe = R.at-fe ; at-f = R.at-f ; at-fr = R.at-fr }
      where module R = Routines (routines-at ks k (in-tail (ne-of e) mem) rest)

------------------------------------------------------------------------
-- A routine's entry clears a frame of no slots: no slot changes (extensionality)
------------------------------------------------------------------------

private
  clear-aux0 : ∀ {f f′ : FrameSemantics.Frame FS} (k′ : ℕ) (dx : Dec (f ≡ f′)) (o : Maybe (StoredValue FS))
             → MemOps.clear-frame-aux {FS} {f} {f′} {k′} {0} dx (Data.Nat.Properties._<?_ k′ 0) o ≡ o
  clear-aux0 k′ (yes _) o = refl
  clear-aux0 k′ (no _)  o = refl

clear0 : ∀ (m : StackMem FS) (f : FrameSemantics.Frame FS) → MemOps.clear-frame {FS} m f 0 ≡ m
clear0 m f = extensionality (λ f′ → extensionality (λ k′ → clear-aux0 k′ (FrameSemantics._≟F_ FS f f′) (m f′ k′)))

------------------------------------------------------------------------
-- ★ The outlined program's scans: the program's own, `d` on
------------------------------------------------------------------------

module Out (ks : List ℕ) (b : ℕ) (T : AbstractTrace) where

  P P′ : AbstractTrace
  P  = instr-ctrl (c-start b) ∷ T
  P′ = outline ks P

  d : ℕ
  d = length (skip ks)

  find-label-out : ∀ m → ¬ skip-label ≡ m → find-label P′ m ≡ Data.Maybe.map (d +_) (find-label P m)
  find-label-out m ne =
    trans (fl-++ (skip ks) (map site-call T) m 1 (fl-skip ks m 1 ne))
          (trans (fl-map T m (d + 1)) (fl-shiftᵈ T m d 1))

  find-entry-out : ∀ e → NotR e → find-entry P′ e ≡ Data.Maybe.map (d +_) (find-entry P e)
  find-entry-out e nr =
    trans (ft-++ (skip ks) (map site-call T) e 1 (ft-skip ks e 1 nr))
          (trans (ft-map T e (d + 1)) (ft-shiftᵈ T e d 1))

  -- the routines, at the outlined program's pc `2 + rpos ks k`
  private
    shape : P′ ≡ instr-ctrl (c-start b) ∷ instr-ctrl (c-jmp skip-label) ∷ prim-routines ks ++ instr-ctrl (c-label skip-label) ∷ map site-call T
    shape = cong (λ z → instr-ctrl (c-start b) ∷ instr-ctrl (c-jmp skip-label) ∷ z)
                 (Data.List.Properties.++-assoc (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ []) (map site-call T))

  rp : ℕ → ℕ
  rp k = suc (suc (rpos ks k))

  find-alloc : ∀ k → k ∈ ks → find-fn P′ (alloc-fn k) ≡ just (rp k)
  find-alloc k mem = trans (cong (λ z → find-fn z (alloc-fn k)) shape)
                           (ft-alloc ks k mem (instr-ctrl (c-label skip-label) ∷ map site-call T) 2)

  find-free : ∀ k → k ∈ ks → find-fn P′ (free-fn k) ≡ just (suc (suc (suc (rp k))))
  find-free k mem = trans (cong (λ z → find-fn z (free-fn k)) shape)
                          (ft-free ks k mem (instr-ctrl (c-label skip-label) ∷ map site-call T) 2)

  routines-out : ∀ k → k ∈ ks → Routines P′ (rp k) k
  routines-out k mem = subst (λ z → Routines z (rp k) k) (sym shape) (record
    { at-ae = R.at-ae ; at-a = R.at-a ; at-ar = R.at-ar ; at-fe = R.at-fe ; at-f = R.at-f ; at-fr = R.at-fr })
    where module R = Routines (routines-at ks k mem (instr-ctrl (c-label skip-label) ∷ map site-call T))

  -- past the start, the outlined program fetches the program's instruction, called, `d` on
  fetch-out : ∀ q → fetch P′ (d + suc q) ≡ Data.Maybe.map site-call (fetch T q)
  fetch-out q =
    trans (cong (fetch P′) (+-suc d q))
      (trans (fetch-++-right (skip ks) (map site-call T) q) (fetch-map T q))
    where
      fetch-map : ∀ (xs : AbstractTrace) n → fetch (map site-call xs) n ≡ Data.Maybe.map site-call (fetch xs n)
      fetch-map []       n       = refl
      fetch-map (x ∷ xs) zero    = refl
      fetch-map (x ∷ xs) (suc n) = fetch-map xs n

  -- a chain's events and control steps, through a rewrite of its first state
  ce-subst : ∀ {A : Set} {k z} (F : A → FlatState) {x y : A} (e : x ≡ y) (c : FlatSteps P′ k (F x) z)
           → chain-events (subst (λ w → FlatSteps P′ k (F w) z) e c) ≡ chain-events c
  ce-subst F refl c = refl

  -- ★ AN ALLOCATION, CALLED: the call, the routine's entry, the primitive, the
  -- return reach the program's own step, shifted (the entry's clear of no slot
  -- changes nothing; the return leaves the frame the call entered)
  alloc-site : ∀ (fs fs′ : FlatState) (q k : ℕ) → k ∈ ks
             → Shifted d fs′ fs → fpc fs ≡ suc q → fetch T q ≡ just (instr-alloc-heap k)
             → LocState.halted (floc fs) ≡ false → flink fs ≡ nothing
             → Σ FlatState λ fs″ → Σ (FlatSteps P′ 4 fs′ fs″) λ c → (chain-events c ≡ []) × Shifted d fs″ (flat-exec-instr (instr-alloc-heap k) P fs)
  alloc-site fs fs′ q k mem sh@(lo , al , pc , rt , lk , cl) pq ft h lk0 =
    s₄ , (h₀ , f₀) ∷ subst (λ mj → FlatSteps P′ 3 (do-call-at mj fs′) s₄) (sym (find-alloc k mem)) run
       , ce-subst (λ mj → do-call-at mj fs′) (sym (find-alloc k mem)) run , shifted
    where
      R = routines-out k mem
      open Routines R
      h₀ : LocState.halted (floc fs′) ≡ false
      h₀ = trans (cong LocState.halted lo) h
      f₀ : fetch P′ (fpc fs′) ≡ just (instr-ctrl (c-call-fn (alloc-fn k)))
      f₀ = trans (cong (fetch P′) (trans pc (cong (d +_) pq))) (trans (fetch-out q) (cong (Data.Maybe.map site-call) ft))
      s₁ s₂ s₃ s₄ : FlatState
      s₁ = do-call-at (just (rp k)) fs′
      s₂ = flat-exec-instr (instr-ctrl (c-entry (e-fn (alloc-fn k)) 0)) P′ s₁
      s₃ = flat-exec-instr (instr-alloc-heap k) P′ s₂
      s₄ = flat-exec-instr (instr-ctrl (c-ret 0)) P′ s₃
      run : FlatSteps P′ 3 s₁ s₄
      run = (h₀ , at-ae) ∷ (h₀ , at-a) ∷ (h₀ , at-ar) ∷ []
      lo′ : floc s₄ ≡ floc (flat-exec-instr (instr-alloc-heap k) P fs)
      lo′ = trans (cong (λ m → proj₁ (AbstractExec.exec-abstract {FS} (instr-alloc-heap k) (record (floc fs′) { stackMem = m }) (falloc fs′)))
                        (clear0 (LocState.stackMem (floc fs′)) _))
                  (cong₂ (λ L A → proj₁ (AbstractExec.exec-abstract {FS} (instr-alloc-heap k) L A)) lo al)
      al′ : falloc s₄ ≡ falloc (flat-exec-instr (instr-alloc-heap k) P fs)
      al′ = cong₂ (λ L A → proj₂ (AbstractExec.exec-abstract {FS} (instr-alloc-heap k) L A)) lo al
      shifted : Shifted d s₄ (flat-exec-instr (instr-alloc-heap k) P fs)
      shifted = lo′ , al′ , trans (cong suc pc) (sym (+-suc d (fpc fs))) , rt , sym (cong (Data.Maybe.map (d +_)) lk0) , cl

  -- ★ A FREE, CALLED: as an allocation, the free's gate passed at the program's state
  -- (it reads the registers and the blocks' sizes and marks, which the call and the
  -- entry leave as they were)
  free-site : ∀ (fs fs′ : FlatState) (q k : ℕ) → k ∈ ks
            → Shifted d fs′ fs → fpc fs ≡ suc q → fetch T q ≡ just (instr-free-heap k)
            → LocState.halted (floc fs) ≡ false → flink fs ≡ nothing
            → gate-ok (instr-free-heap k) (floc fs) (falloc fs) ≡ true
            → Σ FlatState λ fs″ → Σ (FlatSteps P′ 4 fs′ fs″) λ c → (chain-events c ≡ []) × Shifted d fs″ (flat-exec-instr (instr-free-heap k) P fs)
  free-site fs fs′ q k mem sh@(lo , al , pc , rt , lk , cl) pq ft h lk0 g =
    s₄ , (h₀ , f₀) ∷ subst (λ mj → FlatSteps P′ 3 (do-call-at mj fs′) s₄) (sym (find-free k mem)) run
       , ce-subst (λ mj → do-call-at mj fs′) (sym (find-free k mem)) run , fin _ _ g₂ g
    where
      R = routines-out k mem
      open Routines R
      h₀ : LocState.halted (floc fs′) ≡ false
      h₀ = trans (cong LocState.halted lo) h
      f₀ : fetch P′ (fpc fs′) ≡ just (instr-ctrl (c-call-fn (free-fn k)))
      f₀ = trans (cong (fetch P′) (trans pc (cong (d +_) pq))) (trans (fetch-out q) (cong (Data.Maybe.map site-call) ft))
      s₁ s₂ s₃ s₄ : FlatState
      s₁ = do-call-at (just (suc (suc (suc (rp k))))) fs′
      s₂ = flat-exec-instr (instr-ctrl (c-entry (e-fn (free-fn k)) 0)) P′ s₁
      s₃ = flat-exec-instr (instr-free-heap k) P′ s₂
      s₄ = flat-exec-instr (instr-ctrl (c-ret 0)) P′ s₃
      -- the gate at the routine's state is the gate at the program's
      g₂ : gate-ok (instr-free-heap k) (floc s₂) (falloc s₂) ≡ true
      g₂ = trans (bb (readReg (LocState.regs (floc fs′)) Input1)) (trans (cong₂ (λ L A → gate-ok (instr-free-heap k) L A) lo al) g)
        where
          -- the gate reads a block's size and mark, not the frame
          bb : ∀ v → block-base? k v (falloc s₂) ≡ block-base? k v (falloc fs′)
          bb (SV-Ptr (AtDynamic hl)) = refl
          bb (SV-Ptr (AtStack _ _))  = refl
          bb (SV-Tag _)              = refl
          bb (SV-Lit _ _)            = refl
          bb (SV-Code _)             = refl
      h₃ : ∀ b → b ≡ true → LocState.halted (floc (straight-at b (instr-free-heap k) s₂)) ≡ false
      h₃ .true refl = h₀
      f₃ : ∀ b → b ≡ true → fetch P′ (fpc (straight-at b (instr-free-heap k) s₂)) ≡ just (instr-ctrl (c-ret 0))
      f₃ .true refl = at-fr
      run : FlatSteps P′ 3 s₁ s₄
      run = (h₀ , at-fe) ∷ (h₀ , at-f) ∷ (h₃ _ g₂ , f₃ _ g₂) ∷ []
      fin : ∀ b b′ → b ≡ true → b′ ≡ true
          → Shifted d (do-ret 0 (fret (straight-at b (instr-free-heap k) s₂)) (straight-at b (instr-free-heap k) s₂))
                      (straight-at b′ (instr-free-heap k) fs)
      fin .true .true refl refl =
          trans (cong (λ m → proj₁ (AbstractExec.exec-abstract {FS} (instr-free-heap k) (record (floc fs′) { stackMem = m }) (falloc fs′)))
                      (clear0 (LocState.stackMem (floc fs′)) _))
                (cong₂ (λ L A → proj₁ (AbstractExec.exec-abstract {FS} (instr-free-heap k) L A)) lo al)
        , cong₂ (λ L A → proj₂ (AbstractExec.exec-abstract {FS} (instr-free-heap k) L A)) lo al
        , trans (cong suc pc) (sym (+-suc d (fpc fs))) , rt , sym (cong (Data.Maybe.map (d +_)) lk0) , cl

  -- what a plain instruction looks up agrees, up to `d`: no jump of the program's
  -- targets the skip label, and no call of its names a routine
  agree : ∀ i → (∀ m → (i ≡ instr-ctrl (c-jmp m)) ⊎ (i ≡ instr-ctrl (c-branch-tag-zero m)) → ¬ skip-label ≡ m)
        → (∀ f → i ≡ instr-ctrl (c-call-fn f) → NotR (e-fn f))
        → Agree d i P′ P
  agree mov-to-output                         nj nc = tt
  agree mov-to-input                          nj nc = tt
  agree load-indirect                         nj nc = tt
  agree load-indirect-suc                     nj nc = tt
  agree (load-from-slot x)                    nj nc = tt
  agree (store-at-slot x)                     nj nc = tt
  agree store-indirect                        nj nc = tt
  agree store-indirect-suc                    nj nc = tt
  agree (lea-slot x)                          nj nc = tt
  agree (restore-input x)                     nj nc = tt
  agree (instr-alloc-stack x)                 nj nc = tt
  agree (instr-dealloc-stack x)               nj nc = tt
  agree (instr-reclaim-to x)                  nj nc = tt
  agree (instr-push-frame x)                  nj nc = tt
  agree instr-pop-frame                       nj nc = tt
  agree instr-call-closure                 nj nc = λ tg → find-entry-out (e-thunk tg) (λ k → (λ ()) , (λ ()))
  agree (worklist-init x)                     nj nc = tt
  agree (worklist-push x)                     nj nc = tt
  agree (worklist-pop x)                      nj nc = tt
  agree (worklist-check x)                    nj nc = tt
  agree (instr-sigop si)                      nj nc = tt
  agree (instr-load-const p v)                nj nc = tt
  agree (instr-load-code-addr l)              nj nc = tt
  agree instr-save-closure-reg                nj nc = tt
  agree (instr-load-tag-lit n)                nj nc = tt
  agree (instr-alloc-heap k)                  nj nc = tt
  agree (instr-reg-op op)                     nj nc = tt
  agree (instr-free-heap k)                   nj nc = tt
  agree (instr-room k)                        nj nc = tt
  agree (load-at k)                           nj nc = tt
  agree (store-at k)                          nj nc = tt
  agree (addr-at k)                           nj nc = tt
  agree (load-rec k)                          nj nc = tt
  agree (store-rec k)                         nj nc = tt
  agree (instr-ctrl (c-label l))              nj nc = tt
  agree (instr-ctrl (c-jmp m))             nj nc = find-label-out m (nj m (inj₁ refl))
  agree (instr-ctrl (c-branch-tag-zero m)) nj nc = find-label-out m (nj m (inj₂ refl))
  agree (instr-ctrl (c-entry e b))            nj nc = tt
  agree (instr-ctrl (c-call-fn f))         nj nc = find-entry-out (e-fn f) (nc f refl)
  agree (instr-ctrl (c-ret b))                nj nc = tt
  agree (instr-ctrl (c-start b))              nj nc = tt
  agree (instr-ctrl c-leave)                  nj nc = tt

  -- ★ A PLAIN STEP: the same instruction, one step each, shifted
  plain-step : ∀ (fs fs′ : FlatState) (q : ℕ) (i : AbstractInstr)
             → Shifted d fs′ fs → fpc fs ≡ suc q → fetch T q ≡ just i → site-call i ≡ i
             → LocState.halted (floc fs) ≡ false
             → (∀ m → (i ≡ instr-ctrl (c-jmp m)) ⊎ (i ≡ instr-ctrl (c-branch-tag-zero m)) → ¬ skip-label ≡ m)
             → (∀ f → i ≡ instr-ctrl (c-call-fn f) → NotR (e-fn f))
             → FlatSteps P′ 1 fs′ (flat-exec-instr i P′ fs′) × Shifted d (flat-exec-instr i P′ fs′) (flat-exec-instr i P fs)
  plain-step fs fs′ q i sh@(lo , al , pc , rt , lk , cl) pq ft e h nj nc =
      ((trans (cong LocState.halted lo) h
       , trans (cong (fetch P′) (trans pc (cong (d +_) pq))) (trans (fetch-out q) (trans (cong (Data.Maybe.map site-call) ft) (cong just e)))) ∷ [])
    , shifted-instrᵍ d i P′ P fs′ fs (agree i nj nc) sh

  -- the skip label, where the scan finds it: past the jump and the routines
  private
    n : ℕ
    n = length (prim-routines ks)

    shape′ : P′ ≡ instr-ctrl (c-start b) ∷ instr-ctrl (c-jmp skip-label) ∷ prim-routines ks ++ instr-ctrl (c-label skip-label) ∷ map site-call T
    shape′ = cong (λ z → instr-ctrl (c-start b) ∷ instr-ctrl (c-jmp skip-label) ∷ z)
                  (Data.List.Properties.++-assoc (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ []) (map site-call T))

    find-skip : find-label P′ skip-label ≡ just (suc (suc n))
    find-skip = trans (cong (λ z → find-label z skip-label) shape′)
                  (trans (fl-++ (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ map site-call T) skip-label 2 (fl-routines ks skip-label 2))
                    (trans (cong (λ z → fl-label-match z (map site-call T) skip-label (n + 2)) (≡ᵇᴵ-refl skip-label))
                           (cong just (Data.Nat.Properties.+-comm n 2))))

    at-skip : fetch P′ (suc (suc n)) ≡ just (instr-ctrl (c-label skip-label))
    at-skip = trans (cong (λ z → fetch z (suc (suc n))) shape′)
                    (trans (cong (fetch (prim-routines ks ++ instr-ctrl (c-label skip-label) ∷ map site-call T)) (sym (Data.Nat.Properties.+-identityʳ n)))
                           (fetch-++-right (prim-routines ks) (instr-ctrl (c-label skip-label) ∷ map site-call T) 0))

    d≡ : d ≡ suc (n + 1)
    d≡ = cong suc (Data.List.Properties.length-++ (prim-routines ks))

  -- ★ THE START: the program's start, then the jump over the routines and the
  -- skip label, reach the program's start step, shifted
  start-step : ∀ (s₀ : FlatState) → fpc s₀ ≡ 0 → fret s₀ ≡ [] → LocState.halted (floc s₀) ≡ false
             → Σ FlatState λ fs″ → FlatSteps P′ 3 s₀ fs″ × Shifted d fs″ (flat-exec-instr (instr-ctrl (c-start b)) P s₀)
  start-step s₀ p0 r0 h =
    s₃ , (h , trans (cong (fetch P′) p0) refl)
       ∷ (h , trans (cong (λ z → fetch P′ (suc z)) p0) refl)
       ∷ subst (λ mj → FlatSteps P′ 1 (do-jump mj s₁) s₃) (sym find-skip) ((h , at-skip) ∷ [])
       , refl , refl , pcs , trans r0 (cong (map (d +_)) (sym r0)) , refl , refl
    where
      s₁ s₃ : FlatState
      s₁ = flat-exec-instr (instr-ctrl (c-start b)) P′ s₀
      s₃ = flat-exec-instr (instr-ctrl (c-label skip-label)) P′ (do-jump (just (suc (suc n))) s₁)
      pcs : suc (suc (suc n)) ≡ d + suc (fpc s₀)
      pcs = trans (cong suc (trans (sym (Data.Nat.Properties.+-comm n 2)) (sym (Data.Nat.Properties.+-assoc n 1 1))))
              (trans (cong (_+ 1) (sym d≡)) (cong (d +_) (cong suc (sym p0))))


  cc-subst : ∀ {k x y z} (e : x ≡ y) (c : FlatSteps P′ k x z)
           → chain-ctrls (subst (λ w → FlatSteps P′ k w z) e c) ≡ chain-ctrls c
  cc-subst refl c = refl

  -- a gate a step passes without faulting
  gate-true : ∀ (bg : Bool) (i : AbstractInstr) (fs : FlatState)
            → LocState.faulted (floc (straight-at bg i fs)) ≡ false → bg ≡ true
  gate-true true  i fs _  = refl
  gate-true false i fs ()

  ------------------------------------------------------------------------
  -- ★★ THE RUNS SHOW THE SAME: from shifted states, at every fuel of the
  -- program, a fuel of the outlined one with EQUAL events and at least the
  -- program's control steps (what `FlatShows` reads)
  ------------------------------------------------------------------------

  Same : ℕ → FlatState → ℕ → FlatState → Set
  Same m fs′ n fs = (flat-events m P′ fs′ ≡ flat-events n P fs) × (flat-ctrls n P fs ≤ flat-ctrls m P′ fs′)

  module Run (Good : FlatState → Set)
             (g-step : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i → Good (flat-exec-instr i P fs))
             (g-ns   : ∀ {fs} → Good fs → ¬ fetch P (fpc fs) ≡ just (instr-ctrl (c-start b)))
             (g-link : ∀ {fs i} → Good fs → fetch P (fpc fs) ≡ just i → (∀ e bb → ¬ i ≡ instr-ctrl (c-entry e bb)) → flink fs ≡ nothing)
             (g-nf   : ∀ {fs i} → Good fs → LocState.halted (floc fs) ≡ false → fetch P (fpc fs) ≡ just i
                     → LocState.faulted (floc (flat-exec-instr i P fs)) ≡ false)
             (sz     : ∀ q k → (fetch T q ≡ just (instr-alloc-heap k)) ⊎ (fetch T q ≡ just (instr-free-heap k)) → k ∈ ks)
             (nj     : ∀ q i m → fetch T q ≡ just i → (i ≡ instr-ctrl (c-jmp m)) ⊎ (i ≡ instr-ctrl (c-branch-tag-zero m)) → ¬ skip-label ≡ m)
             (nc     : ∀ q i f → fetch T q ≡ just i → i ≡ instr-ctrl (c-call-fn f) → NotR (e-fn f))
             where

    private
      ≤-+ : ∀ {a x y z} → a ≤ y → x ≤ z → a + x ≤ y + z
      ≤-+ = Data.Nat.Properties.+-mono-≤

    ev : ∀ n {fs fs′} → Good fs → Shifted d fs′ fs → Σ ℕ λ m → Same m fs′ n fs
    ev zero    G sh = 0 , refl , z≤n
    ev (suc n) {fs} {fs′} G sh@(lo , al , pc , rt , lk , cl) = by-h (LocState.halted (floc fs)) refl
      where
        hg : ∀ {bh} → LocState.halted (floc fs) ≡ bh → LocState.halted (floc fs′) ≡ bh
        hg e = trans (cong LocState.halted lo) e

        -- a step's chain, its events none or the step's, its controls at least the step's
        go : ∀ {i N fs″} → (h : LocState.halted (floc fs) ≡ false) → (f : fetch P (fpc fs) ≡ just i)
           → (c : FlatSteps P′ N fs′ fs″) → chain-events c ≡ event-of i fs → ctrl-of i ≤ chain-ctrls c
           → Shifted d fs″ (flat-exec-instr i P fs) → Σ ℕ λ m → Same m fs′ (suc n) fs
        go {i} {N} {fs″} h f c ce cc sh′ = go′ (ev n (g-step G h f) sh′)
          where
            go′ : Σ ℕ (λ m → Same m fs″ n (flat-exec-instr i P fs)) → Σ ℕ λ m → Same m fs′ (suc n) fs
            go′ (m′ , ee , ec) =
              N + m′
              , trans (flat-events-steps c m′) (trans (cong₂ _▹_ ce ee) (sym (ev-unfold n P fs h f)))
              , subst (_≤ flat-ctrls (N + m′) P′ fs′) (sym (ct-unfold n P fs h f))
                  (subst (ctrl-of i + flat-ctrls n P (flat-exec-instr i P fs) ≤_) (sym (flat-ctrls-steps c m′)) (≤-+ cc ec))

        not-entry-a : ∀ k → ∀ e bb → ¬ instr-alloc-heap k ≡ instr-ctrl (c-entry e bb)
        not-entry-a k e bb ()
        not-entry-f : ∀ k → ∀ e bb → ¬ instr-free-heap k ≡ instr-ctrl (c-entry e bb)
        not-entry-f k e bb ()

        at-q : ∀ q → fpc fs ≡ suc q → LocState.halted (floc fs) ≡ false → ∀ mi → fetch T q ≡ mi → Σ ℕ λ m → Same m fs′ (suc n) fs
        at-q q pq h nothing ft =
          1 , trans (ev-none 0 P′ fs′ (hg h) (trans (cong (fetch P′) (trans pc (cong (d +_) pq))) (trans (fetch-out q) (cong (Data.Maybe.map site-call) ft))))
                    (sym (ev-none n P fs h (trans (cong (fetch P) pq) ft)))
            , subst (_≤ flat-ctrls 1 P′ fs′) (sym (ct-none n P fs h (trans (cong (fetch P) pq) ft))) z≤n
        at-q q pq h (just i) ft = view (site-view i) ft
          where
            fP : ∀ {j} → fetch T q ≡ just j → fetch P (fpc fs) ≡ just j
            fP e = trans (cong (fetch P) pq) e
            view : ∀ {j} → SiteView j → fetch T q ≡ just j → Σ ℕ λ m → Same m fs′ (suc n) fs
            view (sv-alloc k) e =
              let (fs″ , c , ce , sh′) = alloc-site fs fs′ q k (sz q k (inj₁ e)) sh pq e h (g-link G (fP e) (not-entry-a k))
              in go h (fP e) c ce z≤n sh′
            view (sv-free k) e =
              let g = gate-true (gate-ok (instr-free-heap k) (floc fs) (falloc fs)) (instr-free-heap k) fs (g-nf G h (fP e))
                  (fs″ , c , ce , sh′) = free-site fs fs′ q k (sz q k (inj₂ e)) sh pq e h (g-link G (fP e) (not-entry-f k)) g
              in go h (fP e) c ce z≤n sh′
            view {j} (sv-same se) e =
              let (c , sh′) = plain-step fs fs′ q j sh pq e se h (λ m w → nj q j m e w) (λ f w → nc q j f e w)
              in go h (fP e) c (trans (Data.List.Properties.++-identityʳ _) (cong (λ L → FlatEventTrace.ev-of-loc {FS} j L) lo))
                    (subst (_≤ ctrl-of j + 0) refl (Data.Nat.Properties.m≤m+n (ctrl-of j) 0)) sh′

        by-pc : ∀ p → fpc fs ≡ p → LocState.halted (floc fs) ≡ false → Σ ℕ λ m → Same m fs′ (suc n) fs
        by-pc zero    e h = ⊥-elim (g-ns G (cong (fetch P) e))
        by-pc (suc q) e h = at-q q e h (fetch T q) refl

        by-h : ∀ bh → LocState.halted (floc fs) ≡ bh → Σ ℕ λ m → Same m fs′ (suc n) fs
        by-h true  e =
          1 , trans (ev-halt 0 P′ fs′ (hg e)) (trans (cong (λ L → flat-events-step true 0 P′ (record fs′ { floc = L })) lo) (sym (ev-halt n P fs e)))
            , subst (_≤ flat-ctrls 1 P′ fs′) (sym (ct-halt n P fs e)) z≤n
        by-h false e = by-pc (fpc fs) refl e
