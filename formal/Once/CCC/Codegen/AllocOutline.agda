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
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Once.CCC.Label using (LabelId; EntryId; e-thunk; e-fn; _≡ᵇᴵ_; ≡ᵇᴵ-true; _≡ᵇᴱ_; ≡ᵇᴱ-true)
open import Data.Nat.Properties using (+-suc; ≡ᵇ⇒≡)
open import Data.Nat using (_≡ᵇ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Once.CCC.Label using (≡ᵇᴱ-refl)
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

  -- ★ AN ALLOCATION, CALLED: the call, the routine's entry, the primitive, the
  -- return reach the program's own step, shifted (the entry's clear of no slot
  -- changes nothing; the return leaves the frame the call entered)
  alloc-site : ∀ (fs fs′ : FlatState) (q k : ℕ) → k ∈ ks
             → Shifted d fs′ fs → fpc fs ≡ suc q → fetch T q ≡ just (instr-alloc-heap k)
             → LocState.halted (floc fs) ≡ false → flink fs ≡ nothing
             → Σ FlatState λ fs″ → FlatSteps P′ 4 fs′ fs″ × Shifted d fs″ (flat-exec-instr (instr-alloc-heap k) P fs)
  alloc-site fs fs′ q k mem sh@(lo , al , pc , rt , lk , cl) pq ft h lk0 =
    s₄ , (h₀ , f₀) ∷ subst (λ mj → FlatSteps P′ 3 (do-call-at mj fs′) s₄) (sym (find-alloc k mem)) run , shifted
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
