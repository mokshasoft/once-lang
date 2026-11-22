-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.NoLeakHistory — a flat run's allocator history (plan 0.146
-- §5 item 2, NoLeak's `frees-live`, D472).
--
-- The run is `Once.Implementation.Run`'s (`at fs₀ k = exec-flat k prog fs₀`;
-- the notions are restated here, as `Once.Implementation` is imported by
-- `Once.Certified` alone). A run's step `k` either leaves the allocator as it
-- was (the run has stopped) or executes the instruction it fetches.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractTrace)

module Once.Adequacy.NoLeakHistory (FS : FrameSemantics) (prog : AbstractTrace) where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS}
open FlatState using (floc; fpc; falloc)

at : FlatState → ℕ → FlatState
at fs₀ k = exec-flat k prog fs₀

Executes : FlatState → ℕ → AbstractInstr → Set
Executes fs₀ k i = LocState.halted (floc (at fs₀ k)) ≡ false × fetch prog (fpc (at fs₀ k)) ≡ just i

-- a halted run stays where it is
halted-stay : ∀ b fs → LocState.halted (floc fs) ≡ true → exec-flat b prog fs ≡ fs
halted-stay zero    fs h = refl
halted-stay (suc b) fs h = cong (λ x → step-dispatch x b prog fs) h

-- running `a + b` steps is running `a`, then `b`
exec-flat-+ : ∀ a b fs → exec-flat (a + b) prog fs ≡ exec-flat b prog (exec-flat a prog fs)
exec-flat-+ zero    b fs = refl
exec-flat-+ (suc a) b fs = by (LocState.halted (floc fs)) refl
  where
    by : ∀ x → LocState.halted (floc fs) ≡ x
       → step-dispatch (LocState.halted (floc fs)) (a + b) prog fs ≡ exec-flat b prog (step-dispatch (LocState.halted (floc fs)) a prog fs)
    by true  e = trans (cong (λ x → step-dispatch x (a + b) prog fs) e)
                   (sym (trans (cong (λ x → exec-flat b prog (step-dispatch x a prog fs)) e) (halted-stay b fs e)))
    by false e = trans (cong (λ x → step-dispatch x (a + b) prog fs) e)
                   (trans (go (fetch prog (fpc fs)))
                          (sym (cong (λ x → exec-flat b prog (step-dispatch x a prog fs)) e)))
      where
        go : ∀ mi → fetch-dispatch mi (a + b) prog fs ≡ exec-flat b prog (fetch-dispatch mi a prog fs)
        go nothing  = sym (halted-stay b _ refl)
        go (just i) = exec-flat-+ a b (flat-exec-instr i prog fs)

-- ★ step `k`: the run stood (its allocator kept), or it executed what it fetched
one-step : ∀ fs₀ k → (falloc (at fs₀ (suc k)) ≡ falloc (at fs₀ k))
                    ⊎ (Σ AbstractInstr λ i → Executes fs₀ k i × (at fs₀ (suc k) ≡ flat-exec-instr i prog (at fs₀ k)))
one-step fs₀ k = subst P (sym last) (by (LocState.halted (floc x)) refl)
  where
    x = at fs₀ k
    last : at fs₀ (suc k) ≡ exec-flat 1 prog x
    last = trans (cong (λ n → exec-flat n prog fs₀) (Data.Nat.Properties.+-comm 1 k)) (exec-flat-+ k 1 fs₀)
    P : FlatState → Set
    P y = (falloc y ≡ falloc x) ⊎ (Σ AbstractInstr λ i → Executes fs₀ k i × (y ≡ flat-exec-instr i prog x))
    by : ∀ h → LocState.halted (floc x) ≡ h → P (exec-flat 1 prog x)
    by true  e = inj₁ (cong falloc (halted-stay 1 x e))
    by false e = subst (λ y → P y) (sym (cong (λ h → step-dispatch h 0 prog x) e)) (go (fetch prog (fpc x)) refl)
      where
        go : ∀ mi → fetch prog (fpc x) ≡ mi → P (fetch-dispatch mi 0 prog x)
        go nothing  _ = inj₁ refl
        go (just i) f = inj₂ (i , (e , f) , refl)

------------------------------------------------------------------------
-- ★ The allocator's events: what `Once.Implementation.Run` names
------------------------------------------------------------------------

open import Data.Nat using (_<_; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Bool using (_∧_; not; _∨_)
open AllocState using (next-heap-ref; freed; block-size)
open AbstractExec {FS} using (heapRefOf; freeMark-mono)
import Once.Adequacy.NoLeakFrees
module NF = Once.Adequacy.NoLeakFrees FS

Allocates : FlatState → ℕ → ℕ → Set
Allocates fs₀ k r = Σ ℕ (λ n → Executes fs₀ k (instr-alloc-heap n)) × next-heap-ref (falloc (at fs₀ k)) ≡ r

Frees : FlatState → ℕ → ℕ → Set
Frees fs₀ k r = Σ ℕ (λ n → Executes fs₀ k (instr-free-heap n)) × heapRefOf (readReg (LocState.regs (floc (at fs₀ k))) Input1) ≡ just r

Live : FlatState → ℕ → ℕ → Set
Live fs₀ k r = Σ ℕ λ j → (j < k) × Allocates fs₀ j r × (∀ i → j < i → i < k → ¬ Frees fs₀ i r)

module _ (fs₀ : FlatState) where

  -- a block with a size was allocated by an earlier step (the entry's sizes are 0)
  size-hist : (∀ r → block-size (falloc fs₀) r ≡ 0) → ∀ k r → (block-size (falloc (at fs₀ k)) r ≡ 0 → ⊥)
            → Σ ℕ λ j → (j < k) × Allocates fs₀ j r
  size-hist z0 zero    r nz = ⊥-elim (nz (z0 r))
  size-hist z0 (suc k) r nz = by (one-step fs₀ k)
    where
      up : (Σ ℕ λ j → (j < k) × Allocates fs₀ j r) → Σ ℕ λ j → (j < suc k) × Allocates fs₀ j r
      up (j , lt , a) = j , Data.Nat.Properties.m<n⇒m<1+n lt , a
      by : (falloc (at fs₀ (suc k)) ≡ falloc (at fs₀ k))
         ⊎ (Σ AbstractInstr λ i → Executes fs₀ k i × (at fs₀ (suc k) ≡ flat-exec-instr i prog (at fs₀ k)))
         → Σ ℕ λ j → (j < suc k) × Allocates fs₀ j r
      by (inj₁ e) = up (size-hist z0 k r (λ z → nz (trans (cong (λ a → block-size a r) e) z)))
      by (inj₂ (i , ex , e)) = pick (NF.step-size i prog (at fs₀ k) r)
        where
          pick : (block-size (falloc (flat-exec-instr i prog (at fs₀ k))) r ≡ block-size (falloc (at fs₀ k)) r)
               ⊎ (Σ ℕ λ n → (i ≡ instr-alloc-heap n) × (next-heap-ref (falloc (at fs₀ k)) ≡ r))
               → Σ ℕ λ j → (j < suc k) × Allocates fs₀ j r
          pick (inj₁ s) = up (size-hist z0 k r (λ z → nz (trans (cong (λ y → block-size (falloc y) r) e) (trans s z))))
          pick (inj₂ (n , refl , nx)) = k , Data.Nat.Properties.≤-refl , ((n , ex) , nx)

  -- a freed mark stays
  freed-mono : ∀ i k r → i ≤ k → freed (falloc (at fs₀ i)) r ≡ true → freed (falloc (at fs₀ k)) r ≡ true
  freed-mono i zero    r z≤n e = e
  freed-mono i (suc k) r le e = by (Data.Nat.Properties.m≤n⇒m<n∨m≡n le)
    where
      step : freed (falloc (at fs₀ k)) r ≡ true → freed (falloc (at fs₀ (suc k))) r ≡ true
      step e′ = go (one-step fs₀ k)
        where
          go : (falloc (at fs₀ (suc k)) ≡ falloc (at fs₀ k))
             ⊎ (Σ AbstractInstr λ i′ → Executes fs₀ k i′ × (at fs₀ (suc k) ≡ flat-exec-instr i′ prog (at fs₀ k)))
             → freed (falloc (at fs₀ (suc k))) r ≡ true
          go (inj₁ q) = trans (cong (λ a → freed a r) q) e′
          go (inj₂ (i′ , _ , q)) = trans (cong (λ y → freed (falloc y) r) q) (NF.step-freed-mono i′ prog (at fs₀ k) r e′)
      by : (i < suc k) ⊎ (i ≡ suc k) → freed (falloc (at fs₀ (suc k))) r ≡ true
      by (inj₁ lt) = step (freed-mono i k r (Data.Nat.Properties.≤-pred lt) e)
      by (inj₂ refl) = e
