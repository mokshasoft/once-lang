-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.Moves — plan 0.146 B1.4b, `LowerSim` layer (1): what the
-- lowering's word moves do on the flat machine.
--
-- `Seg prog pc tr`: the trace `tr` sits in `prog` at `pc`. A move of `n`
-- words is `2n` steps, each a `flat-step-straight` (the program is not
-- consulted): a load into `Output`, a store from it. Its end state has the
-- words moved and every other slot, every other frame, the heap, `Input1`
-- and the control state as before.
--
-- Here: one load and one store of the current frame, by computation, and
-- what a store leaves in each slot.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.CCC.FrameSemantics using (FrameSemantics; module FrameSemantics)
open import Once.CCC.Machine.Locations using (AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)

module Once.LinCore.Moves {FS : FrameSemantics} where

open FlatMachine {FS}
open FrameSemantics FS using (Frame; _≟F_)
open MemOps {FS}
open LocState
open AllocState using (current-frame)

------------------------------------------------------------------------
-- 1. A TRACE AT A PC.
------------------------------------------------------------------------

Seg : AbstractTrace → ℕ → AbstractTrace → Set
Seg prog pc []       = ⊤
Seg prog pc (i ∷ is) = fetch prog pc ≡ just i × Seg prog (suc pc) is

Seg-++ˡ : ∀ prog pc xs ys → Seg prog pc (xs ++ ys) → Seg prog pc xs
Seg-++ˡ prog pc []       ys s       = tt
Seg-++ˡ prog pc (x ∷ xs) ys (f , s) = f , Seg-++ˡ prog (suc pc) xs ys s

Seg-++ʳ : ∀ prog pc xs ys → Seg prog pc (xs ++ ys) → Seg prog (pc + length xs) ys
Seg-++ʳ prog pc []       ys s       rewrite +-identityʳ pc = s
Seg-++ʳ prog pc (x ∷ xs) ys (f , s) rewrite +-suc pc (length xs) = Seg-++ʳ prog (suc pc) xs ys s

------------------------------------------------------------------------
-- 2. ONE LOAD, ONE STORE of the current frame.
------------------------------------------------------------------------

-- the current frame's slot
slot : FlatState → ℕ → Maybe (StoredValue FS)
slot fs k = stackMem (floc fs) (current-frame (falloc fs)) k

-- a load of a defined slot: `Output` holds its word
load-step : ∀ (fs : FlatState) a {v} → slot fs a ≡ just v
          → flat-step-straight (load-from-slot a) fs
            ≡ record fs { floc = record (floc fs) { regs = writeReg (regs (floc fs)) Output v } ; fpc = suc (fpc fs) }
load-step fs a e =
  cong (λ m → record fs { floc   = Data.Product.proj₁ (exec-load-from-slot-with-value m (floc fs) (falloc fs))
                        ; falloc = Data.Product.proj₂ (exec-load-from-slot-with-value m (floc fs) (falloc fs))
                        ; fpc    = suc (fpc fs) }) e
  where import Data.Product
        open AbstractExec {FS} using (exec-load-from-slot-with-value)

-- a store: the slot holds `Output`'s word
store-step : ∀ (fs : FlatState) b
           → flat-step-straight (store-at-slot b) fs
             ≡ record fs { floc = writeLoc (floc fs) (AtStack (current-frame (falloc fs)) b) (readReg (regs (floc fs)) Output)
                         ; fpc = suc (fpc fs) }
store-step fs b = refl

-- what a store to the current frame leaves: the slot written, the rest as before
private
  ws-same : ∀ (mem : StackMem FS) f k v → writeStackMem mem f k v f k ≡ just v
  ws-same mem f k v with f ≟F f | k ≟ k
  ... | yes _ | yes _ = refl
  ... | yes _ | no ne = ⊥-elim (ne refl)
  ... | no ne | _     = ⊥-elim (ne refl)

  ws-other : ∀ (mem : StackMem FS) f k v k′ → ¬ k ≡ k′ → writeStackMem mem f k v f k′ ≡ mem f k′
  ws-other mem f k v k′ ne with f ≟F f | k ≟ k′
  ... | yes _ | yes e = ⊥-elim (ne e)
  ... | yes _ | no _  = refl
  ... | no _  | _     = refl

  ws-frame : ∀ (mem : StackMem FS) f k v f′ k′ → ¬ f ≡ f′ → writeStackMem mem f k v f′ k′ ≡ mem f′ k′
  ws-frame mem f k v f′ k′ ne with f ≟F f′
  ... | yes e = ⊥-elim (ne e)
  ... | no _  = refl

store-same : ∀ (s : LocState FS) f k v → stackMem (writeLoc s (AtStack f k) v) f k ≡ just v
store-same s f k v = ws-same (stackMem s) f k v

store-other : ∀ (s : LocState FS) f k v k′ → ¬ k ≡ k′ → stackMem (writeLoc s (AtStack f k) v) f k′ ≡ stackMem s f k′
store-other s f k v k′ ne = ws-other (stackMem s) f k v k′ ne

store-frame : ∀ (s : LocState FS) f k v f′ k′ → ¬ f ≡ f′ → stackMem (writeLoc s (AtStack f k) v) f′ k′ ≡ stackMem s f′ k′
store-frame s f k v f′ k′ ne = ws-frame (stackMem s) f k v f′ k′ ne
