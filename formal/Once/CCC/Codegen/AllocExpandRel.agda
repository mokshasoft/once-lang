-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandRel — the expansion's simulation relation (D468, 3c3b).
--
-- A state of the primitive program `P` and one of its expansion are related
-- when the expanded one is the primitive one with its LIVE blocks renamed (`ρ`:
-- the primitive's fresh refs to the expanded run's reused ones) and its freed
-- blocks gathered on the free lists:
--
--   * control: the pc and the return addresses by the pc map (`off`), the frames
--     and the control flags as they are;
--   * data: registers, stack and the closure register by the renaming of
--     values (`rv ρ`: a heap pointer's ref renamed); a live block's cells by
--     `ρ`, its size at most the expanded block's;
--   * the renaming is injective on the live blocks, and misses the record
--     (ref 0), the sentinel, and every block on a free list;
--   * the free lists: the record's head word of each class points along a
--     chain of free blocks (each block's word 0 the next) to the sentinel, whose
--     word is the tag 0;
--   * the primitive side: a freed block's cells are all empty (the clearing
--     free), and the expanded run frees nothing.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandRel {FS : FrameSemantics} where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef; module HeapLocation; module HeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState)
open FlatState
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off)
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rhl; rloc; rv; blk; rec-loc)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)

------------------------------------------------------------------------
-- The primitive's live blocks (ref 0 is the record: never a block of the primitive's)
------------------------------------------------------------------------

Live : AllocState {FS} → ℕ → Set
Live al r = 0 < r × r < AllocState.next-heap-ref al × AllocState.freed al r ≡ false

------------------------------------------------------------------------
-- A free list: the chain from a head word, through the blocks' word 0, to the sentinel
------------------------------------------------------------------------

Chain : HeapMem FS → ℕ → List ℕ → StoredValue FS → Set
Chain h σ []       v = v ≡ blk σ
Chain h σ (b ∷ bs) v = v ≡ blk b × Σ (StoredValue FS) λ w → h (heap-loc (mkHeapRef b) 0) ≡ just w × Chain h σ bs w

------------------------------------------------------------------------
-- ★ The relation
------------------------------------------------------------------------

-- `Sz`: the program's block sizes (its allocations' and frees')
module _ (C : Classes) (P : AbstractTrace) (Sz : ℕ → Set) where

  record Rel (fs gs : FlatState) : Set where
    field
      -- the renaming, the sentinel, the free lists
      ρ     : ℕ → ℕ
      σ     : ℕ
      lists : ℕ → List ℕ

      -- control
      r-pc    : fpc gs ≡ off C 0 P (fpc fs)
      r-ret   : fret gs ≡ map (off C 0 P) (fret fs)
      r-link  : flink gs ≡ Data.Maybe.map (off C 0 P) (flink fs)
      r-frame : AllocState.current-frame (falloc gs) ≡ AllocState.current-frame (falloc fs)
      r-saved : AllocState.saved-frames (falloc gs) ≡ AllocState.saved-frames (falloc fs)
      r-slots : AllocState.frame-slots (falloc gs) ≡ AllocState.frame-slots (falloc fs)
      r-next-slot : AllocState.next-slot (falloc gs) ≡ AllocState.next-slot (falloc fs)

      -- the renaming's image: injective on the live blocks, apart from the
      -- record, the sentinel and the free lists, below the expanded counter
      r-inj   : ∀ r r′ → Live (falloc fs) r → Live (falloc fs) r′ → ρ r ≡ ρ r′ → r ≡ r′

      -- data, by the renaming (`LRel`: registers, stack, the live heap, a held
      -- cell's block live, the flags and the log)
      r-loc   : L.LRel ρ (Live (falloc fs)) r-inj (floc fs) (floc gs)
      r-clo   : fclosure gs ≡ rv ρ (fclosure fs)
      -- every block handed out, at least its size (a reused block is its class's size)
      r-size  : ∀ r → r < AllocState.next-heap-ref (falloc fs) → AllocState.block-size (falloc fs) r ≤ AllocState.block-size (falloc gs) (ρ r)
      r-below : ∀ r → Live (falloc fs) r → 0 < ρ r × ρ r < AllocState.next-heap-ref (falloc gs)
      r-not-σ : ∀ r → Live (falloc fs) r → ¬ ρ r ≡ σ
      r-not-free : ∀ r c b → Live (falloc fs) r → b ∈ lists c → ¬ ρ r ≡ b

      -- the free lists, in the record and the blocks
      r-heads : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                                       × Chain (LocState.heapMem (floc gs)) σ (lists c) v
      r-sent  : LocState.heapMem (floc gs) (heap-loc (mkHeapRef σ) 0) ≡ just (SV-Tag 0)

      -- the two runs' own invariants
      r-nofree  : ∀ r → AllocState.freed (falloc gs) r ≡ false
      -- the record is no block of the primitive's
      r-rec0    : AllocState.block-size (falloc fs) 0 ≡ 0
      -- a live block's renamed block holds its class's size; a free block, every size of its class
      r-csize   : ∀ r → Live (falloc fs) r → bsz C (AllocState.block-size (falloc fs) r) ≤ AllocState.block-size (falloc gs) (ρ r)
      r-lsize   : ∀ c b → b ∈ lists c → ∀ k → Sz k → cls C k ≡ c → bsz C k ≤ AllocState.block-size (falloc gs) b
      -- a block not handed out has size 0 (so a gate passed only inside a handed-out block)
      r-unsized : ∀ r → AllocState.next-heap-ref (falloc fs) ≤ r → AllocState.block-size (falloc fs) r ≡ 0
