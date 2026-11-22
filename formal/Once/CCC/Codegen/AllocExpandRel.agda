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

------------------------------------------------------------------------
-- The renaming of refs, on locations and values
------------------------------------------------------------------------

ref-of : HeapLocation → ℕ
ref-of hl = HeapRef.ref-id (HeapLocation.heap-ref hl)

rhl : (ℕ → ℕ) → HeapLocation → HeapLocation
rhl ρ hl = heap-loc (mkHeapRef (ρ (ref-of hl))) (HeapLocation.heap-offset hl)

rloc : (ℕ → ℕ) → ValueLocation FS → ValueLocation FS
rloc ρ (AtStack f k)  = AtStack f k
rloc ρ (AtDynamic hl) = AtDynamic (rhl ρ hl)

rv : (ℕ → ℕ) → StoredValue FS → StoredValue FS
rv ρ (SV-Ptr loc)  = SV-Ptr (rloc ρ loc)
rv ρ (SV-Tag n)    = SV-Tag n
rv ρ (SV-Lit p v)  = SV-Lit p v
rv ρ (SV-Code l)   = SV-Code l

-- a block's base pointer, and a record word's location
blk : ℕ → StoredValue FS
blk b = SV-Ptr (AtDynamic (heap-loc (mkHeapRef b) 0))

rec-loc : ℕ → HeapLocation
rec-loc k = heap-loc (mkHeapRef 0) k

------------------------------------------------------------------------
-- The primitive's live blocks
------------------------------------------------------------------------

Live : AllocState {FS} → ℕ → Set
Live al r = r < AllocState.next-heap-ref al × AllocState.freed al r ≡ false

------------------------------------------------------------------------
-- A free list: the chain from a head word, through the blocks' word 0, to the sentinel
------------------------------------------------------------------------

Chain : HeapMem FS → ℕ → List ℕ → StoredValue FS → Set
Chain h σ []       v = v ≡ blk σ
Chain h σ (b ∷ bs) v = v ≡ blk b × Σ (StoredValue FS) λ w → h (heap-loc (mkHeapRef b) 0) ≡ just w × Chain h σ bs w

------------------------------------------------------------------------
-- ★ The relation
------------------------------------------------------------------------

module _ (C : Classes) (P : AbstractTrace) where

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
      r-halt  : LocState.halted (floc gs) ≡ LocState.halted (floc fs)
      r-fault : LocState.faulted (floc gs) ≡ LocState.faulted (floc fs)
      r-left  : LocState.left (floc gs) ≡ LocState.left (floc fs)
      r-log   : LocState.ev-log (floc gs) ≡ LocState.ev-log (floc fs)

      -- data, by the renaming
      r-regs  : ∀ r → readReg (LocState.regs (floc gs)) r ≡ rv ρ (readReg (LocState.regs (floc fs)) r)
      r-clo   : fclosure gs ≡ rv ρ (fclosure fs)
      r-stack : ∀ f k → LocState.stackMem (floc gs) f k ≡ Data.Maybe.map (rv ρ) (LocState.stackMem (floc fs) f k)
      r-heap  : ∀ hl v → Live (falloc fs) (ref-of hl) → LocState.heapMem (floc fs) hl ≡ just v
              → LocState.heapMem (floc gs) (rhl ρ hl) ≡ just (rv ρ v)
      r-size  : ∀ r → Live (falloc fs) r → AllocState.block-size (falloc fs) r ≤ AllocState.block-size (falloc gs) (ρ r)

      -- the renaming's image: injective on the live blocks, apart from the
      -- record, the sentinel and the free lists, below the expanded counter
      r-inj   : ∀ r r′ → Live (falloc fs) r → Live (falloc fs) r′ → ρ r ≡ ρ r′ → r ≡ r′
      r-below : ∀ r → Live (falloc fs) r → 0 < ρ r × ρ r < AllocState.next-heap-ref (falloc gs)
      r-not-σ : ∀ r → Live (falloc fs) r → ¬ ρ r ≡ σ
      r-not-free : ∀ r c b → Live (falloc fs) r → b ∈ lists c → ¬ ρ r ≡ b

      -- the free lists, in the record and the blocks
      r-heads : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                                       × Chain (LocState.heapMem (floc gs)) σ (lists c) v
      r-sent  : LocState.heapMem (floc gs) (heap-loc (mkHeapRef σ) 0) ≡ just (SV-Tag 0)

      -- the two runs' own invariants
      r-cleared : ∀ hl → AllocState.freed (falloc fs) (ref-of hl) ≡ true → LocState.heapMem (floc fs) hl ≡ nothing
      r-nofree  : ∀ r → AllocState.freed (falloc gs) r ≡ false
