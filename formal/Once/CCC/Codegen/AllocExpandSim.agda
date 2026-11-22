-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpandSim — the expansion's simulation, a step at a time (D468, 3c3b).
--
-- `core-straight`: a step of the primitive program that keeps its allocator
-- and moves to the next instruction, done by the one instruction it expands to,
-- keeps the relation, given the step's memory relation (`LRel`) and that the
-- expanded heap changed only at live blocks' renamed cells (so the record, the
-- sentinel and the free blocks are as they were).
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Codegen.AllocExpandSim {FS : FrameSemantics} where

open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
import Data.Nat.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Once.Memory.HeapAddress using (HeapLocation; heap-loc; mkHeapRef)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Machine.Flat using (module FlatMachine)
open FlatMachine {FS} using (FlatState; module FlatState)
open FlatState
open import Once.CCC.Codegen.AllocExpand
open Classes
open import Once.CCC.Codegen.AllocExpandRen {FS} using (ref-of; rhl; rv; blk; rec-loc)
open import Once.CCC.Codegen.AllocExpandRel {FS} using (Rel; module Rel; Live; Chain)
open import Once.CCC.Codegen.AllocExpandStep {FS} using (module L)
open import Once.CCC.Codegen.AllocExpandPc {FS} using (off)

module _ (C : Classes) (P : AbstractTrace) where
  open Rel

  -- a chain read through a heap that agrees on its cells
  chain-frame : ∀ (h h′ : HeapMem FS) σ (bs : List ℕ) v
              → (∀ b → b ∈ bs → h′ (heap-loc (mkHeapRef b) 0) ≡ h (heap-loc (mkHeapRef b) 0))
              → Chain h σ bs v → Chain h′ σ bs v
  chain-frame h h′ σ []       v same c = c
  chain-frame h h′ σ (b ∷ bs) v same (e , w , hw , c) =
    e , w , trans (same b (here refl)) hw , chain-frame h h′ σ bs w (λ b′ m → same b′ (there m)) c

  -- ★ a step that keeps the allocator and moves on
  core-straight : ∀ {fs gs} (R : Rel C P fs gs) (A B : LocState FS)
                → L.LRel (ρ R) (Live (falloc fs)) (r-inj R) A B
                → (∀ q → (∀ r → Live (falloc fs) r → ¬ ρ R r ≡ ref-of q) → LocState.heapMem B q ≡ LocState.heapMem (floc gs) q)
                → off C 0 P (suc (fpc fs)) ≡ suc (fpc gs)
                → Rel C P (record fs { floc = A ; fpc = suc (fpc fs) }) (record gs { floc = B ; fpc = suc (fpc gs) })
  core-straight {fs} {gs} R A B LR frame pc = record
    { ρ = ρ R ; σ = σ R ; lists = lists R
    ; r-pc = sym pc
    ; r-ret = r-ret R ; r-link = r-link R
    ; r-frame = r-frame R ; r-saved = r-saved R ; r-slots = r-slots R ; r-next-slot = r-next-slot R
    ; r-inj = r-inj R
    ; r-loc = LR
    ; r-clo = r-clo R
    ; r-size = r-size R
    ; r-below = r-below R ; r-not-σ = r-not-σ R ; r-not-free = r-not-free R
    ; r-heads = heads′
    ; r-sent = trans (frame (heap-loc (mkHeapRef (σ R)) 0) (λ r lv e → r-not-σ R r lv e)) (r-sent R)
    ; r-nofree = r-nofree R
    ; r-unsized = r-unsized R }
    where
      -- the record's words: no live block is renamed to ref 0
      rec-free : ∀ k → LocState.heapMem B (rec-loc k) ≡ LocState.heapMem (floc gs) (rec-loc k)
      rec-free k = frame (rec-loc k) (λ r lv e → Data.Nat.Properties.<-irrefl (sym e) (proj₁ (r-below R r lv)))
      heads′ : ∀ c → c < count C → Σ (StoredValue FS) λ v → LocState.heapMem B (rec-loc (head-word c)) ≡ just v
                                                         × Chain (LocState.heapMem B) (σ R) (lists R c) v
      heads′ c c< = hd (r-heads R c c<)
        where
          hd : (Σ (StoredValue FS) λ v → LocState.heapMem (floc gs) (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem (floc gs)) (σ R) (lists R c) v)
             → Σ (StoredValue FS) λ v → LocState.heapMem B (rec-loc (head-word c)) ≡ just v
                                     × Chain (LocState.heapMem B) (σ R) (lists R c) v
          hd (v , e , ch) = v , trans (rec-free (head-word c)) e
                          , chain-frame (LocState.heapMem (floc gs)) (LocState.heapMem B) (σ R) (lists R c) v
                              (λ b m → frame (heap-loc (mkHeapRef b) 0) (λ r lv e′ → r-not-free R r c b lv m e′)) ch
