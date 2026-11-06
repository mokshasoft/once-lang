-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Machine.FlatAlloc
--
-- plan 0.123 B.4 α: WHAT AN ALLOCATION OF `n` WORDS DOES to the allocator, in
-- the vocabulary of the value relation (D386): the fresh block was not live,
-- is live after, has `n` cells (each in it), and every block live before
-- keeps its size and stays live.
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)

module Once.CCC.Machine.FlatAlloc {FS : FrameSemantics} where

open import Data.Nat using (ℕ; suc; _<_; _≟_)
open import Data.Nat.Properties using (n<1+n; m<n⇒m<1+n; <-irrefl; <⇒<ᵇ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Bool
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Once.Memory.HeapAddress using (HeapRef; mkHeapRef; heap-loc)
open import Once.CCC.Machine.Locations using (ValueLocation; AtStack; AtDynamic)
open import Once.CCC.Machine.SMCore
open AllocState using (next-heap-ref; block-size)
open import Once.CCC.Machine.Allocation using (module FrontierInvariant)
open FrontierInvariant {FS} using (BeforeFrontier)
open import Once.CCC.Machine.ValueRel
open ClosureWellFormedBase {FS} using (Live; InBlk; BlocksKept)

-- the allocator after `instr-alloc-heap n`, and the block it hands out
alloc-after : ℕ → AllocState {FS} → AllocState {FS}
alloc-after n alloc = record alloc { next-heap-ref = suc (next-heap-ref alloc)
                                   ; block-size = size-with n (next-heap-ref alloc) (block-size alloc) }

fresh-ref : AllocState {FS} → HeapRef
fresh-ref alloc = mkHeapRef (next-heap-ref alloc)

alloc-exec : ∀ (n : ℕ) (s : LocState FS) (alloc : AllocState {FS})
           → AbstractExec.exec-abstract {FS} (instr-alloc-heap n) s alloc
             ≡ (record s { regs = writeReg (LocState.regs s) Output (SV-Ptr (AtDynamic (heap-loc (fresh-ref alloc) 0))) }
               , alloc-after n alloc)
alloc-exec n s alloc = refl

-- what was live stays live
alloc-bft : ∀ n (alloc : AllocState {FS}) l → Live alloc l → Live (alloc-after n alloc) l
alloc-bft n alloc (AtDynamic hl) (BeforeFrontier.heap-before p) = BeforeFrontier.heap-before (m<n⇒m<1+n p)

-- the fresh block is live after, and was not before
alloc-live : ∀ n (alloc : AllocState {FS}) o → Live (alloc-after n alloc) (AtDynamic (heap-loc (fresh-ref alloc) o))
alloc-live n alloc o = BeforeFrontier.heap-before (n<1+n _)

alloc-fresh : ∀ (alloc : AllocState {FS}) o → Live alloc (AtDynamic (heap-loc (fresh-ref alloc) o)) → ⊥
alloc-fresh alloc o (BeforeFrontier.heap-before p) = <-irrefl refl p

-- a live block keeps its size
alloc-bk : ∀ n (alloc : AllocState {FS}) → BlocksKept alloc (alloc-after n alloc)
alloc-bk n alloc (AtDynamic (heap-loc (mkHeapRef r) o)) (BeforeFrontier.heap-before p) ib
  with r ≟ next-heap-ref alloc
... | yes e = ⊥-elim (<-irrefl e p)
... | no  _ = ib

private
  T→≡ : ∀ {b} → Data.Bool.T b → b ≡ Data.Bool.true
  T→≡ {Data.Bool.true} _ = refl

-- the fresh block has `n` cells
alloc-in : ∀ n (alloc : AllocState {FS}) o → o < n → InBlk (alloc-after n alloc) (AtDynamic (heap-loc (fresh-ref alloc) o))
alloc-in n alloc o o<n with next-heap-ref alloc ≟ next-heap-ref alloc
... | yes _ = T→≡ (<⇒<ᵇ o<n)
... | no ne = ⊥-elim (ne refl)
