-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.AllocExpand — the cell allocator as abstract code (D468).
--
-- Plan 0.146 B1.6 item 3c2. `expand` takes a flat program whose allocations and
-- frees are the machine's primitives (`instr-alloc-heap k` a fresh block,
-- `instr-free-heap k` its block given back) and lowers them to abstract code over
-- free lists in the abstract heap, so no allocator is written or proved per arch:
--
--   * the RECORD (the reserved ref 0, `load-rec`/`store-rec`): word 0 the
--     frontier (per arch; the flat bump is `next-heap-ref`), words 1 and 2
--     scratch, word `3 + c` the head of class `c`'s list;
--   * an empty list is a pointer to a one-cell SENTINEL block whose word is
--     `SV-Tag 0`, so emptiness is `c-branch-tag-zero` on `*Input1`; a free block's
--     first word links the next (a pointer: never a tag);
--   * alloc pops its class's head, or bumps the frontier by the class's block
--     size; free pushes the block on its class's list;
--   * the start (after `c-start`) allocates the sentinel and points every head
--     at it.
--
-- Every expansion keeps the registers the primitive keeps (alloc writes Output
-- only, free nothing): Output and Input1 are saved in the scratch words and put
-- back, so the simulation (3c3) relates the registers exactly.
--
-- Two allocators are two choices of `Classes` (D468 amended): `--alloc=slab`
-- (one class per node size, each its exact size) and `--alloc=pool` (one class,
-- the largest node size). The pass runs before the room checks, which count the
-- bump at the class's size.
------------------------------------------------------------------------

module Once.CCC.Codegen.AllocExpand where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; instr-ctrl; instr-alloc-heap; instr-free-heap; instr-load-tag-lit
        ; load-rec; store-rec; load-at; store-at; mov-to-input; mov-to-output
        ; c-label; c-jmp; c-branch-tag-zero; c-start; c-call-fn; c-entry; c-ret)
open import Once.CCC.Label using (LabelId; mkLabelId; module LabelId; e-fn)
open import Data.Bool using (Bool; true; false)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Once.Target.Symbol using (showNat)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Name using (canonical; CanonicalName)

------------------------------------------------------------------------
-- The allocator's choice: which list serves a block size, and the size it bumps
------------------------------------------------------------------------

record Classes : Set where
  field
    count : ℕ          -- the number of free lists
    cls   : ℕ → ℕ      -- a block size's list (below `count` for the program's sizes)
    bsz   : ℕ → ℕ      -- the size a block of that size is allocated at (at least it)
open Classes

-- the record's words
w-s1 w-s2 : ℕ
w-s1 = 1
w-s2 = 2

head-word : ℕ → ℕ
head-word c = 3 + c

-- the record's size: frontier, two scratch words, one head per list
rec-words : Classes → ℕ
rec-words C = 3 + count C

------------------------------------------------------------------------
-- Labels: the expansion's own, apart from every image label by their owner
-- (an image's is a block's name, `LinCore.Lower.jl`/`tl`), one pair per
-- allocation site at indices `2·site` and `2·site + 1` (an empty path, so
-- their symbols read back as every image label's: `LabelSymInj`)
------------------------------------------------------------------------

alloc-owner = canonical ("once-alloc" ∷ [])

alloc-label : ℕ → ℕ → LabelId
alloc-label site n = mkLabelId alloc-owner [] (n + (site + site))

lb-bump lb-done : ℕ → LabelId
lb-bump site = alloc-label site 0
lb-done site = alloc-label site 1

-- an image's label: not the expansion's owner
ImgL : LabelId → Set
ImgL m = LabelId.owner m ≡ alloc-owner → ⊥

-- one of a site's two labels
SiteL : LabelId → ℕ → Set
SiteL L s = Σ ℕ λ b → (b ≤ 1) × (L ≡ alloc-label s b)

------------------------------------------------------------------------
-- The expansions
------------------------------------------------------------------------

module _ (C : Classes) where

  -- alloc of size `k` at `site` (Output := the block; Input1 kept)
  alloc-code : ℕ → ℕ → AbstractTrace
  alloc-code site k =
      mov-to-output ∷ store-rec w-s1                         -- save Input1
    ∷ load-rec h ∷ mov-to-input                              -- Input1 := the head
    ∷ instr-ctrl (c-branch-tag-zero (lb-bump site))          -- the sentinel: the list is empty
    ∷ load-at 0 ∷ store-rec h                                -- head := the block's link
    ∷ mov-to-output ∷ store-rec w-s2                         -- the block, aside
    ∷ load-rec w-s1 ∷ mov-to-input                           -- Input1 back
    ∷ load-rec w-s2                                          -- Output := the block
    ∷ instr-ctrl (c-jmp (lb-done site))
    ∷ instr-ctrl (c-label (lb-bump site))
    ∷ load-rec w-s1 ∷ mov-to-input                           -- Input1 back
    ∷ instr-alloc-heap (bsz C k)                             -- the frontier's next block
    ∷ instr-ctrl (c-label (lb-done site))
    ∷ []
    where h = head-word (cls C k)

  -- free of a size-`k` block (Input1 := it; Output and Input1 kept)
  free-code : ℕ → AbstractTrace
  free-code k =
      store-rec w-s1                                         -- save Output
    ∷ load-rec h ∷ store-at 0                                -- the block's link := the head
    ∷ mov-to-output ∷ store-rec h                            -- head := the block
    ∷ load-rec w-s1                                          -- Output back
    ∷ []
    where h = head-word (cls C k)

  -- the start's set-up: the sentinel, every head at it (Output and Input1 kept)
  heads : ℕ → AbstractTrace
  heads zero    = []
  heads (suc c) = store-rec (head-word c) ∷ heads c

  setup : AbstractTrace
  setup =
      store-rec w-s1 ∷ mov-to-output ∷ store-rec w-s2        -- save Output, Input1
    ∷ instr-alloc-heap 1                                     -- the sentinel
    ∷ heads (count C)
    ++ mov-to-input ∷ instr-load-tag-lit 0 ∷ store-at 0      -- its word: the tag 0
    ∷ load-rec w-s2 ∷ mov-to-input                           -- Input1 back
    ∷ load-rec w-s1                                          -- Output back
    ∷ []

  -- one instruction at its site (its index in the program)
  expand-at : ℕ → AbstractInstr → AbstractTrace
  expand-at site (instr-alloc-heap k)     = alloc-code site k
  expand-at site (instr-free-heap k)      = free-code k
  expand-at site (instr-ctrl (c-start b)) = instr-ctrl (c-start b) ∷ setup
  {-# CATCHALL #-}
  expand-at site i                        = i ∷ []

  expand-from : ℕ → AbstractTrace → AbstractTrace
  expand-from site []      = []
  expand-from site (i ∷ t) = expand-at site i ++ expand-from (suc site) t

  expand : AbstractTrace → AbstractTrace
  expand = expand-from 0

------------------------------------------------------------------------
-- ★ D480: THE ALLOCATOR AS A CALL, as the expansion of an OUTLINED program.
-- `outline ks P` is `P` with each allocation and free a call, in place, and one
-- primitive alloc and free routine per size of `ks` right after the start,
-- jumped over (`c-jmp skip-label … c-label skip-label`): the program's own code
-- keeps its order and its end, shifted by the routines' length. Its expansion
-- (`expand C (outline ks P)`) is the call mode: each routine's primitive becomes
-- the inline code once. The routines' names lead every part with a non-digit,
-- as the symbols' read-back needs (`LabelSymInj.GoodL`); the skip label's owner
-- is no block's and not the expansion's (`ImgL`).
------------------------------------------------------------------------

alloc-fn free-fn : ℕ → CanonicalName
alloc-fn k = canonical ("once-alloc" ∷ ("a" ++ˢ showNat k) ∷ [])
free-fn  k = canonical ("once-alloc" ∷ ("f" ++ˢ showNat k) ∷ [])

-- a site, called
site-call : AbstractInstr → AbstractInstr
site-call (instr-alloc-heap k) = instr-ctrl (c-call-fn (alloc-fn k))
site-call (instr-free-heap k)  = instr-ctrl (c-call-fn (free-fn k))
{-# CATCHALL #-}
site-call i                    = i

-- a size's two primitive routines
prim-routine : ℕ → AbstractTrace
prim-routine k =
    instr-ctrl (c-entry (e-fn (alloc-fn k)) 0) ∷ instr-alloc-heap k ∷ instr-ctrl (c-ret 0)
  ∷ instr-ctrl (c-entry (e-fn (free-fn k)) 0)  ∷ instr-free-heap k  ∷ instr-ctrl (c-ret 0) ∷ []

prim-routines : List ℕ → AbstractTrace
prim-routines []       = []
prim-routines (k ∷ ks) = prim-routine k ++ prim-routines ks

skip-label : LabelId
skip-label = mkLabelId (canonical ("once-outline" ∷ [])) [] 0

-- the routines, jumped over
skip : List ℕ → AbstractTrace
skip ks = instr-ctrl (c-jmp skip-label) ∷ prim-routines ks ++ instr-ctrl (c-label skip-label) ∷ []

-- the start, the routines, then the program's own code with its sites called
outline : List ℕ → AbstractTrace → AbstractTrace
outline ks []      = []
outline ks (i ∷ T) = i ∷ skip ks ++ map site-call T

-- the mode: inline (`--inline-alloc`) or by call (the default), over the program's sizes `ks`
expandₘ : Bool → Classes → List ℕ → AbstractTrace → AbstractTrace
expandₘ true  C ks P = expand C P
expandₘ false C ks P = expand C (outline ks P)
