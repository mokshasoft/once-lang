-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.BlockLayout — WHERE EACH BLOCK SITS IN THE LINKED IMAGE.
--
-- Plan 0.91 S5 / plan 0.93 S4, the SPAN half. `entry-blocks` asks for two
-- things about every block the emitter produced:
--
--     BlockAt prog (lbl , b , t) =
--       ∃[ j ] ((find-thunk prog lbl ≡ just j) × SpanAt prog j (block-layout blk))
--
-- a PLACEMENT (the block's laid-out text is a contiguous span at `j`) and a
-- RESOLUTION (`find-thunk` finds it THERE). This module proves the placement.
-- It is pure list arithmetic: `link u = entry u ++ c-ret ∷ blocks-layout (blocks u)`
-- and `blocks-layout (b ∷ bs) = block-layout b ++ blocks-layout bs`, so every
-- block's layout IS a `++`-fragment at an offset the list structure computes.
--
-- The RESOLUTION half is a different kind of fact — it needs `find-thunk`'s scan
-- to pass every earlier `c-thunk` without matching, i.e. that the entry mints no
-- `c-thunk` and that the blocks' labels are pairwise distinct. That is the
-- `ThunkScope` obligation, and it is deliberately NOT here: mixing a layout
-- lemma with a provenance one is how `BlockAt` came to be guessed rather than
-- derived (plan 0.91 §3 S2's own note: "expect to revise it").
--
-- `SpanAt` is spelled out rather than imported: it lives inside
-- `IRObsCorrect.Interface`'s `FrameSemantics`-parameterised `Core`, but the
-- notion is pure fetch-agreement and depends on no frame semantics.
------------------------------------------------------------------------

module Once.CCC.Codegen.BlockLayout where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Once.CCC.Machine.SMCore
  using (block-layout; blocks-layout; AbstractTrace; AbstractInstr; LabelId)
open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.Flat using (module FlatMachine)
open import Once.CCC.Label using (_≡ᵇᴵ_; ≡ᵇᴵ-refl)
open import Once.CCC.Machine.SMCore using (instr-ctrl; c-thunk)

------------------------------------------------------------------------
-- Fetch agreement, spelled out (= `Interface.Core.SpanAt`).
--
-- `fetch` lives inside `FlatMachine {FS}`, so this module carries the same
-- parameter its consumers do; nothing below actually inspects `FS`.
------------------------------------------------------------------------

module Layout {FS : FrameSemantics} where
  open FlatMachine {FS} using (fetch; find-thunk; ft-go; ft-at; ft-match; thunk-of?; ft-go-++-miss)


  Span : AbstractTrace → ℕ → AbstractTrace → Set
  Span prog base t = ∀ (k : ℕ) (i : AbstractInstr) → fetch t k ≡ just i → fetch prog (k + base) ≡ just i

  -- `fetch` skips a prefix of its own length. The `FlatStepLemmas` twin, restated
  -- here so this module stands alone.
  fetch-skip : ∀ (xs ys : AbstractTrace) (j : ℕ) → fetch (xs ++ ys) (length xs + j) ≡ fetch ys j
  fetch-skip []        ys j = refl
  fetch-skip (i ∷ xs') ys j = fetch-skip xs' ys j

  -- A fragment is a span of itself extended on the RIGHT, at offset 0.
  span-head : ∀ (t post : AbstractTrace) → Span (t ++ post) 0 t
  span-head []          post k        i ()
  span-head (x ∷ t')    post zero     i refl = refl
  span-head (x ∷ t')    post (suc k)  i eq   = span-head t' post k i eq

  -- A span survives a prefix: shift the offset by the prefix's length.
  span-shift : ∀ (pre rest t : AbstractTrace) (d : ℕ)
             → Span rest d t → Span (pre ++ rest) (length pre + d) t
  span-shift pre rest t d sp k i eq =
    subst (λ n → fetch (pre ++ rest) n ≡ just i)
          (trans (cong (length pre +_) refl) (sym (+-assoc-lemma k (length pre) d)))
          (trans (fetch-skip pre rest (k + d)) (sp k i eq))
    where
      -- `k + (length pre + d) ≡ length pre + (k + d)`
      +-assoc-lemma : ∀ a b c → a + (b + c) ≡ b + (a + c)
      +-assoc-lemma a b c =
        trans (sym (+-assoc a b c))
              (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

  ------------------------------------------------------------------------
  -- THE PLACEMENT LEMMA.
  --
  -- Every block in `bs` is a contiguous span of `blocks-layout bs`, at the
  -- offset its predecessors' layouts occupy. Induction on the list: the head
  -- sits at 0 (`span-head`), and a tail member sits where it sat in the tail,
  -- shifted past the head's layout (`span-shift`).
  --
  -- `All` rather than a membership hypothesis, so it composes directly with
  -- `BlocksAt prog bs = All (BlockAt prog) bs`.
  ------------------------------------------------------------------------

  blocks-placed : ∀ (bs : List (LabelId × ℕ × AbstractTrace))
                → All (λ blk → ∃[ d ] Span (blocks-layout bs) d (block-layout blk)) bs
  blocks-placed []         = []
  blocks-placed (b ∷ bs)   =
    (0 , subst (λ n → Span (block-layout b ++ blocks-layout bs) n (block-layout b))
               refl (span-head (block-layout b) (blocks-layout bs)))
    ∷ All-map (λ {blk} (d , sp) →
         (length (block-layout b) + d)
         , span-shift (block-layout b) (blocks-layout bs) (block-layout blk) d sp)
      (blocks-placed bs)

  -- …and in the LINKED image: `link u = entry ++ c-ret ∷ blocks-layout (blocks u)`,
  -- so every block is a span of the whole program, past that prefix.
  blocks-placed-linked : ∀ (pre : AbstractTrace) (bs : List (LabelId × ℕ × AbstractTrace))
                       → All (λ blk → ∃[ d ] Span (pre ++ blocks-layout bs) d (block-layout blk)) bs
  blocks-placed-linked pre bs =
    All-map (λ {blk} (d , sp) →
        (length pre + d) , span-shift pre (blocks-layout bs) (block-layout blk) d sp)
      (blocks-placed bs)

  ------------------------------------------------------------------------
  -- THE RESOLUTION HALF, reduced to ONE hypothesis.
  --
  -- `find-thunk` scans for the first `c-thunk` carrying the target label. A
  -- block's layout BEGINS with exactly that marker (`block-layout (lbl , b , t)
  -- = instr-ctrl (c-thunk lbl b) ∷ t ++ instr-ctrl (c-ret b) ∷ []`), so the scan
  -- lands on it as soon as it reaches the block — the only question is whether
  -- anything EARLIER matched first.
  --
  -- `ft-go-++-miss` (Flat.agda:240) already skips a prefix the scan misses, and
  -- its hypothesis is the weakest form: `ft-go pre target 0 ≡ nothing`, "the
  -- scan fails on the prefix", which its own comment calls "the one a caller can
  -- actually produce". So the whole resolution half reduces to producing THAT,
  -- and that is the `ThunkScope` obligation — the entry mints no `c-thunk` for
  -- this label, and no earlier block carries it.
  ------------------------------------------------------------------------

  -- The scan HITS a block's own marker immediately.
  ft-hit : ∀ (lbl : LabelId) (b : ℕ) (rest : AbstractTrace) (i : ℕ)
         → ft-go (instr-ctrl (c-thunk lbl b) ∷ rest) lbl i ≡ just i
  ft-hit lbl b rest i rewrite ≡ᵇᴵ-refl lbl = refl

  -- …and therefore resolves to the block's offset, GIVEN the miss.
  block-resolves : ∀ (pre : AbstractTrace) (lbl : LabelId) (b : ℕ)
                     (t post : AbstractTrace)
                 → ft-go pre lbl 0 ≡ nothing
                 → find-thunk (pre ++ block-layout (lbl , b , t) ++ post) lbl
                   ≡ just (length pre + 0)
  block-resolves pre lbl b t post miss =
    trans (ft-go-++-miss pre (block-layout (lbl , b , t) ++ post) lbl 0 miss)
          (ft-hit lbl b _ (length pre + 0))
