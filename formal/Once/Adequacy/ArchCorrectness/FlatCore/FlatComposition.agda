-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
--
-- THE BLOCK-OFFSET MACHINERY, arch-generic (Plan 0.65 G1b, 2026-08-11).
--
-- Each abstract instruction lowers to a contiguous BLOCK of machine
-- instructions (1 for most, 2 for `alloc-heap`, …), so the machine pc is NOT
-- the flat pc — it is `blk-off prog flat-pc`, the sum of block lengths before
-- it. Everything here is about that arithmetic and about the label scan
-- stepping over blocks; none of it is about an instruction SET.
--
-- WHAT THE ARCH SUPPLIES, and why it is this and not its constructors.
-- x86-64's version of this module spent 22 clauses proving one thing: that a
-- block containing no label is skipped by `find-label-go`. It had to enumerate
-- every `Instr` constructor because `find-label-go`'s catch-all does not reduce
-- on a variable instruction. That enumeration is a fact about an ISA's
-- instruction set — it cannot be generalised away — but it does not belong in
-- the correspondence. So the core asks for the CONSEQUENCE instead:
--
--     is-label? : Instr → Bool
--     skip-law  : is-label? i ≡ false
--               → find-label-go t (i ∷ rest) xi ≡ find-label-go t rest (suc xi)
--
-- and `find-label-go-skip` becomes a three-line induction. Each arch discharges
-- `skip-law` once, next to its own instruction type, where the case split
-- belongs. (`ArithSimCore`'s rule, third application in this plan:
-- parameterise over what holds AFTER the step, never over how it is built.)
------------------------------------------------------------------------

open import Once.CCC.FrameSemantics using (FrameSemantics)
open import Once.CCC.Machine.SMCore using (AbstractInstr; AbstractTrace)
open import Once.CCC.Label using (Label)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Once.Adequacy.ArchCorrectness.FlatCore.FlatComposition
  (FS : FrameSemantics)
  -- the machine's instruction type and the emitter into it
  (Instr : Set)
  (compile-abstract : AbstractInstr → List Instr)
  (compile-trace : AbstractTrace → List Instr)
  (ct-cons : ∀ i is → compile-trace (i ∷ is) ≡ compile-abstract i ++ compile-trace is)
  -- the machine's instruction fetch, by its three defining equations (`refl`
  -- at every arch — they all index a list)
  (mfetch      : List Instr → ℕ → Maybe Instr)
  (mfetch-nil  : ∀ n → mfetch [] n ≡ nothing)
  (mfetch-zero : ∀ x xs → mfetch (x ∷ xs) zero ≡ just x)
  (mfetch-suc  : ∀ x xs n → mfetch (x ∷ xs) (suc n) ≡ mfetch xs n)
  -- the ONE view of an instruction this development needs, and the one law
  -- that replaces the constructor enumeration
  (is-label?     : Instr → Bool)
  (find-label-go : Label → List Instr → ℕ → Maybe ℕ)
  (skip-law : ∀ (t : Label) (i : Instr) (rest : List Instr) (xi : ℕ)
            → is-label? i ≡ false
            → find-label-go t (i ∷ rest) xi ≡ find-label-go t rest (suc xi))
  where

open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open import Relation.Binary.PropositionalEquality using (refl; cong; sym; trans)
open import Once.CCC.Machine.Flat
open FlatMachine {FS} using (fetch)

------------------------------------------------------------------------
-- Block lengths and the cumulative machine offset of a flat pc.
------------------------------------------------------------------------
blk-len : AbstractInstr → ℕ
blk-len i = length (compile-abstract i)

-- blk-off prog j = number of machine instructions before flat index j.
blk-off : AbstractTrace → ℕ → ℕ
blk-off _        zero    = zero
blk-off []       (suc _) = zero
blk-off (i ∷ is) (suc j) = blk-len i + blk-off is j

------------------------------------------------------------------------
-- A label-free block: the scan steps past it, advancing by its length
-- without matching. THREE LINES, where the arch-specific version was 22
-- clauses — the difference is `skip-law`.
------------------------------------------------------------------------
has-label : List Instr → Bool
has-label []       = false
has-label (i ∷ is) with is-label? i
... | true  = true
... | false = has-label is

find-label-go-skip : ∀ (target : Label) (block rest : List Instr) (xi : ℕ)
  → has-label block ≡ false
  → find-label-go target (block ++ rest) xi ≡ find-label-go target rest (xi + length block)
find-label-go-skip target []       rest xi _  =
  cong (find-label-go target rest) (sym (+-identityʳ xi))
find-label-go-skip target (b ∷ bs) rest xi nl with is-label? b in eq
... | true  = ⊥-elim (true≢false nl)
  where open import Data.Empty using (⊥-elim)
        true≢false : true ≡ false → _
        true≢false ()
... | false =
  trans (skip-law target b (bs ++ rest) xi eq)
        (trans (find-label-go-skip target bs rest (suc xi) nl)
               (cong (find-label-go target rest) (sym (+-suc xi (length bs)))))

------------------------------------------------------------------------
-- `drop` bookkeeping: dropping k flat blocks ⟺ dropping their machine
-- instructions. Pure list arithmetic, no machine anywhere.
------------------------------------------------------------------------
drop-[] : ∀ {A : Set} (n : ℕ) → drop {A = A} n [] ≡ []
drop-[] zero    = refl
drop-[] (suc n) = refl

drop-len-++ : ∀ {A : Set} (xs ys : List A) → drop (length xs) (xs ++ ys) ≡ ys
drop-len-++ []       ys = refl
drop-len-++ (x ∷ xs) ys = drop-len-++ xs ys

drop-+ : ∀ {A : Set} (m n : ℕ) (xs : List A) → drop (m + n) xs ≡ drop n (drop m xs)
drop-+ zero    n xs       = refl
drop-+ (suc m) n []       = sym (drop-[] n)
drop-+ (suc m) n (x ∷ xs) = drop-+ m n xs

drop-compile : ∀ (prog : AbstractTrace) (k : ℕ)
  → drop (blk-off prog k) (compile-trace prog) ≡ compile-trace (drop k prog)
drop-compile prog     zero    = refl
drop-compile []       (suc k) = refl
drop-compile (i ∷ is) (suc k) =
  trans (cong (drop (blk-len i + blk-off is k)) (ct-cons i is))
        (trans (drop-+ (blk-len i) (blk-off is k) (compile-abstract i ++ compile-trace is))
               (trans (cong (drop (blk-off is k)) (drop-len-++ (compile-abstract i) (compile-trace is)))
                      (drop-compile is k)))

------------------------------------------------------------------------
-- Fetching at a block offset.
------------------------------------------------------------------------
fetch-drop : ∀ (xs : List Instr) (n : ℕ) → mfetch xs n ≡ mfetch (drop n xs) zero
fetch-drop []       n       =
  trans (mfetch-nil n)
        (sym (trans (cong (λ ys → mfetch ys zero) (drop-[] n)) (mfetch-nil zero)))
fetch-drop (x ∷ xs) zero    = refl
fetch-drop (x ∷ xs) (suc n) = trans (mfetch-suc x xs n) (fetch-drop xs n)

-- The machine instruction at the block offset = the head of block k.
fetch-at-offset : ∀ (prog : AbstractTrace) (k : ℕ)
  → mfetch (compile-trace prog) (blk-off prog k) ≡ mfetch (compile-trace (drop k prog)) zero
fetch-at-offset prog k =
  trans (fetch-drop (compile-trace prog) (blk-off prog k))
        (cong (λ xs → mfetch xs zero) (drop-compile prog k))

-- pc advance: the machine offset of the NEXT flat pc = current offset + the
-- block length of the instruction at the current pc.
blk-off-suc : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i
  → blk-off prog (suc k) ≡ blk-off prog k + blk-len i
blk-off-suc []       k       i ()
blk-off-suc (j ∷ js) zero    .j refl = +-identityʳ (blk-len j)
blk-off-suc (j ∷ js) (suc k) i  eq   =
  trans (cong (blk-len j +_) (blk-off-suc js k i eq))
        (sym (+-assoc (blk-len j) (blk-off js k) (blk-len i)))

-- drop at a fetched position exposes the instruction as the head.
drop-fetch : ∀ (prog : AbstractTrace) (k : ℕ) (i : AbstractInstr)
  → fetch prog k ≡ just i → drop k prog ≡ i ∷ drop (suc k) prog
drop-fetch []       k       i ()
drop-fetch (j ∷ js) zero    .j refl = refl
drop-fetch (j ∷ js) (suc k) i  eq   = drop-fetch js k i eq
