-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Arith.SigOp.Block
--
-- Plan 0.20 Phase E — the `arith.block.<digest>` SigOpInfo family
-- and the `blockProvider` that lowers them.
--
-- D-arith-1 / D-arith-7: from CCC's perspective an arith block is a
-- single opaque SigOp. It carries
--   - name = "arith.block." ++ digest of the recognised MArithIR
--   - semI = eval-arith body (lifted from ⟦sh⟧S to ⟦shape-as-type sh⟧)
--   - semM = the definitional modular-`Word` evaluator (D054); the
--           machine layer denotes `Int` as the CPU's `add`.
--
-- The Provider recognises any SigOp whose name starts with
-- `"arith.block."` and discharges its `Contract` via the same
-- `mkPurePrimResult` machinery used by `add-int-proof`
-- (`Once.Arith.SigOp.Proofs.agda:137`). The block is pure from CCC's
-- view: no heap alloc, no halt, scratch usage stays in BeforeFrontier.
------------------------------------------------------------------------

module Once.Arith.SigOp.Block where

open import Once.Arith.CmpOp using (CmpOp; c-lt; c-le; c-gt; c-ge; c-eq; c-ne; FCmpOp; fcmp)
open import Once.Spec.Theory
  using (float-rounded; float-order; float-equality; ‵==ᵈ; ‵!=ᵈ; ‵<ᵈ; ‵<=ᵈ; ‵>ᵈ; ‵>=ᵈ; ‵<; ‵<=; ‵>; ‵>=; ‵==; ‵!=)
open import Once.Spec.Type using (Base; b-*; b-Float; b-Int; b-Unit; ∅ₖ)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming ()
import Data.Integer as ℤ
open import Data.Nat using (suc)
-- the decimal the symbol layer proves injective (`SymbolInjective.toList-showNat`)
open import Once.Target.Symbol using () renaming (showNat to showℕ)
open import Data.List using ([]; _∷_)
open import Data.String using (String; _++_)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.SigOp.Info using (SigOpInfo; mk-info'; blockV)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.Spec.Name using (bare)

open import Once.Arith.Machine.Shape using (InputShape; shape-unit; shape-int; shape-float; shape-pair; InputPath; Side; Fst; Snd; Path; here-int; here-flt; go-fst; go-snd; ⌊_⌋ᴾ)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; aflit; ainput; aadd; asub; amul; adiv; amod; aneg; ai2f; acmp; afcmp; numtype-as-type; shape-as-type)

open import Once.Spec.Float.Decimal using (Decimal)
open Once.Spec.Float.Decimal.Decimal using (exp10; sig)
open import Once.Arith.Type using (NumType; NInt; NFloat)

------------------------------------------------------------------------
-- Digest computation (deterministic serialisation)
------------------------------------------------------------------------

-- | Render a path as alphanumeric-only chars. `F`=Fst, `S`=Snd, `Z`
-- terminates. The terminator gives a delimiter-free encoding that is
-- still injective in the path's contents.
show-side : Side → String
show-side Fst = "F"
show-side Snd = "S"

show-path : InputPath → String
show-path []       = "Z"
show-path (s ∷ p)  = show-side s ++ show-path p

-- | Render a ℤ literal as alphanumeric chars: positive `+n` → `n_`,
-- negative `-n` → `n<n>_`. Trailing `_` delimits so the digest is
-- linearly reconstructible without spaces.
show-zlit : ℤ → String
show-zlit (+_ n)         = showℕ n ++ "_"
show-zlit (-[1+_] n)     = "n" ++ showℕ (suc n) ++ "_"

-- | …and a `Decimal` payload, as its two fields (plan 0.75 F4). Rendered
-- UNNORMALISED, because the payload is: `0.5` and `0.50` are distinct records
-- (D116) and therefore distinct blocks. They round to the same word, so the
-- two bodies are identical — a missed sharing opportunity, never a wrong
-- answer, and `Once.Spec.Float.Decimal` pins the pair agreeing.
show-dlit : Decimal → String
show-dlit d = show-zlit (sig d) ++ showℕ (exp10 d) ++ "_"

-- | Render an MArithIR tree as a stable, alphanumeric-only digest.
-- Plan 0.20 Phase G: the digest is used as the suffix of an assembly
-- symbol (`once_arith.block.<digest>`), so it must avoid spaces /
-- parens / arithmetic punctuation that GNU `as` doesn't accept in
-- symbol names. Operators map to capital-letter mnemonics:
--   A = add, B = sub, M = mul, G = neg.
-- Leaves: `L` for literal, `I` for an input projection (`J` a float one). Terminators
-- (`_`, `Z`) keep the encoding prefix-free.
--
-- PLAN 0.75 F4: `F` for a float literal and `C` for the D125 widening. The
-- digest must SEPARATE the kinds — `1 + 2` at `Int` and at `Float` are
-- different blocks needing different instructions, and a digest that collided
-- them would link one body for both. The `NumType` index does not appear in
-- the string because it is DETERMINED by the leaves: a tree containing `F`,
-- `J` or `C` is a float tree and no other tree is.
show-arith-ir : ∀ {sh n} → MArithIR sh n → String
show-arith-ir (alit z)     = "L" ++ show-zlit z
show-arith-ir (aflit d)    = "F" ++ show-dlit d
show-arith-ir {n = NInt}   (ainput p) = "I" ++ show-path ⌊ p ⌋ᴾ
-- plan 0.129 B5: a FLOAT input is `J`. Once a block can read a `Float`
-- (`Rewrite.shape-of`), `x + y` at `Int` and at `Float` have the same tree, and
-- the leaf letter is all that separates them (`dedup-blocks` keeps one body per
-- symbol).
show-arith-ir {n = NFloat} (ainput p) = "J" ++ show-path ⌊ p ⌋ᴾ
show-arith-ir (aadd a b)   = "A" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (asub a b)   = "B" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (amul a b)   = "M" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (adiv a b)   = "D" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (amod a b)   = "R" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (aneg a)     = "G" ++ show-arith-ir a
show-arith-ir (ai2f a)     = "C" ++ show-arith-ir a
-- plan 0.108: `K` and ONE digit for the comparison — prefix-free like the rest.
show-arith-ir (acmp o a b) = "K" ++ show-cmp o ++ show-arith-ir a ++ show-arith-ir b
  where show-cmp : CmpOp → String
        show-cmp c-lt = "0"
        show-cmp c-le = "1"
        show-cmp c-gt = "2"
        show-cmp c-ge = "3"
        show-cmp c-eq = "4"
        show-cmp c-ne = "5"
-- plan 0.150: a FLOAT comparison — one letter per row and symbol of the table.
show-arith-ir (afcmp o a b) = "Q" ++ show-fcmp o ++ show-arith-ir a ++ show-arith-ir b
  where show-fcmp : FCmpOp → String
        show-fcmp (fcmp float-rounded  ‵==ᵈ) = "a"
        show-fcmp (fcmp float-rounded  ‵!=ᵈ) = "b"
        show-fcmp (fcmp float-rounded  ‵<ᵈ)  = "c"
        show-fcmp (fcmp float-rounded  ‵<=ᵈ) = "d"
        show-fcmp (fcmp float-rounded  ‵>ᵈ)  = "e"
        show-fcmp (fcmp float-rounded  ‵>=ᵈ) = "f"
        show-fcmp (fcmp float-order    ‵<)   = "g"
        show-fcmp (fcmp float-order    ‵<=)  = "h"
        show-fcmp (fcmp float-order    ‵>)   = "i"
        show-fcmp (fcmp float-order    ‵>=)  = "j"
        show-fcmp (fcmp float-equality ‵==)  = "k"
        show-fcmp (fcmp float-equality ‵!=)  = "l"

-- | D395: the block's INPUT SHAPE, prefix-free (Polish notation, lower case so
-- it never reads as a tree letter). Since D391 a leaf's load is at its flat
-- word offset (`Shape.flat-off`), which the whole shape decides, not the
-- side-path alone: `snd + 1` over `Int * Int` loads word 1 and over
-- `(Int * Int) * Int` word 2. Without the shape the two named one block, and
-- `dedup-blocks` linked both calls to one body.
show-shape : InputShape → String
show-shape shape-unit       = "u"
show-shape shape-int        = "i"
show-shape shape-float      = "f"
show-shape (shape-pair a b) = "p" ++ show-shape a ++ show-shape b

-- | The digest is the serialisation of the shape and the tree. (A hash
-- function would be shorter; the serialisation is sufficient for
-- correctness — it is injective — and only symbol-table size suffers.)
block-digest : ∀ {sh n} → MArithIR sh n → String
block-digest {sh} e = show-shape sh ++ show-arith-ir e

-- | The canonical name for an arith block.
block-name : ∀ {sh n} → MArithIR sh n → String
block-name e = "arith.block." ++ block-digest e

------------------------------------------------------------------------
-- The block's `SigOpInfo`
------------------------------------------------------------------------

-- A block's input shape is a tuple of `Unit`/`Int`/`Float` ⇒ its `shape-as-type` is base.
shape-as-type-base : ∀ (sh : InputShape) → Base ∅ₖ (shape-as-type sh)
shape-as-type-base shape-unit       = b-Unit
shape-as-type-base shape-int        = b-Int
shape-as-type-base shape-float      = b-Float
shape-as-type-base (shape-pair l r) = b-* (shape-as-type-base l) (shape-as-type-base r)

-- …and the codomain's, which used to be the constant `b-Int`.
numtype-as-type-base : ∀ (n : NumType) → Base ∅ₖ (numtype-as-type n)
numtype-as-type-base NInt   = b-Int
numtype-as-type-base NFloat = b-Float

-- | Named by its digest; its contract is its body (`blockV`, plan 0.129 B5),
-- whose meaning is `block-semM`. Observably pure: no event, no halt.
block-info : ∀ {sh n} → MArithIR sh n → SigOpInfo (shape-as-type sh) (numtype-as-type n)
block-info {sh} {n} e = mk-info' (bare (block-name e)) (blockV e refl refl) (shape-as-type-base sh) (numtype-as-type-base n)
