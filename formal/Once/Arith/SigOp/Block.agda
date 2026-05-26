-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
--   - semM = postulated for now (matches `Once.Arith.SigOp.Builders`
--           convention; the I-arith-cleanup item lands definitional
--           bodies once the I/M evaluator split lands).
--
-- The Provider recognises any SigOp whose name starts with
-- `"arith.block."` and discharges its `Contract` via the same
-- `mkPurePrimResult` machinery used by `add-int-proof`
-- (`Once.Arith.SigOp.Proofs.agda:137`). The block is pure from CCC's
-- view: no heap alloc, no halt, scratch usage stays in BeforeFrontier.
------------------------------------------------------------------------

module Once.Arith.SigOp.Block where

open import Data.Integer using (ℤ)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Type using (Type; Int)
open import Once.CCC.SigOp.Info using (SigOpInfo; mk-info; name)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-int; shape-pair; ⟦_⟧S; InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; aneg;
         eval-arith; shape-as-type; ArithBlock; mk-block)

import Once.Semantics.Core ℤ as I
import Once.Semantics.Core ℕ as M

------------------------------------------------------------------------
-- Digest computation (deterministic serialisation)
------------------------------------------------------------------------

-- | Render a path as a compact string ("FS" for Fst, "Sn" for Snd).
show-side : Side → String
show-side Fst = "F"
show-side Snd = "S"

show-path : InputPath → String
show-path []       = "·"
show-path (s ∷ p)  = show-side s ++ show-path p

-- | Render an MArithIR tree as a stable, deterministic string. Two
-- alpha-equivalent recognised IRs produce the same serialisation
-- (D-arith-3: no names anywhere in MArithIR, so equivalence is
-- syntactic on the tree).
show-arith-ir : ∀ {sh} → MArithIR sh → String
show-arith-ir (alit z)     = "L" ++ showℤ z
show-arith-ir (ainput p)   = "I" ++ show-path p
show-arith-ir (aadd a b)   = "(+ " ++ show-arith-ir a ++ " " ++ show-arith-ir b ++ ")"
show-arith-ir (asub a b)   = "(- " ++ show-arith-ir a ++ " " ++ show-arith-ir b ++ ")"
show-arith-ir (amul a b)   = "(* " ++ show-arith-ir a ++ " " ++ show-arith-ir b ++ ")"
show-arith-ir (aneg a)     = "(~ " ++ show-arith-ir a ++ ")"

-- | The digest is just the serialisation. (A hash function would be
-- stable across re-renders and shorter; the plan's "64-bit hex digest"
-- is a Phase E follow-up. The serialisation is sufficient for
-- correctness; only symbol-table size suffers.)
block-digest : ∀ {sh} → MArithIR sh → String
block-digest e = show-arith-ir e

-- | The canonical name for an arith block.
block-name : ∀ {sh} → MArithIR sh → String
block-name e = "arith.block." ++ block-digest e

------------------------------------------------------------------------
-- Bridge: ⟦ shape-as-type sh ⟧ ↔ ⟦ sh ⟧S
------------------------------------------------------------------------

-- | Convert a CCC-typed input value (`I.⟦ shape-as-type sh ⟧`) into
-- the AbsState-typed shape value (`⟦ sh ⟧S`). Both are tree-nested
-- products of ℤs at the proof level; this is a structural identity
-- that Agda needs help to see definitionally.
toShape-I : ∀ sh → I.⟦ shape-as-type sh ⟧ → ⟦ sh ⟧S
toShape-I shape-int        z       = z
toShape-I (shape-pair l r) (x , y) = toShape-I l x , toShape-I r y

------------------------------------------------------------------------
-- SigOpInfo family
------------------------------------------------------------------------

-- | Machine-level semantics for the block.
--
-- The machine layer uses `ℕ` for `⟦ Int ⟧`, so a definitional
-- machine-level evaluator would need an ℕ-based reinterpretation of
-- subtraction / negation (modular arithmetic). Per the existing
-- `Once.Arith.SigOp.Builders` convention this is postulated; the
-- I-arith-cleanup item is to write a definitional ℕ-eval that
-- matches the x86 register-level reality.
postulate
  block-semM : ∀ {sh} → MArithIR sh → M.⟦ shape-as-type sh ⟧ → M.⟦ Int ⟧

-- | The block's `SigOpInfo`.
--
-- `semI` is definitional (`eval-arith` lifted through `toShape-I`),
-- so any downstream evaluator that reduces through proof-level
-- semantics gets the arith result directly. `semM` is postulated as
-- above.
block-info : ∀ {sh} → MArithIR sh → SigOpInfo (shape-as-type sh) Int
block-info {sh} e = mk-info
  (block-name e)
  (λ x → eval-arith e (toShape-I sh x))
  (block-semM e)
