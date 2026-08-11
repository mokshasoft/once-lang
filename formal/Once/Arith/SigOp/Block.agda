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

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_; -[1+_]) renaming (_<?_ to _<ℤ?_)
import Data.Integer as ℤ
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)

open import Once.Type using (Type; Int)
open import Once.SigOp.Info using (SigOpInfo; mk-info; name; Pure)
open import Once.Functor.Translate using (IsBaseType; base-Unit; base-Int; base-Prod; con-base)
open import Once.CanonicalName using (bare)

open import Once.Arith.Machine.AbsState
  using (InputShape; shape-unit; shape-int; shape-pair; ⟦_⟧S; InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.IR
  using (MArithIR; alit; ainput; aadd; asub; amul; adiv; amod; aneg;
         shape-as-type; ArithBlock; mk-block)
import Once.Word as OnceWord
module W = OnceWord.Word64

import Once.Semantics.Value OnceWord.Carrier as M
-- (Core ℤ as I removed: block-info's semI deleted — block-semM is the meaning.)

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

-- | Render an MArithIR tree as a stable, alphanumeric-only digest.
-- Plan 0.20 Phase G: the digest is used as the suffix of an assembly
-- symbol (`once_arith.block.<digest>`), so it must avoid spaces /
-- parens / arithmetic punctuation that GNU `as` doesn't accept in
-- symbol names. Operators map to capital-letter mnemonics:
--   A = add, B = sub, M = mul, G = neg.
-- Leaves: `L` for literal, `I` for input projection. Terminators
-- (`_`, `Z`) keep the encoding prefix-free.
show-arith-ir : ∀ {sh} → MArithIR sh → String
show-arith-ir (alit z)     = "L" ++ show-zlit z
show-arith-ir (ainput p)   = "I" ++ show-path p
show-arith-ir (aadd a b)   = "A" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (asub a b)   = "B" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (amul a b)   = "M" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (adiv a b)   = "D" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (amod a b)   = "R" ++ show-arith-ir a ++ show-arith-ir b
show-arith-ir (aneg a)     = "G" ++ show-arith-ir a

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

------------------------------------------------------------------------
-- SigOpInfo family
------------------------------------------------------------------------

-- | Machine-level semantics for the block (D054).
--
-- The machine layer denotes `Int` as a modular `Word` (= the CPU's
-- `add`), so `block-semM` is the definitional `Word` evaluator,
-- mirroring `eval-arith` (the ℤ spec) op-for-op with the modular
-- operations from `Once.Arith.Word`. No postulates, no no-overflow
-- side condition: wraparound is the defined meaning.
--
-- `M.⟦ Int ⟧` is `ℕ` (machine `IntRep`), and `Word` is `ℕ`, so the
-- result carrier matches definitionally.

-- | Project a `Word` leaf out of a machine-typed input tree. Parallel
-- to `project` (AbsState) but over `M.⟦ shape-as-type sh ⟧` rather
-- than `⟦ sh ⟧S`.
projectM : ∀ (sh : InputShape) → InputPath → M.⟦ shape-as-type sh ⟧ → Maybe W.Word
projectM shape-unit       _         _       = nothing
projectM shape-int        []        z       = just z
projectM shape-int        (_ ∷ _)   _       = nothing
projectM (shape-pair _ _) []        _       = nothing
projectM (shape-pair l _) (Fst ∷ p) (x , _) = projectM l p x
projectM (shape-pair _ r) (Snd ∷ p) (_ , y) = projectM r p y

-- | Default-zero for an out-of-shape path (mirrors `eval-arith`'s
-- `+ 0` rule; well-formed IRs never hit it).
maybe-zeroM : Maybe W.Word → W.Word
maybe-zeroM (just w) = w
maybe-zeroM nothing  = 0

block-semM : ∀ {sh} → MArithIR sh → M.⟦ shape-as-type sh ⟧ → M.⟦ Int ⟧
block-semM (alit z)        _   = W.fromℤ z
block-semM {sh} (ainput p) inp = maybe-zeroM (projectM sh p inp)
block-semM (aadd a b)      inp = block-semM a inp W.⊕ block-semM b inp
block-semM (asub a b)      inp = block-semM a inp W.⊖ block-semM b inp
block-semM (amul a b)      inp = block-semM a inp W.⊗ block-semM b inp
block-semM (adiv a b)      inp = block-semM a inp W./ˢ block-semM b inp
block-semM (amod a b)      inp = block-semM a inp W.%ˢ block-semM b inp
block-semM (aneg a)        inp = W.⊝ block-semM a inp

-- | The block's `SigOpInfo`.
--
-- `semI` is definitional (`eval-arith` lifted through `toShape-I`),
-- so any downstream evaluator that reduces through proof-level
-- semantics gets the arith result directly. `semM` is the
-- definitional modular-`Word` evaluator (`block-semM`).
-- A block's input shape is a tuple of `Unit`/`Int` ⇒ its `shape-as-type` is base.
shape-as-type-base : ∀ (sh : InputShape) → IsBaseType (shape-as-type sh)
shape-as-type-base shape-unit       = base-Unit
shape-as-type-base shape-int        = base-Int
shape-as-type-base (shape-pair l r) = base-Prod (shape-as-type-base l) (shape-as-type-base r)

block-info : ∀ {sh} → MArithIR sh → SigOpInfo (shape-as-type sh) Int
block-info {sh} e = mk-info
  (bare (block-name e))
  (block-semM e)
  Pure  -- arith blocks are observably pure (no event, no halt)
  (shape-as-type-base sh) (con-base base-Int)
