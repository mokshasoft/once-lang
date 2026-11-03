-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.FlatLayout — HOW A COMPONENT GOES INTO A BLOCK (plan 0.123
-- B.4 α, D375, D378).
--
-- A value is one of two kinds, by its type alone:
--   word — a scalar (Int, Float) or a node (μ, ν, a closure): ONE word, held in
--          a register as itself;
--   flat — Unit, a product or a sum: its `size` words at an address, held in a
--          register as that address.
-- So a component goes into its container's block as its word (`store-at`), or
-- as a copy of its words (`copy-from`). One rule, used by every construct.
------------------------------------------------------------------------

module Once.CCC.Codegen.FlatLayout where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using ([]; _∷_)
open import Once.IRTy using (IRTy; Unit; Void; _*_; _⇛_; μ-type; ν-type; Int; Float) renaming (_+_ to _+ᵀ_)
open import Once.CCC.Codegen.Size using (size)
open import Once.CCC.Machine.SMCore
  using (AbstractTrace; restore-input; load-from-slot; load-at; store-at; addr-at)

data Kind : Set where
  word flat : Kind

kind : IRTy → Kind
kind Unit       = flat
kind Void       = flat
kind (_ * _)    = flat
kind (_ +ᵀ _)   = flat
kind (_ ⇛ _)    = word
kind (μ-type _) = word
kind (ν-type _) = word
kind Int        = word
kind Float      = word

-- the k words from word i of the value whose address is in slot `src`, to the
-- block whose address is in slot `blk`, from its word `off + i`
copy-from : (src blk off i k : ℕ) → AbstractTrace
copy-from src blk off i zero    = []
copy-from src blk off i (suc k) =
  restore-input src ∷ load-at i ∷ restore-input blk ∷ store-at (off + i) ∷
  copy-from src blk off (suc i) k

-- a component, stashed in slot `stash`, into the block in slot `blk` at `off`
put-k : Kind → ℕ → (stash blk off : ℕ) → AbstractTrace
put-k word _ stash blk off = restore-input blk ∷ load-from-slot stash ∷ store-at off ∷ []
put-k flat n stash blk off = copy-from stash blk off 0 n

put : IRTy → (stash blk off : ℕ) → AbstractTrace
put X = put-k (kind X) (size X)

-- the component at word `k` of the flat value whose address is in `Input1`, into
-- `Output`: a word kind is its word, a flat kind its address. A 0-word component
-- reads nothing, so any cell of the block is its address: it takes the
-- container's own (word 0 — always in the block, so `addr-at` never points past
-- it, D379).
get-k : Kind → ℕ → ℕ → AbstractTrace
get-k word _       k = load-at k ∷ []
get-k flat zero    k = addr-at 0 ∷ []
get-k flat (suc _) k = addr-at k ∷ []

get : IRTy → ℕ → AbstractTrace
get X = get-k (kind X) (size X)
