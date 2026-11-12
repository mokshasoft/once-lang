-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.LinCore.MoveCode — plan 0.146 B1.4b: the lowering's word moves, as
-- code (`Lower` emits them, `Moves` proves what they do).
------------------------------------------------------------------------

module Once.LinCore.MoveCode where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using ([]; _∷_)
open import Once.CCC.Machine.SMCore using (AbstractTrace; load-from-slot; store-at-slot; load-at; store-at)

-- `n` words from slots `a…` to slots `b…`, lowest first (safe when b ≤ a)
mvSS : ℕ → ℕ → ℕ → AbstractTrace
mvSS a b zero    = []
mvSS a b (suc n) = load-from-slot a ∷ store-at-slot b ∷ mvSS (suc a) (suc b) n

-- …highest first (safe when a ≤ b)
mvSSd : ℕ → ℕ → ℕ → AbstractTrace
mvSSd a b zero    = []
mvSSd a b (suc n) = load-from-slot (a + n) ∷ store-at-slot (b + n) ∷ mvSSd a b n

-- from `Input1`'s words `o…` to slots `b…`
mvPS : ℕ → ℕ → ℕ → AbstractTrace
mvPS o b zero    = []
mvPS o b (suc n) = load-at o ∷ store-at-slot b ∷ mvPS (suc o) (suc b) n

-- from slots `a…` to `Input1`'s words `o…`
mvSP : ℕ → ℕ → ℕ → AbstractTrace
mvSP a o zero    = []
mvSP a o (suc n) = load-from-slot a ∷ store-at o ∷ mvSP (suc a) (suc o) n

-- `Output`'s word into slots `b…` (a sum's padding: every word of a value is
-- written, so a copy of it never reads an empty slot)
stores : ℕ → ℕ → AbstractTrace
stores b zero    = []
stores b (suc n) = store-at-slot b ∷ stores (suc b) n
