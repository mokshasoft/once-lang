-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Parser.Module.Alloc
--
-- Allocation-annotation parser: `@stack | @heap | @pool | @arena | @const`.
------------------------------------------------------------------------

module Once.Parser.Module.Alloc where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary using (does)
open import Once.Parser.Module.Core

-- | Allocation keyword → strategy (CLASSIFIER, decidable-equality based so it
-- reduces under a decision; dispatched whole, so the eager `does` is harmless).
allocKw : String → Maybe AllocStrategy
allocKw w =
  if does (w ≟ "stack") then just Stack
  else if does (w ≟ "heap")  then just Heap
  else if does (w ≟ "pool")  then just Pool
  else if does (w ≟ "arena") then just Arena
  else if does (w ≟ "const") then just Const
  else nothing

-- | Head classifier: `@ keyword` ⇒ its strategy, else `nothing`. Routes
-- `parseAllocB` (Plan 0.52 bridge-readiness) so it steps for a variable tail.
allocStrat : List Token → Maybe AllocStrategy
allocStrat (TAt ∷ TWord w ∷ _) = allocKw w
allocStrat _                   = nothing

drop2 : List Token → List Token
drop2 (_ ∷ _ ∷ xs) = xs
drop2 xs           = xs

drop2-≤ : (xs : List Token) → length (drop2 xs) ≤ length xs
drop2-≤ (_ ∷ _ ∷ xs) = m≤n⇒m≤1+n (m≤n⇒m≤1+n ≤-refl)
drop2-≤ []           = ≤-refl
drop2-≤ (_ ∷ [])     = ≤-refl

-- | Bounded variant: on success consumes 2 tokens (`@` + keyword). Residual ≤
-- input (it is `<` when an alloc is found, but `tryAllocB` only needs `≤`).
parseAllocB : (toks : List Token) → ParseAtB≤ {AllocStrategy} toks
pab : (toks : List Token) → Maybe AllocStrategy → ParseAtB≤ {AllocStrategy} toks
parseAllocB toks = pab toks (allocStrat toks)
pab toks (just strat) = just (strat , drop2 toks , drop2-≤ toks)
pab toks nothing      = nothing

-- | Parse: @stack | @heap | @pool | @arena | @const (plain Parser).
parseAlloc : Parser AllocStrategy
parseAlloc toks with parseAllocB toks
... | just (a , rest , _) = just (a , rest)
... | nothing = nothing

-- | Try to parse an allocation annotation, returning alloc + remaining
-- tokens; the residual is ≤ the input length. De-`with`'d via `tab`.
tryAllocB : (toks : List Token) →
            Maybe AllocStrategy × Σ[ rest ∈ List Token ] length rest ≤ length toks
tab : (toks : List Token) → ParseAtB≤ {AllocStrategy} toks →
      Maybe AllocStrategy × Σ[ rest ∈ List Token ] length rest ≤ length toks
tryAllocB toks = tab toks (parseAllocB toks)
tab toks (just (a , rest , bnd)) = just a , rest , bnd
tab toks nothing                 = nothing , toks , ≤-refl

tryAlloc : List Token → Maybe AllocStrategy × List Token
tryAlloc toks = let (a , rest , _) = tryAllocB toks in (a , rest)
