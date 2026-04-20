-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Parser.Module.Alloc
--
-- Allocation-annotation parser: `@stack | @heap | @pool | @arena | @const`.
------------------------------------------------------------------------

module Once.Parser.Module.Alloc where

open import Once.Parser.Module.Core

-- | Bounded variant: on success consumes 2 tokens (`@` + keyword).
parseAllocB : (toks : List Token) → ParseAtB {AllocStrategy} toks
parseAllocB (TAt ∷ TWord w ∷ rest) with w ≟ "stack"
... | yes _ = just (Stack , rest , s≤s (n≤1+n _))
... | no _ with w ≟ "heap"
...   | yes _ = just (Heap , rest , s≤s (n≤1+n _))
...   | no _ with w ≟ "pool"
...     | yes _ = just (Pool , rest , s≤s (n≤1+n _))
...     | no _ with w ≟ "arena"
...       | yes _ = just (Arena , rest , s≤s (n≤1+n _))
...       | no _ with w ≟ "const"
...         | yes _ = just (Const , rest , s≤s (n≤1+n _))
...         | no _ = nothing
parseAllocB _ = nothing

-- | Parse: @stack | @heap | @pool | @arena | @const (plain Parser).
parseAlloc : Parser AllocStrategy
parseAlloc toks with parseAllocB toks
... | just (a , rest , _) = just (a , rest)
... | nothing = nothing

-- | Try to parse an allocation annotation, returning alloc + remaining
-- tokens; the residual is ≤ the input length.
tryAllocB : (toks : List Token) →
            Maybe AllocStrategy × Σ[ rest ∈ List Token ]
              length rest ≤ length toks
tryAllocB toks with parseAllocB toks
... | just (a , rest , bnd) = just a , rest , <⇒≤ bnd
... | nothing = nothing , toks , ≤-refl

tryAlloc : List Token → Maybe AllocStrategy × List Token
tryAlloc toks = let (a , rest , _) = tryAllocB toks in (a , rest)
