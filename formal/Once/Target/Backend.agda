-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Target.Backend — plan 0.146 B1.7c (D463): ★ WHAT AN ARCH'S CODE
-- GENERATOR IMPLEMENTS.
--
-- Above it everything is arch-neutral: the compiled program is an abstract
-- trace (`AbstractTrace`) and the arith blocks its ops call (`ArithBlock`,
-- each under its arch-neutral symbol, `block-symbol`). An arch's backend
-- writes them as a file: the trace lowered to its instructions, each block's
-- body as its code (`payload`), the externs the program names. Its proof
-- half is `Adequacy.ArchCorrectness.Interface.ArchSim`, over the same
-- backend. The arches: `Target.<Arch>.Backend`; the one case split on the
-- arch: `Target.Backends.backend`.
------------------------------------------------------------------------

module Once.Target.Backend where

open import Data.List using (List; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Compile.Emit using (block-symbol; dedup-blocks)

record Backend : Set₁ where
  field
    -- the file, and its text
    File  : Set
    print : File → String
    -- an arith block's code
    Payload : Set
    payload : ArithBlock → Payload
    -- ★ the file of an image: its code, its blocks' table (by symbol), its externs
    file : AbstractTrace → List (String × Payload) → List String → File
    -- the file of a library: no code, no entry (D465: the linear core compiles whole programs)
    empty : File
    -- what the assembler demands of a file (every symbol defined once, every reference
    -- resolved, every symbol one it reads: `CPU.Interface.ArchSemantics.AsmWF`)
    AsmWF : File → Set

-- a block list's table: by symbol, once each (master's `Compile.blocks-<arch>`)
file-table : ∀ {P : Set} → (ArithBlock → P) → List ArithBlock → List (String × P)
file-table pay bs = map (λ sb → proj₁ sb , pay (proj₂ sb)) (dedup-blocks (map (λ b → block-symbol b , b) bs))
