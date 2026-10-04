-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ImageWF — plan 0.107 phase d, layer 2: THE IMAGE IS CLOSED
-- AND ITS SYMBOLS ARE DISTINCT.
--
-- What `as`/`ld` demand of a file (`AsmWF`), read through the lowering
-- (`Once.CCC.Target.<arch>.FileSymbols`, layer 1, proved), is a property of the
-- ABSTRACT program image — the same for the three targets, because the symbols
-- are rendered by shared functions. This module states it once:
--
--   * every symbol the image and its arith blocks define is defined once;
--   * every symbol the image references is one of them, or an interpretation
--     symbol the module declares (`moduleExterns`).
--
-- RESIDUAL, class **deferred proof** — four statements (a program and a
-- library, each: defined once, resolved), replacing `FileWF.file-wf`'s one
-- statement over the per-arch FILE. Discharging them is layers 2 and 3 of
-- plan 0.107 §6: the counter windows (`LabelScope`, `LabelsUnique`), linkedness
-- (`CallsLinked`), the rewrite's block registration (D264), and symbol
-- injectivity (`Once.Target.SymbolInjective`).
------------------------------------------------------------------------

module Once.Adequacy.ImageWF where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
open import Once.Denotation.Program using (IRProgram; irProgram)
open import Once.Arith.Machine.IR using (ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Target.Symbol using (once-symbol-own)
open import Once.Compile using (Module; moduleToIR; moduleTable; image-of; program-blocks;
                                lib-image; lib-blocks; dedup-blocks)
open import Once.Adequacy.EmitFile using (moduleExterns)
open import Once.CCC.Codegen.ImageSymbols using (heap-symbol; adefs; arefs)

-- An arith block's symbol — what every arch's `arith-block-symbol` is.
block-symbol : ArithBlock → String
block-symbol b = once-symbol-own (block-name (block-body b))

-- The file's block table, by symbol, once each (`Compile.blocks-<arch>`).
block-syms : List ArithBlock → List String
block-syms bs = map proj₁ (dedup-blocks (map (λ b → block-symbol b , b) bs))

-- What a program's file defines: the heap, `_start`, the image's labels and
-- entries, the arith blocks.
prog-defs : IRProgram → List String
prog-defs p = heap-symbol ∷ "_start" ∷ adefs (image-of p) ++ block-syms (program-blocks p)

-- …and a library's (no `_start`).
lib-defs : Module → List String
lib-defs m = heap-symbol ∷ adefs (lib-image (moduleTable m)) ++ block-syms (lib-blocks (moduleTable m))

Resolved : List String → List String → List String → Set
Resolved defs ext refs = All (λ s → s ∈ defs ⊎ s ∈ ext) refs

postulate
  prog-unique   : ∀ (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir
                → Unique (prog-defs (irProgram (moduleTable m) ir))
  prog-resolved : ∀ (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir
                → Resolved (prog-defs (irProgram (moduleTable m) ir)) (moduleExterns m)
                           (arefs (image-of (irProgram (moduleTable m) ir)))
  lib-unique    : ∀ (m : Module) → moduleToIR m ≡ nothing → Unique (lib-defs m)
  lib-resolved  : ∀ (m : Module) → moduleToIR m ≡ nothing
                → Resolved (lib-defs m) (moduleExterns m) (arefs (lib-image (moduleTable m)))
