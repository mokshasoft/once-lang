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
--     symbol the program calls (`externs-of`, D274).
--
-- RESIDUAL, class **deferred proof** — replacing `FileWF.file-wf`'s one
-- statement over the per-arch FILE. A program's references are RESOLVED by
-- `ImageResolved` from `prog-sigops` (the SigOp leaves); what is left is
-- uniqueness, and the library's two. Discharging them is layers 2 and 3 of
-- plan 0.107 §6: the counter windows (`LabelScope`, `LabelsUnique`), linkedness
-- (`CallsLinked`), the rewrite's block registration (D264), and symbol
-- injectivity (`Once.Target.SymbolInjective`).
------------------------------------------------------------------------

module Once.Adequacy.ImageWF where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
open import Once.Denotation.Program using (IRProgram; irProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (sem)
open import Once.Arith.SigOp.Compare using (cmp-of)
open import Once.CCC.Codegen.NodesOK using (SigLeaves; sigop-syms)
open import Once.Compile using (moduleToIR; moduleTable; image-of; program-blocks; rewrite-program; lib-image; lib-blocks; block-syms; calls-of; externs-of; is-extern?)
open import Once.Parser.Module using ()
open import Once.Parser.Module.Core using (Module)
open import Once.CCC.Codegen.NodesOK using (leaf-syms; leaf-syms-leaves)
open import Once.Denotation.Program using (IRFun)
open import Data.List.Relation.Unary.All using ([]; _∷_; tabulate)
open import Data.List.Relation.Unary.All.Properties using (++⁻)
open import Data.List.Relation.Unary.Any using (there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-filter⁺)
open import Data.Product using (proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Data.List.Membership.DecPropositional Data.String._≟_ using () renaming (_∈?_ to _∈ˢ?_)
import Data.String
open import Once.CCC.Codegen.ImageSymbols using (heap-symbol; adefs)

-- What a program's file defines: the heap, `_start`, the image's labels and
-- entries, the arith blocks.
prog-defs : IRProgram → List String
prog-defs p = heap-symbol ∷ "_start" ∷ adefs (image-of p) ++ block-syms (program-blocks p)

-- …and a library's (no `_start`).
lib-defs : Module → List String
lib-defs m = heap-symbol ∷ adefs (lib-image (moduleTable m)) ++ block-syms (lib-blocks (moduleTable m))

Resolved : List String → List String → List String → Set
Resolved defs ext refs = All (λ s → s ∈ defs ⊎ s ∈ ext) refs

-- What a program's SigOp may name: a symbol its file defines (its blocks), or an
-- interpretation symbol it calls (D274).
ProgG : Module → IR ⌊ Unit ⌋ ⌊ Unit ⌋ → String → Set
ProgG m ir s = s ∈ prog-defs (irProgram (moduleTable m) ir) ⊎ s ∈ externs-of (irProgram (moduleTable m) ir)

ProgP : Module → IR ⌊ Unit ⌋ ⌊ Unit ⌋ → ∀ {A B} → SigOpInfo A B → Set
ProgP m ir si = All (ProgG m ir) (sigop-syms si (cmp-of (sem si)))

-- That each file defines every symbol once is `Once.Adequacy.ImageUnique`'s
-- (plan 0.107 §8 step 4; were postulates here).

------------------------------------------------------------------------
-- D274 / plan 0.107 §9 2D: every SigOp the rewritten program calls names one of
-- its blocks (the rewrite registered it — D264) or an interpretation symbol it
-- declares external — BY CONSTRUCTION: the externs ARE the called symbols that
-- are not blocks. (Was a postulate, KNOWN FALSE while an FFI declaration had two
-- names, plan 0.107 §7.)
------------------------------------------------------------------------

private
  calls-ok : ∀ (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
           → All (ProgG m ir) (calls-of (rewrite-program (irProgram (moduleTable m) ir)))
  calls-ok m ir = tabulate (λ {s} s∈ → split s s∈ (s ∈ˢ? block-syms (program-blocks p)))
    where
      p = irProgram (moduleTable m) ir
      split : ∀ s → s ∈ calls-of (rewrite-program p) → _ → ProgG m ir s
      split s s∈ (yes b) = inj₁ (there (there (∈-++⁺ʳ (adefs (image-of p)) b)))
      split s s∈ (no nb) = inj₂ (∈-filter⁺ (is-extern? p) s∈ nb)

  table-ok : ∀ {G : String → Set} (es : List IRFun)
           → All G (Data.List.concatMap (λ e → leaf-syms (fbody e)) es)
           → All (λ e → SigLeaves (λ si → All G (sigop-syms si (cmp-of (sem si)))) (fbody e)) es
  table-ok []       a = []
  table-ok (e ∷ es) a = leaf-syms-leaves (fbody e) (proj₁ (++⁻ (leaf-syms (fbody e)) a))
                      ∷ table-ok es (proj₂ (++⁻ (leaf-syms (fbody e)) a))

prog-sigops : ∀ (m : Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir
            → SigLeaves (ProgP m ir) (main (rewrite-program (irProgram (moduleTable m) ir)))
            × All (λ e → SigLeaves (ProgP m ir) (fbody e)) (table (rewrite-program (irProgram (moduleTable m) ir)))
prog-sigops m ir _ =
  leaf-syms-leaves (main rp) (proj₁ (++⁻ (leaf-syms (main rp)) (calls-ok m ir)))
  , table-ok (table rp) (proj₂ (++⁻ (leaf-syms (main rp)) (calls-ok m ir)))
  where rp = rewrite-program (irProgram (moduleTable m) ir)

