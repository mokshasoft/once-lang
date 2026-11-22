-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ImageExterns — plan 0.146 B1.7 step 3 (D464): THE
-- SYMBOLS AN IMAGE CALLS OUTSIDE ITSELF, read off the image; what a file of
-- an image must be, as symbols (`ImageWF`).
--
-- A file declares what it calls and does not define: the Host's `leave` and
-- `exhausted`, and every external op the image calls (an FFI value, an
-- answer, an emit, a halt). Master's file reads them off the IR program
-- (`Compile.externs-of`); the linear core's image is read directly, so a
-- call the image makes is an extern by construction (`ext-in`).
------------------------------------------------------------------------

module Once.CCC.Codegen.ImageExterns where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Once.CCC.Codegen.ImageSymbols using (adefs; arefs; entry-symbol)
open import Once.Target.AsmSymbol using (AsmSym)
open import Once.Arith.Machine.IR using (ArithBlock)
import Once.Compile.Emit
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (refl)
open import Once.SigOp.Info using (SigOpInfo; SigOpSem; blockV; primV; ffiV; callsV; emitsV; haltsV; External; ext-ffi; ext-calls; ext-emits; ext-halts; module SigOpInfo)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Label using (e-thunk; e-fn)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Once.Target.SymbolValid using (once-symbol-path-asm)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.Target.SymbolFresh using (host-leave-symbol; host-exhausted-symbol)

-- an op's symbol, if the op is external
ext-at : ∀ {A B} → SigOpSem A B → String → List String
ext-at (blockV _ _ _) s = []
ext-at (primV _)      s = []
ext-at ffiV           s = s ∷ []
ext-at callsV         s = s ∷ []
ext-at (emitsV _)     s = s ∷ []
ext-at (haltsV _)     s = s ∷ []

ext-sym : AbstractInstr → List String
ext-sym (instr-sigop si) = ext-at (SigOpInfo.sem si) (once-symbol-path (SigOpInfo.name si))
{-# CATCHALL #-}
ext-sym _                = []

ext-syms : AbstractTrace → List String
ext-syms []       = []
ext-syms (i ∷ is) = ext-sym i ++ ext-syms is

-- ★ THE SYMBOLS OF A FILE OF AN IMAGE (what `AsmWF` reads of it, read off the image): it
-- defines `once_main`, the image's labels and its blocks' symbols; each once; each reference
-- among them or the externs; every extern a symbol `as` reads
Defs : AbstractTrace → List ArithBlock → List String
Defs t bs = entry-symbol ∷ adefs t ++ Once.Compile.Emit.block-syms bs

ImageWF : AbstractTrace → List ArithBlock → List String → Set
ImageWF t bs ex = Unique (Defs t bs) × All (λ s → s ∈ Defs t bs ⊎ s ∈ ex) (arefs t) × All AsmSym ex

-- ★ the externs of a file of an image
image-externs : AbstractTrace → List String
image-externs t = host-leave-symbol ∷ host-exhausted-symbol ∷ ext-syms t

ext-at-in : ∀ {A B} (s : SigOpSem A B) x → External s → x ∈ ext-at s x
ext-at-in ffiV       x ext-ffi   = here refl
ext-at-in callsV     x ext-calls = here refl
ext-at-in (emitsV _) x ext-emits = here refl
ext-at-in (haltsV _) x ext-halts = here refl

-- ★ an external op the image calls is one of its externs
ext-in : ∀ (t : AbstractTrace) {A B} (si : SigOpInfo A B) → instr-sigop si ∈ t → External (SigOpInfo.sem si)
       → once-symbol-path (SigOpInfo.name si) ∈ image-externs t
ext-in t si m e = there (there (go t m))
  where
    go : ∀ t → instr-sigop si ∈ t → once-symbol-path (SigOpInfo.name si) ∈ ext-syms t
    go (i ∷ is) (here refl) = ∈-++⁺ˡ (ext-at-in (SigOpInfo.sem si) _ e)
    go (i ∷ is) (there m′)  = ∈-++⁺ʳ (ext-sym i) (go is m′)

private
  ext-at-asm : ∀ {A B} (s : SigOpSem A B) x → AsmSym x → All AsmSym (ext-at s x)
  ext-at-asm (blockV _ _ _) x a = []
  ext-at-asm (primV _)      x a = []
  ext-at-asm ffiV           x a = a ∷ []
  ext-at-asm callsV         x a = a ∷ []
  ext-at-asm (emitsV _)     x a = a ∷ []
  ext-at-asm (haltsV _)     x a = a ∷ []

  ext-sym-asm : ∀ (i : AbstractInstr) → All AsmSym (ext-sym i)
  ext-sym-asm (instr-ctrl (c-label m)) = []
  ext-sym-asm (instr-ctrl (c-entry (e-thunk m) _)) = []
  ext-sym-asm (instr-ctrl (c-entry (e-fn f) _)) = []
  ext-sym-asm (instr-ctrl (c-jmp _)) = []
  ext-sym-asm (instr-ctrl (c-branch-tag-zero _)) = []
  ext-sym-asm (instr-ctrl (c-ret _)) = []
  ext-sym-asm (instr-ctrl (c-call-fn _)) = []
  ext-sym-asm (instr-ctrl (c-start _)) = []
  ext-sym-asm (instr-ctrl c-leave) = []
  ext-sym-asm mov-to-output = []
  ext-sym-asm mov-to-input = []
  ext-sym-asm load-indirect = []
  ext-sym-asm load-indirect-suc = []
  ext-sym-asm (load-from-slot _) = []
  ext-sym-asm (store-at-slot _) = []
  ext-sym-asm store-indirect = []
  ext-sym-asm store-indirect-suc = []
  ext-sym-asm (lea-slot _) = []
  ext-sym-asm (restore-input _) = []
  ext-sym-asm (instr-alloc-stack _) = []
  ext-sym-asm (instr-dealloc-stack _) = []
  ext-sym-asm (instr-reclaim-to _) = []
  ext-sym-asm (instr-free-heap _) = []
  ext-sym-asm (load-at _) = []
  ext-sym-asm (store-at _) = []
  ext-sym-asm (addr-at _) = []
  ext-sym-asm (load-rec _) = []
  ext-sym-asm (store-rec _) = []
  ext-sym-asm (instr-room _) = []
  ext-sym-asm (instr-push-frame _) = []
  ext-sym-asm instr-pop-frame = []
  ext-sym-asm instr-call-closure = []
  ext-sym-asm (worklist-init _) = []
  ext-sym-asm (worklist-push _) = []
  ext-sym-asm (worklist-pop _) = []
  ext-sym-asm (worklist-check _) = []
  ext-sym-asm (instr-sigop si) = ext-at-asm (SigOpInfo.sem si) _ (once-symbol-path-asm (SigOpInfo.name si))
  ext-sym-asm (instr-load-const _ _) = []
  ext-sym-asm (instr-load-code-addr _) = []
  ext-sym-asm instr-save-closure-reg = []
  ext-sym-asm (instr-load-tag-lit _) = []
  ext-sym-asm (instr-alloc-heap _) = []
  ext-sym-asm (instr-reg-op _) = []

-- ★ an image's externs are symbols `as` reads
image-externs-valid : ∀ (t : AbstractTrace) → All AsmSym (image-externs t)
image-externs-valid t = (tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ [])
                      ∷ (tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) ∷ go t
  where go : ∀ t → All AsmSym (ext-syms t)
        go []       = []
        go (i ∷ is) = ++⁺ (ext-sym-asm i) (go is)
