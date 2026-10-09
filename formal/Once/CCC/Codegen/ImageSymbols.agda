-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.CCC.Codegen.ImageSymbols — plan 0.107 phase d, layer 1: THE SYMBOLS
-- AN ABSTRACT IMAGE DEFINES AND REFERENCES.
--
-- `AsmWF` (`Once.CCC.Target.<arch>.File`) is a statement about the symbols of
-- the LOWERED file. Every one of them is the symbol of an abstract instruction,
-- and the rendering is shared by the three targets (`Once.CCC.Label.labelSym`,
-- `Once.Target.Symbol.once-symbol-path`), so the symbols can be read off the
-- ABSTRACT image once, arch-independently. Each arch then proves its lowering
-- is faithful to this reading (`Once.CCC.Target.<arch>.FileSymbols`), and the
-- file's well-formedness becomes a property of the image.
--
-- A `c-label` or a `c-entry` DEFINES a symbol; a jump, a branch, a direct call,
-- a code address, a SigOp call, and `_start`'s heap register REFERENCE one.
------------------------------------------------------------------------

module Once.CCC.Codegen.ImageSymbols where

open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)

open import Once.CCC.Label using (once; callee; labelSym; thunkSym; e-fn)
open import Once.SigOp.Info using (module SigOpInfo)
open SigOpInfo using (name)
open import Once.Target.Symbol using (once-symbol-path)
open import Once.CCC.Machine.SMCore
  using (AbstractInstr; AbstractTrace; FlatCtrl;
         instr-ctrl; instr-sigop; instr-load-code-addr;
         c-label; c-jmp; c-branch-scratch-zero; c-branch-tag-zero; c-entry; c-ret;
         c-call-fn; c-start)

-- The runtime's one datum: the `.bss` heap `_start` points the heap register at.
heap-symbol : String
heap-symbol = "once_heap_base"

ctrl-defs : FlatCtrl → List String
ctrl-defs (c-label n)   = labelSym (once n) ∷ []
ctrl-defs (c-entry e _) = labelSym (callee e) ∷ []
ctrl-defs (c-jmp _)                 = []
ctrl-defs (c-branch-scratch-zero _) = []
ctrl-defs (c-branch-tag-zero _)     = []
ctrl-defs (c-ret _)                 = []
ctrl-defs (c-call-fn _)             = []
ctrl-defs (c-start _)               = []

ctrl-refs : FlatCtrl → List String
ctrl-refs (c-jmp n)                 = labelSym (once n) ∷ []
ctrl-refs (c-branch-scratch-zero n) = labelSym (once n) ∷ []
ctrl-refs (c-branch-tag-zero n)     = labelSym (once n) ∷ []
ctrl-refs (c-call-fn f)             = labelSym (callee (e-fn f)) ∷ []
ctrl-refs (c-start _)               = heap-symbol ∷ []
ctrl-refs (c-label _)               = []
ctrl-refs (c-entry _ _)             = []
ctrl-refs (c-ret _)                 = []

instr-defs : AbstractInstr → List String
instr-defs (instr-ctrl c) = ctrl-defs c
{-# CATCHALL #-}
instr-defs _              = []

instr-refs : AbstractInstr → List String
instr-refs (instr-ctrl c)           = ctrl-refs c
instr-refs (instr-sigop si)         = once-symbol-path (name si) ∷ []
instr-refs (instr-load-code-addr n) = thunkSym n ∷ []
{-# CATCHALL #-}
instr-refs _                        = []

adefs : AbstractTrace → List String
adefs []       = []
adefs (i ∷ is) = instr-defs i ++ adefs is

arefs : AbstractTrace → List String
arefs []       = []
arefs (i ∷ is) = instr-refs i ++ arefs is
