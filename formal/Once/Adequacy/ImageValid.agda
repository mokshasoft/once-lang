-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ImageValid — plan 0.107 §8 step 4 (D272, D275): EVERY SYMBOL A
-- FILE DEFINES OR DECLARES EXTERNAL IS AN `as` SYMBOL NAME.
--
-- Were four postulates (`ImageWF.{prog,lib}-defs-valid`, `-externs-valid`),
-- the extern two FALSE for a module whose signature name is not an identifier
-- (D275). Now theorems for EVERY program: the symbols are `once-symbol-path`
-- renderings (total z-encoding), label symbols, and two fixed names.
------------------------------------------------------------------------

module Once.Adequacy.ImageValid where

open import Data.List using (List; []; _∷_; map)
import Data.List
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺; filter⁺)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Data.Bool using (true; false; if_then_else_)
import Data.Bool.ListAction as BLA
open import Data.String using (_==_)

open import Once.Type using (fits-int; fits-float)
open import Once.CCC.Machine.SMCore
open import Once.CCC.Codegen.ImageSymbols using (instr-defs; ctrl-defs; adefs; heap-symbol)
open import Once.CCC.Codegen.NodesOK using (sigop-syms; leaf-syms; leaf-syms-all)
open import Once.SigOp.Info using (SigOpInfo; name; sem)
open import Once.Arith.SigOp.Compare using (cmp-of; cmp-block-info)
open import Once.Arith.CmpOp using (CmpOp)
open import Data.Maybe using (Maybe; just; nothing)
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Denotation.Program using (IRProgram; IRFun; main; table; fbody)
open import Once.Target.AsmSymbol using (AsmSym)
open import Once.Target.SymbolValid using (once-symbol-path-asm; once-symbol-own-asm; once-label-asm; callee-label-asm)
open import Once.Arith.SigOp.Block using (block-name)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Compile using (Module; moduleTable; image-of; program-blocks; rewrite-program; lib-image; lib-blocks; dedup-go; dedup-blocks; block-symbol; block-syms; calls-of; externs-of; is-extern?)
open import Once.Adequacy.ImageWF using (prog-defs; lib-defs)

------------------------------------------------------------------------
-- What an image defines
------------------------------------------------------------------------

ctrl-defs-asm : ∀ (c : FlatCtrl) → All AsmSym (ctrl-defs c)
ctrl-defs-asm (c-label n)               = once-label-asm n ∷ []
ctrl-defs-asm (c-entry e _)             = callee-label-asm e ∷ []
ctrl-defs-asm (c-jmp _)                 = []
ctrl-defs-asm (c-branch-scratch-zero _) = []
ctrl-defs-asm (c-branch-tag-zero _)     = []
ctrl-defs-asm (c-ret _)                 = []
ctrl-defs-asm (c-call-fn _)             = []
ctrl-defs-asm (c-start _)               = []

instr-defs-asm : ∀ (i : AbstractInstr) → All AsmSym (instr-defs i)
instr-defs-asm (instr-ctrl c) = ctrl-defs-asm c
instr-defs-asm mov-to-output = []
instr-defs-asm mov-to-input = []
instr-defs-asm load-indirect = []
instr-defs-asm load-indirect-suc = []
instr-defs-asm (load-from-slot s) = []
instr-defs-asm (store-at-slot s) = []
instr-defs-asm store-indirect = []
instr-defs-asm store-indirect-suc = []
instr-defs-asm (lea-slot s) = []
instr-defs-asm (restore-input s) = []
instr-defs-asm (instr-alloc-stack k) = []
instr-defs-asm (instr-dealloc-stack k) = []
instr-defs-asm (instr-reclaim-to k) = []
instr-defs-asm (instr-push-frame k) = []
instr-defs-asm instr-pop-frame = []
instr-defs-asm instr-call-closure = []
instr-defs-asm (worklist-init s) = []
instr-defs-asm (worklist-push s) = []
instr-defs-asm (worklist-pop s) = []
instr-defs-asm (worklist-check s) = []
instr-defs-asm (instr-sigop si) = []
instr-defs-asm (instr-load-const fits-int v) = []
instr-defs-asm (instr-load-const fits-float v) = []
instr-defs-asm (instr-load-code-addr n) = []
instr-defs-asm instr-save-closure-reg = []
instr-defs-asm (instr-load-tag-lit k) = []
instr-defs-asm (instr-case-on-tag f g) = []
instr-defs-asm (instr-alloc-heap k) = []
instr-defs-asm (instr-loop b) = []
instr-defs-asm (instr-reg-op scratch-one) = []
instr-defs-asm (instr-reg-op scratch-zero) = []
instr-defs-asm (instr-reg-op scratch-dec) = []
instr-defs-asm (instr-reg-op scratch-load-count) = []
instr-defs-asm (instr-reg-op count-zero) = []
instr-defs-asm (instr-reg-op count-inc) = []
instr-defs-asm (instr-reg-op out-nz) = []
instr-defs-asm (lea-indexed k) = []

adefs-asm : ∀ (t : AbstractTrace) → All AsmSym (adefs t)
adefs-asm []       = []
adefs-asm (i ∷ is) = ++⁺ (instr-defs-asm i) (adefs-asm is)

------------------------------------------------------------------------
-- The block table (deduplicated by symbol)
------------------------------------------------------------------------

private
  dedup-step : ∀ {P : String → Set} (seen : List String) (s : String) (b : ArithBlock) (bs : List (String × ArithBlock))
             → (r : _) → P s → All (λ q → P (proj₁ q)) (dedup-go (s ∷ seen) bs) → All (λ q → P (proj₁ q)) (dedup-go seen bs)
             → All (λ q → P (proj₁ q)) (if r then dedup-go seen bs else (s , b) ∷ dedup-go (s ∷ seen) bs)
  dedup-step seen s b bs true  ps a₁ a₂ = a₂
  dedup-step seen s b bs false ps a₁ a₂ = ps ∷ a₁

  dedup-all : ∀ {P : String → Set} (seen : List String) (xs : List (String × ArithBlock))
            → All (λ q → P (proj₁ q)) xs → All (λ q → P (proj₁ q)) (dedup-go seen xs)
  dedup-all seen []             []       = []
  dedup-all seen ((s , b) ∷ bs) (p ∷ ps) =
    dedup-step seen s b bs (BLA.any (λ x → x == s) seen) p (dedup-all (s ∷ seen) bs ps) (dedup-all seen bs ps)

  tag : ArithBlock → String × ArithBlock
  tag b = block-symbol b , b

  tagged-asm : ∀ (bs : List ArithBlock) → All (λ q → AsmSym (proj₁ q)) (map tag bs)
  tagged-asm []       = []
  tagged-asm (b ∷ bs) = once-symbol-own-asm (block-name (block-body b)) ∷ tagged-asm bs

  fst-all : ∀ {P : String → Set} (xs : List (String × ArithBlock)) → All (λ q → P (proj₁ q)) xs → All P (map proj₁ xs)
  fst-all []       []       = []
  fst-all (x ∷ xs) (p ∷ ps) = p ∷ fst-all xs ps

block-syms-asm : ∀ (bs : List ArithBlock) → All AsmSym (block-syms bs)
block-syms-asm bs = fst-all {AsmSym} (dedup-blocks (map tag bs)) (dedup-all {AsmSym} [] (map tag bs) (tagged-asm bs))

------------------------------------------------------------------------
-- THE THEOREMS
------------------------------------------------------------------------

private
  heap-asm : AsmSym heap-symbol
  heap-asm = tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

  start-asm : AsmSym "_start"
  start-asm = tt , tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []

prog-defs-valid : ∀ (p : IRProgram) → All AsmSym (prog-defs p)
prog-defs-valid p = heap-asm ∷ start-asm ∷ ++⁺ (adefs-asm (image-of p)) (block-syms-asm (program-blocks p))

lib-defs-valid : ∀ (m : Module) → All AsmSym (lib-defs m)
lib-defs-valid m = heap-asm ∷ ++⁺ (adefs-asm (lib-image (moduleTable m))) (block-syms-asm (lib-blocks (moduleTable m)))

-- Every symbol a SigOp calls — itself or (a comparison) its block.
sigop-syms-asm : ∀ {A B} (si : SigOpInfo A B) (m : Maybe CmpOp) → All AsmSym (sigop-syms si m)
sigop-syms-asm si nothing  = once-symbol-path-asm (name si) ∷ []
sigop-syms-asm si (just c) = once-symbol-path-asm (name (cmp-block-info c)) ∷ []

calls-asm : ∀ (q : IRProgram) → All AsmSym (calls-of q)
calls-asm q = ++⁺ (leaf-syms-all h (main q)) (tbl (table q))
  where
    h : ∀ {A B} (si : SigOpInfo A B) → All AsmSym (sigop-syms si (cmp-of (sem si)))
    h si = sigop-syms-asm si (cmp-of (sem si))
    tbl : ∀ (es : List IRFun) → All AsmSym (Data.List.concatMap (λ e → leaf-syms (fbody e)) es)
    tbl []       = []
    tbl (e ∷ es) = ++⁺ (leaf-syms-all h (fbody e)) (tbl es)

externs-valid : ∀ (p : IRProgram) → All AsmSym (externs-of p)
externs-valid p = filter⁺ (is-extern? p) (calls-asm (rewrite-program p))
