-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.X86-64.Emit
--
-- Plan 0.20 Phase G — translate the arith subsystem's `XInstr`
-- subset to AT&T-syntax x86-64 assembly text, and assemble a full
-- block subroutine (prologue + body + epilogue) ready to concatenate
-- after the main program text.
--
-- Calling convention (SysV / matching the rest of Once's codegen):
--   - `%rdi` holds the *block input value pointer*. For a primitive
--     `Int` input the value lives at `0(%rdi)`; for a nested pair the
--     `Fst`/`Snd` walk maps to byte offsets `0` and `+8`.
--   - The block's `Int` result is returned in `%rax` per the SysV
--     return-value convention. The wrapping `SigOp arith.block.*`
--     call site treats the result the same way `compile-const`
--     emits its integer literals.
--   - `%r12-%r15` are the abstract reg file (`AbsReg 0..3`).
--     `Xmov-imm` / `Xmov-arg` / `Xmov-rr` write them; `Xadd-rr`
--     etc. operate in place. None of them are callee-saved across
--     this call: the block does not modify CCC's normal callee-saved
--     register set because (a) the wider compiler reserves
--     `r12-r15` as scratch already, and (b) the block is invoked
--     via a SigOp call site that, like any other SigOp, treats
--     these registers as caller-saved.
--   - Scratch stack slots are addressed via `[%rsp - 8*(slot+1)]`
--     after the prologue subtracts `8 * required-scratch` from
--     `%rsp`. The reservation matches `Once.Arith.Backend.XInstr.Syntax`'s
--     comment.
------------------------------------------------------------------------

module Once.Arith.Backend.X86-64.Emit where

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.Nat using (ℕ; suc; _*_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)

open import Once.Arith.Backend.XInstr.Syntax
open import Once.Arith.Backend.XInstr.CodeGen using (emit-program)
open import Once.Arith.Machine.AbsState using (InputPath; Side; Fst; Snd)
open import Once.Arith.Machine.Compile using (compile-abs; required-scratch)
open import Once.Arith.Machine.IR using (MArithIR; ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-shape; block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Target.Symbol using (once-symbol-own)

------------------------------------------------------------------------
-- Register / scratch text
------------------------------------------------------------------------

reg-text : XReg → String
reg-text XR12 = "%r12"
reg-text XR13 = "%r13"
reg-text XR14 = "%r14"
reg-text XR15 = "%r15"

-- | A scratch slot lives at `[%rsp - 8*(slot+1)]` once the prologue
-- has reserved `8 * required-scratch` bytes below the original
-- %rsp.
scratch-text : XScratch → String
scratch-text record { slot = s } =
  "-" ++ showℕ (8 * suc s) ++ "(%rsp)"

------------------------------------------------------------------------
-- Per-instruction text
------------------------------------------------------------------------

instr-text : XInstr → String
instr-text (Xmov-imm dst z)   = "    movq $" ++ showℤ z ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-rr dst src)  = "    movq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-r-m s src)   = "    movq " ++ reg-text src ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-m-r dst s)   = "    movq " ++ scratch-text s ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-arg dst path) = path-load-text dst path
  where
    -- | Byte offset for one path step. `Fst` is offset 0, `Snd` is
    -- offset 8 — matching CCC's pair layout (compose `fst`/`snd`
    -- compile to `mov rax, [rdi]` / `mov rax, [rdi+8]`).
    side-offset : Side → String
    side-offset Fst = "0"
    side-offset Snd = "8"

    -- | Walk an intermediate path step using `%rax` as scratch.
    -- After the first step `%rax` holds the current "base"; each
    -- intermediate step reads `offset(%rax)` back into `%rax`. The
    -- final step lands in `dst`.
    walk-rax-rest : XReg → InputPath → String
    walk-rax-rest dst (s ∷ []) =
      "    movq " ++ side-offset s ++ "(%rax), " ++ reg-text dst ++ "\n"
    walk-rax-rest dst (s ∷ ss) =
      "    movq " ++ side-offset s ++ "(%rax), %rax\n" ++ walk-rax-rest dst ss
    -- Path [] inside an intermediate walk is unreachable for shapes
    -- that the recogniser produces; treat as a no-op fallback.
    walk-rax-rest dst []       = ""

    -- | Top-level path walker.
    --
    -- - `[]` (whole input): the block's `%rdi` IS the value (Int
    --   passed by-value through the SigOp call site). Move it to
    --   `dst`.
    -- - `[s]` (one hop): direct `mov dst, offset(%rdi)`.
    -- - `s :: rest` (chained): bootstrap into `%rax`, then walk the
    --   rest. Each `s :: rest` step does one memory dereference,
    --   matching CCC's `fst`/`snd` compose chain exactly.
    path-load-text : XReg → InputPath → String
    path-load-text dst []         =
      "    movq %rdi, " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ [])   =
      "    movq " ++ side-offset s ++ "(%rdi), " ++ reg-text dst ++ "\n"
    path-load-text dst (s ∷ rest) =
      "    movq " ++ side-offset s ++ "(%rdi), %rax\n" ++
      walk-rax-rest dst rest
instr-text (Xadd-rr dst src)  = "    addq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xsub-rr dst src)  = "    subq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Ximul-rr dst src) = "    imulq " ++ reg-text src ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xneg-r dst)       = "    negq " ++ reg-text dst ++ "\n"
instr-text (Xmov-out src)     = "    movq " ++ reg-text src ++ ", %rax\n"

program-text : XProgram → String
program-text []       = ""
program-text (i ∷ is) = instr-text i ++ program-text is

------------------------------------------------------------------------
-- Block subroutine emission
------------------------------------------------------------------------

-- | Emit a complete arith-block subroutine. The symbol must match
-- the one the call site emits (`once_arith.block.<digest>`); the
-- caller passes that pre-mangled symbol in.
--
-- Layout:
--
--   <sym>:
--       subq $N, %rsp        ; reserve scratch (N = 8 * required-scratch)
--       <emitted instructions>
--       addq $N, %rsp
--       ret
--
-- The block is frameless w.r.t. `%rbp` — like the rest of Once's
-- codegen post-Plan 0.2.4.5 D1. `%rsp` is the only stack pointer
-- the block touches; the prologue's `subq` and epilogue's `addq`
-- are perfectly balanced so the call site sees no stack drift.
emit-arith-block : (sym : String) → ArithBlock → String
emit-arith-block sym blk =
  let n     = required-scratch (block-body blk)
      pad   = showℕ (8 * n)
      instr = emit-program (compile-abs (block-body blk))
  in sym ++ ":\n" ++
     "    subq $" ++ pad ++ ", %rsp\n" ++
     program-text instr ++
     "    addq $" ++ pad ++ ", %rsp\n" ++
     "    ret\n\n"

------------------------------------------------------------------------
-- Block-list emission
------------------------------------------------------------------------

-- | The canonical assembly symbol for an `ArithBlock`. Mirrors the
-- name `block-info` puts in the `SigOpInfo` (`bare (block-name …)` =
-- `canonical [block-name]`), mangled through `once-symbol-own` =
-- `once-symbol-path ∘ canonical ∘ [_]` to match `compile-sigOp`'s
-- `once-symbol-path` call-site emission (Plan 0.50 — legacy `once-symbol`
-- left the dots un-encoded, mismatching the call).
arith-block-symbol : ArithBlock → String
arith-block-symbol blk = once-symbol-own (block-name (block-body blk))

-- | Emit a list of arith blocks as concatenated assembly text. Each
-- block becomes a `<once_arith.block.<digest>>:` subroutine; dedup
-- by symbol is the caller's responsibility (the rewrite pass may
-- discover the same block at multiple call sites).
emit-arith-blocks : List ArithBlock → String
emit-arith-blocks []       = ""
emit-arith-blocks (b ∷ bs) =
  ".globl " ++ arith-block-symbol b ++ "\n" ++
  emit-arith-block (arith-block-symbol b) b ++
  emit-arith-blocks bs
