-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Arith.Backend.RiscV64.Emit
--
-- Plan 0.53 — RISC-V 64 arith-block emitter. Mirrors
-- `Once.Arith.Backend.X86-64.Emit`: translate the arch-independent arith
-- `XInstr` IR to RV64 assembly text and assemble a leaf block subroutine
-- (prologue + body + epilogue).
--
-- Calling convention (matching the rest of Once's RV64 codegen):
--   - `t0` holds the block input value pointer (Input1). A primitive Int
--     lives at `0(t0)`; a nested pair's `Fst`/`Snd` map to byte offsets
--     `0` / `8`.
--   - The Int result is returned in `a0` (Output).
--   - `t1-t4` are the abstract reg file (`AbsReg 0..3`); `a0` doubles as
--     the path-walk scratch. All are caller-saved at the SigOp call site.
--   - Scratch stack slots live at `8*slot(sp)` after the prologue reserves
--     `8 * required-scratch` bytes. The block is a leaf (no calls), so it
--     needs no `ra` save.
------------------------------------------------------------------------

module Once.Arith.Backend.RiscV64.Emit where

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

-- The 4 abstract arith registers → RV64 temporaries (free within a leaf
-- block; the main codegen's uses of t1 are all closure-call-local).
reg-text : XReg → String
reg-text XR12 = "t1"
reg-text XR13 = "t2"
reg-text XR14 = "t3"
reg-text XR15 = "t4"

-- | A scratch slot lives at `8*slot(sp)` within the reserved frame.
scratch-text : XScratch → String
scratch-text record { slot = s } =
  showℕ (8 * s) ++ "(sp)"

------------------------------------------------------------------------
-- Per-instruction text
------------------------------------------------------------------------

instr-text : XInstr → String
instr-text (Xmov-imm dst z)   = "    li " ++ reg-text dst ++ ", " ++ showℤ z ++ "\n"
instr-text (Xmov-rr dst src)  = "    mv " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Xmov-r-m s src)   = "    sd " ++ reg-text src ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-m-r dst s)   = "    ld " ++ reg-text dst ++ ", " ++ scratch-text s ++ "\n"
instr-text (Xmov-arg dst path) = path-load-text dst path
  where
    -- Byte offset for one path step (matches CCC's pair layout).
    side-offset : Side → String
    side-offset Fst = "0"
    side-offset Snd = "8"

    -- Walk intermediate steps using a0 as base; final step lands in dst.
    walk-a0-rest : XReg → InputPath → String
    walk-a0-rest dst (s ∷ []) =
      "    ld " ++ reg-text dst ++ ", " ++ side-offset s ++ "(a0)\n"
    walk-a0-rest dst (s ∷ ss) =
      "    ld a0, " ++ side-offset s ++ "(a0)\n" ++ walk-a0-rest dst ss
    walk-a0-rest dst []       = ""

    -- Top-level path walker. `[]` = the input pointer t0 IS the value.
    path-load-text : XReg → InputPath → String
    path-load-text dst []         =
      "    mv " ++ reg-text dst ++ ", t0\n"
    path-load-text dst (s ∷ [])   =
      "    ld " ++ reg-text dst ++ ", " ++ side-offset s ++ "(t0)\n"
    path-load-text dst (s ∷ rest) =
      "    ld a0, " ++ side-offset s ++ "(t0)\n" ++
      walk-a0-rest dst rest
instr-text (Xadd-rr dst src)  = "    add " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Xsub-rr dst src)  = "    sub " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Ximul-rr dst src) = "    mul " ++ reg-text dst ++ ", " ++ reg-text dst ++ ", " ++ reg-text src ++ "\n"
instr-text (Xneg-r dst)       = "    neg " ++ reg-text dst ++ ", " ++ reg-text dst ++ "\n"
instr-text (Xmov-out src)     = "    mv a0, " ++ reg-text src ++ "\n"

program-text : XProgram → String
program-text []       = ""
program-text (i ∷ is) = instr-text i ++ program-text is

------------------------------------------------------------------------
-- Block subroutine emission
------------------------------------------------------------------------

-- | A complete arith-block subroutine. Leaf (no calls) ⇒ no ra save.
--
--   <sym>:
--       addi sp, sp, -N      ; reserve scratch (N = 8 * required-scratch)
--       <emitted instructions>
--       addi sp, sp, N
--       ret
emit-arith-block : (sym : String) → ArithBlock → String
emit-arith-block sym blk =
  let n     = required-scratch (block-body blk)
      pad   = showℕ (8 * n)
      instr = emit-program (compile-abs (block-body blk))
  in sym ++ ":\n" ++
     "    addi sp, sp, -" ++ pad ++ "\n" ++
     program-text instr ++
     "    addi sp, sp, " ++ pad ++ "\n" ++
     "    ret\n\n"

------------------------------------------------------------------------
-- Block-list emission
------------------------------------------------------------------------

arith-block-symbol : ArithBlock → String
arith-block-symbol blk = once-symbol-own (block-name (block-body blk))

emit-arith-blocks : List ArithBlock → String
emit-arith-blocks []       = ""
emit-arith-blocks (b ∷ bs) =
  ".globl " ++ arith-block-symbol b ++ "\n" ++
  emit-arith-block (arith-block-symbol b) b ++
  emit-arith-blocks bs
