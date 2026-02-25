------------------------------------------------------------------------
-- Once.Target.AArch64.Emit
--
-- Assembly text emission for AArch64 instructions.
-- Converts instruction data types to GAS-compatible assembly text.
--
-- This is extracted via MAlonzo to provide verified pretty-printing.
------------------------------------------------------------------------

module Once.Target.AArch64.Emit where

open import Once.Target.AArch64.Syntax

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map; foldr)

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

-- | Join strings with newlines
unlines : List String → String
unlines [] = ""
unlines (x ∷ []) = x
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

------------------------------------------------------------------------
-- Register emission
------------------------------------------------------------------------

-- | Convert register to assembly text
regToText : Reg → String
regToText x0  = "x0"
regToText x1  = "x1"
regToText x2  = "x2"
regToText x3  = "x3"
regToText x4  = "x4"
regToText x5  = "x5"
regToText x6  = "x6"
regToText x7  = "x7"
regToText x8  = "x8"
regToText x9  = "x9"
regToText x10 = "x10"
regToText x11 = "x11"
regToText x12 = "x12"
regToText x13 = "x13"
regToText x14 = "x14"
regToText x15 = "x15"
regToText x16 = "x16"
regToText x17 = "x17"
regToText x18 = "x18"
regToText x19 = "x19"
regToText x20 = "x20"
regToText x21 = "x21"
regToText x22 = "x22"
regToText x23 = "x23"
regToText x24 = "x24"
regToText x25 = "x25"
regToText x26 = "x26"
regToText x27 = "x27"
regToText x28 = "x28"
regToText x29 = "x29"
regToText x30 = "x30"

------------------------------------------------------------------------
-- Memory operand emission
------------------------------------------------------------------------

-- | Convert memory operand to assembly text
memToText : Mem → String
memToText (base r) = "[" ++ regToText r ++ "]"
memToText (base+imm r n) = "[" ++ regToText r ++ ", #" ++ show n ++ "]"
memToText (sp+imm n) = "[sp, #" ++ show n ++ "]"

------------------------------------------------------------------------
-- Operand emission
------------------------------------------------------------------------

-- | Convert operand to assembly text (for mov/add/sub/cmp)
operandToText : Operand → String
operandToText (reg r) = regToText r
operandToText (mem m) = memToText m
operandToText (imm n) = "#" ++ show n

------------------------------------------------------------------------
-- Instruction emission
------------------------------------------------------------------------

-- | Convert a single instruction to assembly text (GAS syntax)
instrToText : Instr → String

-- Data movement
instrToText (mov rd op) = "    mov " ++ regToText rd ++ ", " ++ operandToText op
instrToText (ldr rd m) = "    ldr " ++ regToText rd ++ ", " ++ memToText m
instrToText (str rs m) = "    str " ++ regToText rs ++ ", " ++ memToText m

-- Pair load/store
instrToText (ldp r1 r2 m) = "    ldp " ++ regToText r1 ++ ", " ++ regToText r2 ++ ", " ++ memToText m
instrToText (stp r1 r2 m) = "    stp " ++ regToText r1 ++ ", " ++ regToText r2 ++ ", " ++ memToText m

-- Arithmetic
instrToText (add rd rn op) = "    add " ++ regToText rd ++ ", " ++ regToText rn ++ ", " ++ operandToText op
instrToText (sub rd rn op) = "    sub " ++ regToText rd ++ ", " ++ regToText rn ++ ", " ++ operandToText op

-- Comparison
instrToText (cmp rn op) = "    cmp " ++ regToText rn ++ ", " ++ operandToText op

-- Branches (labels are numeric)
instrToText (b n) = "    b .L" ++ show n
instrToText (b-eq n) = "    b.eq .L" ++ show n
instrToText (b-ne n) = "    b.ne .L" ++ show n

-- Subroutine calls
instrToText (bl n) = "    bl .L" ++ show n
instrToText (blr r) = "    blr " ++ regToText r
instrToText ret = "    ret"

-- Stack operations
instrToText (sub-sp n) = "    sub sp, sp, #" ++ show n
instrToText (add-sp n) = "    add sp, sp, #" ++ show n
instrToText (mov-from-sp rd) = "    mov " ++ regToText rd ++ ", sp"

-- Special
instrToText nop = "    nop"
instrToText (brk n) = "    brk #" ++ show n

-- Zero register store (for tag=0 in sums)
instrToText (str-zr m) = "    str xzr, " ++ memToText m

-- PC-relative address
instrToText (adr rd n) = "    adr " ++ regToText rd ++ ", .L" ++ show n

-- Labels (pseudo-instruction)
instrToText (label n) = ".L" ++ show n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

-- | Convert a program (list of instructions) to assembly text
programToText : Program → String
programToText instrs = unlines (map instrToText instrs)
