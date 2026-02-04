------------------------------------------------------------------------
-- Once.Backend.X86.Emit
--
-- Assembly text emission for x86-64 instructions.
-- Converts instruction data types to GAS-compatible assembly text.
-- Uses AT&T syntax: op src, dst (as required by GNU assembler)
--
-- This is extracted via MAlonzo to provide verified pretty-printing.
------------------------------------------------------------------------

module Once.Backend.X86.Emit where

open import Once.Backend.X86.Syntax

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; map)

------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

-- | Join strings with newlines
unlines : List String → String
unlines [] = ""
unlines (x ∷ []) = x
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

------------------------------------------------------------------------
-- Register emission (AT&T syntax with % prefix)
------------------------------------------------------------------------

-- | Convert register to assembly text
regToText : Reg → String
regToText rax = "%rax"
regToText rbx = "%rbx"
regToText rcx = "%rcx"
regToText rdx = "%rdx"
regToText rsi = "%rsi"
regToText rdi = "%rdi"
regToText rbp = "%rbp"
regToText rsp = "%rsp"
regToText r8  = "%r8"
regToText r9  = "%r9"
regToText r10 = "%r10"
regToText r11 = "%r11"
regToText r12 = "%r12"
regToText r13 = "%r13"
regToText r14 = "%r14"
regToText r15 = "%r15"

------------------------------------------------------------------------
-- Memory operand emission (AT&T syntax: offset(%reg))
------------------------------------------------------------------------

-- | Convert memory operand to assembly text
memToText : Mem → String
memToText (base r) = "(" ++ regToText r ++ ")"
memToText (base+disp r n) = show n ++ "(" ++ regToText r ++ ")"
memToText (rip+disp n) = ".L" ++ show n ++ "(%rip)"

------------------------------------------------------------------------
-- Operand emission
------------------------------------------------------------------------

-- | Convert operand to assembly text
-- AT&T syntax: immediates have $ prefix, memory uses () notation
operandToText : Operand → String
operandToText (reg r) = regToText r
operandToText (mem m) = memToText m
operandToText (imm n) = "$" ++ show n

------------------------------------------------------------------------
-- Instruction emission (AT&T syntax: op src, dst)
------------------------------------------------------------------------

-- | Convert a single instruction to assembly text (GAS AT&T syntax)
instrToText : Instr → String

-- Data movement (64-bit operations use 'q' suffix)
-- AT&T syntax: movq src, dst
instrToText (mov dst src) = "    movq " ++ operandToText src ++ ", " ++ operandToText dst
instrToText (lea rd m) = "    leaq " ++ memToText m ++ ", " ++ regToText rd

-- Arithmetic
instrToText (add dst src) = "    addq " ++ operandToText src ++ ", " ++ operandToText dst
instrToText (sub dst src) = "    subq " ++ operandToText src ++ ", " ++ operandToText dst

-- Comparison
instrToText (cmp op1 op2) = "    cmpq " ++ operandToText op2 ++ ", " ++ operandToText op1
instrToText (test op1 op2) = "    testq " ++ operandToText op2 ++ ", " ++ operandToText op1

-- Control flow (labels are numeric with .L prefix)
instrToText (jmp n) = "    jmp .L" ++ show n
instrToText (je n) = "    je .L" ++ show n
instrToText (jne n) = "    jne .L" ++ show n
instrToText (call op) = "    call *" ++ operandToText op
instrToText ret = "    ret"

-- Stack operations
instrToText (push op) = "    pushq " ++ operandToText op
instrToText (pop r) = "    popq " ++ regToText r

-- Special
instrToText nop = "    nop"
instrToText ud2 = "    ud2"

-- Labels (pseudo-instruction)
instrToText (label n) = ".L" ++ show n ++ ":"

-- Opaque assembly (pass through from Contract)
instrToText (Opaque s) = s

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

-- | Convert a program (list of instructions) to assembly text
programToText : Program → String
programToText instrs = unlines (map instrToText instrs)
