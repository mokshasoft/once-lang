------------------------------------------------------------------------
-- Once.Backend.RiscV64.Emit
--
-- Assembly text emission for RISC-V 64-bit instructions.
-- Converts instruction data types to GAS-compatible assembly text.
--
-- This is extracted via MAlonzo to provide verified pretty-printing.
------------------------------------------------------------------------

module Once.Backend.RiscV64.Emit where

open import Once.Backend.RiscV64.Syntax

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
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

-- | Convert signed integer to string
showℤ : ℤ → String
showℤ (+ n) = showℕ n
showℤ (-[1+ n ]) = "-" ++ showℕ (ℕ.suc n)
  where import Data.Nat as ℕ

------------------------------------------------------------------------
-- Register emission
------------------------------------------------------------------------

-- | Convert register to assembly text (ABI names)
regToText : Reg → String
regToText zero = "zero"
regToText ra   = "ra"
regToText sp   = "sp"
regToText gp   = "gp"
regToText tp   = "tp"
regToText t0   = "t0"
regToText t1   = "t1"
regToText t2   = "t2"
regToText s0   = "s0"
regToText s1   = "s1"
regToText a0   = "a0"
regToText a1   = "a1"
regToText a2   = "a2"
regToText a3   = "a3"
regToText a4   = "a4"
regToText a5   = "a5"
regToText a6   = "a6"
regToText a7   = "a7"
regToText s2   = "s2"
regToText s3   = "s3"
regToText s4   = "s4"
regToText s5   = "s5"
regToText s6   = "s6"
regToText s7   = "s7"
regToText s8   = "s8"
regToText s9   = "s9"
regToText s10  = "s10"
regToText s11  = "s11"
regToText t3   = "t3"
regToText t4   = "t4"
regToText t5   = "t5"
regToText t6   = "t6"

------------------------------------------------------------------------
-- Instruction emission
------------------------------------------------------------------------

-- | Convert a single instruction to assembly text (GAS syntax)
instrToText : Instr → String

-- R-type: Register-Register Operations
instrToText (add rd rs1 rs2) = "    add " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (sub rd rs1 rs2) = "    sub " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (and rd rs1 rs2) = "    and " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (or rd rs1 rs2) = "    or " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (xor rd rs1 rs2) = "    xor " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (sll rd rs1 rs2) = "    sll " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (srl rd rs1 rs2) = "    srl " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (sra rd rs1 rs2) = "    sra " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (slt rd rs1 rs2) = "    slt " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2
instrToText (sltu rd rs1 rs2) = "    sltu " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ regToText rs2

-- I-type: Immediate Operations
instrToText (addi rd rs1 imm) = "    addi " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℤ imm
instrToText (andi rd rs1 imm) = "    andi " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℤ imm
instrToText (ori rd rs1 imm) = "    ori " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℤ imm
instrToText (xori rd rs1 imm) = "    xori " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℤ imm
instrToText (slti rd rs1 imm) = "    slti " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℤ imm
instrToText (sltiu rd rs1 imm) = "    sltiu " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℤ imm
instrToText (slli rd rs1 shamt) = "    slli " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℕ shamt
instrToText (srli rd rs1 shamt) = "    srli " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℕ shamt
instrToText (srai rd rs1 shamt) = "    srai " ++ regToText rd ++ ", " ++ regToText rs1 ++ ", " ++ showℕ shamt

-- Load instructions: ld rd, offset(rs1)
instrToText (ld rd offset rs1) = "    ld " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (lw rd offset rs1) = "    lw " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (lwu rd offset rs1) = "    lwu " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (lh rd offset rs1) = "    lh " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (lhu rd offset rs1) = "    lhu " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (lb rd offset rs1) = "    lb " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (lbu rd offset rs1) = "    lbu " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"

-- Store instructions: sd rs2, offset(rs1)
instrToText (sd rs2 offset rs1) = "    sd " ++ regToText rs2 ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (sw rs2 offset rs1) = "    sw " ++ regToText rs2 ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (sh rs2 offset rs1) = "    sh " ++ regToText rs2 ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"
instrToText (sb rs2 offset rs1) = "    sb " ++ regToText rs2 ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"

-- Conditional branches (using labels)
instrToText (beq rs1 rs2 offset) = "    beq " ++ regToText rs1 ++ ", " ++ regToText rs2 ++ ", .L" ++ showℤ offset
instrToText (bne rs1 rs2 offset) = "    bne " ++ regToText rs1 ++ ", " ++ regToText rs2 ++ ", .L" ++ showℤ offset
instrToText (blt rs1 rs2 offset) = "    blt " ++ regToText rs1 ++ ", " ++ regToText rs2 ++ ", .L" ++ showℤ offset
instrToText (bge rs1 rs2 offset) = "    bge " ++ regToText rs1 ++ ", " ++ regToText rs2 ++ ", .L" ++ showℤ offset
instrToText (bltu rs1 rs2 offset) = "    bltu " ++ regToText rs1 ++ ", " ++ regToText rs2 ++ ", .L" ++ showℤ offset
instrToText (bgeu rs1 rs2 offset) = "    bgeu " ++ regToText rs1 ++ ", " ++ regToText rs2 ++ ", .L" ++ showℤ offset

-- Upper immediate
instrToText (lui rd imm) = "    lui " ++ regToText rd ++ ", " ++ showℤ imm
instrToText (auipc rd imm) = "    auipc " ++ regToText rd ++ ", " ++ showℤ imm

-- Jumps
instrToText (jal rd offset) = "    jal " ++ regToText rd ++ ", .L" ++ showℤ offset
instrToText (jalr rd rs1 offset) = "    jalr " ++ regToText rd ++ ", " ++ showℤ offset ++ "(" ++ regToText rs1 ++ ")"

-- Pseudo-instructions
instrToText (li rd imm) = "    li " ++ regToText rd ++ ", " ++ showℤ imm
instrToText (mv rd rs) = "    mv " ++ regToText rd ++ ", " ++ regToText rs
instrToText (j offset) = "    j .L" ++ showℤ offset
instrToText (call offset) = "    call .L" ++ showℤ offset
instrToText ret = "    ret"
instrToText nop = "    nop"
instrToText ebreak = "    ebreak"

-- Labels (pseudo-instruction for assembly targets)
instrToText (label n) = ".L" ++ showℕ n ++ ":"

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

-- | Convert a program (list of instructions) to assembly text
programToText : Program → String
programToText instrs = unlines (map instrToText instrs)
