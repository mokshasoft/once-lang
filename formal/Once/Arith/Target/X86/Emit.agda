------------------------------------------------------------------------
-- Once.Arith.Target.X86.Emit
--
-- Assembly text emission for x86-64 arithmetic instructions.
-- Converts ArithInstr to GAS-compatible assembly text (AT&T syntax).
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
------------------------------------------------------------------------

module Once.Arith.Target.X86.Emit where

open import Once.Arith.Target.X86.Syntax

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Integer.Show renaming (show to showℤ)
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
-- GPR emission (AT&T syntax with % prefix)
------------------------------------------------------------------------

gprToText : GPReg → String
gprToText rax = "%rax"
gprToText rbx = "%rbx"
gprToText rcx = "%rcx"
gprToText rdx = "%rdx"
gprToText rsi = "%rsi"
gprToText rdi = "%rdi"
gprToText r8  = "%r8"
gprToText r9  = "%r9"
gprToText r10 = "%r10"
gprToText r11 = "%r11"

-- | 8-bit register names for setcc
gpr8ToText : GPReg → String
gpr8ToText rax = "%al"
gpr8ToText rbx = "%bl"
gpr8ToText rcx = "%cl"
gpr8ToText rdx = "%dl"
gpr8ToText rsi = "%sil"
gpr8ToText rdi = "%dil"
gpr8ToText r8  = "%r8b"
gpr8ToText r9  = "%r9b"
gpr8ToText r10 = "%r10b"
gpr8ToText r11 = "%r11b"

------------------------------------------------------------------------
-- XMM emission
------------------------------------------------------------------------

xmmToText : XMMReg → String
xmmToText xmm0  = "%xmm0"
xmmToText xmm1  = "%xmm1"
xmmToText xmm2  = "%xmm2"
xmmToText xmm3  = "%xmm3"
xmmToText xmm4  = "%xmm4"
xmmToText xmm5  = "%xmm5"
xmmToText xmm6  = "%xmm6"
xmmToText xmm7  = "%xmm7"
xmmToText xmm8  = "%xmm8"
xmmToText xmm9  = "%xmm9"
xmmToText xmm10 = "%xmm10"
xmmToText xmm11 = "%xmm11"
xmmToText xmm12 = "%xmm12"
xmmToText xmm13 = "%xmm13"
xmmToText xmm14 = "%xmm14"
xmmToText xmm15 = "%xmm15"

------------------------------------------------------------------------
-- Memory operand emission
------------------------------------------------------------------------

memToText : ArithMem → String
memToText (base r) = "(" ++ gprToText r ++ ")"
memToText (base+disp r n) = showℕ n ++ "(" ++ gprToText r ++ ")"

------------------------------------------------------------------------
-- Integer operand emission
------------------------------------------------------------------------

intOpToText : IntOperand → String
intOpToText (regI r) = gprToText r
intOpToText (memI m) = memToText m
intOpToText (immI n) = "$" ++ showℤ n

------------------------------------------------------------------------
-- Float operand emission
------------------------------------------------------------------------

floatOpToText : FloatOperand → String
floatOpToText (regF r) = xmmToText r
floatOpToText (memF m) = memToText m

------------------------------------------------------------------------
-- Condition code emission
------------------------------------------------------------------------

ccToText : CondCode → String
ccToText cc-e  = "e"
ccToText cc-ne = "ne"
ccToText cc-l  = "l"
ccToText cc-le = "le"
ccToText cc-g  = "g"
ccToText cc-ge = "ge"

------------------------------------------------------------------------
-- Integer instruction emission
------------------------------------------------------------------------

intInstrToText : IntInstr → String
-- Data movement
intInstrToText (movI dst src) =
  "    movq " ++ intOpToText src ++ ", " ++ gprToText dst
-- Arithmetic
intInstrToText (addI dst src) =
  "    addq " ++ intOpToText src ++ ", " ++ gprToText dst
intInstrToText (subI dst src) =
  "    subq " ++ intOpToText src ++ ", " ++ gprToText dst
intInstrToText (imulI dst src) =
  "    imulq " ++ intOpToText src ++ ", " ++ gprToText dst
intInstrToText (negI dst) =
  "    negq " ++ gprToText dst
-- Division
intInstrToText cqo = "    cqo"
intInstrToText (idivI src) =
  "    idivq " ++ intOpToText src
-- Stack
intInstrToText (pushI src) =
  "    pushq " ++ gprToText src
intInstrToText (popI dst) =
  "    popq " ++ gprToText dst
-- Comparison
intInstrToText (cmpI dst src) =
  "    cmpq " ++ intOpToText src ++ ", " ++ gprToText dst
intInstrToText (setccI cc dst) =
  "    set" ++ ccToText cc ++ " " ++ gpr8ToText dst
intInstrToText (movzxI dst src) =
  "    movzbl " ++ gpr8ToText src ++ ", " ++ gprToText dst

------------------------------------------------------------------------
-- Float instruction emission
------------------------------------------------------------------------

floatInstrToText : FloatInstr → String
-- Data movement
floatInstrToText (movss dst src) =
  "    movss " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (movsd dst src) =
  "    movsd " ++ floatOpToText src ++ ", " ++ xmmToText dst
-- Single-precision
floatInstrToText (addss dst src) =
  "    addss " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (subss dst src) =
  "    subss " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (mulss dst src) =
  "    mulss " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (divss dst src) =
  "    divss " ++ floatOpToText src ++ ", " ++ xmmToText dst
-- Double-precision
floatInstrToText (addsd dst src) =
  "    addsd " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (subsd dst src) =
  "    subsd " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (mulsd dst src) =
  "    mulsd " ++ floatOpToText src ++ ", " ++ xmmToText dst
floatInstrToText (divsd dst src) =
  "    divsd " ++ floatOpToText src ++ ", " ++ xmmToText dst
-- Negation
floatInstrToText (xorps dst src) =
  "    xorps " ++ xmmToText src ++ ", " ++ xmmToText dst
floatInstrToText (xorpd dst src) =
  "    xorpd " ++ xmmToText src ++ ", " ++ xmmToText dst
-- GPR to XMM
floatInstrToText (movqToXMM dst src) =
  "    movq " ++ gprToText src ++ ", " ++ xmmToText dst
-- Type conversion
floatInstrToText (cvtss2sd dst src) =
  "    cvtss2sd " ++ xmmToText src ++ ", " ++ xmmToText dst

------------------------------------------------------------------------
-- Unified instruction emission
------------------------------------------------------------------------

instrToText : ArithInstr → String
instrToText (intI i)   = intInstrToText i
instrToText (floatI f) = floatInstrToText f

------------------------------------------------------------------------
-- Program emission
------------------------------------------------------------------------

-- | Convert a program to assembly text
emitProgram : ArithProgram → String
emitProgram instrs = unlines (map instrToText instrs)
