------------------------------------------------------------------------
-- Once.CCC.Target.X86v3.Emit
--
-- Assembly text emission for CCC IR.
-- Chains CodeGen (IR → Program) and X86.Emit (Program → String).
--
-- This reuses the Target.X86.Emit module since the instruction set is
-- identical. The CCC IR adds free-heap to Once.IR, which CodeGen handles.
------------------------------------------------------------------------

module Once.CCC.Target.X86v3.Emit where

open import Data.String using (String)

-- Import code generation (X86v3.IR → Program)
open import Once.CCC.Target.X86v3.CodeGen using (compile-ir)

-- Import emission (Program → String) - reuse X86 pretty-printer
open import Once.Target.X86.Emit using (programToText)

-- Import X86v3 IR
open import Once.CCC.IR using (IR)

------------------------------------------------------------------------
-- End-to-end compilation: X86v3.IR → assembly text
------------------------------------------------------------------------

-- | Compile X86v3 IR to x86-64 assembly text
-- Input: X86v3 IR morphism
-- Output: GAS-compatible assembly text (AT&T syntax)
compileX86v3ToText : ∀ {A B} → IR A B → String
compileX86v3ToText ir = programToText (compile-ir ir)
