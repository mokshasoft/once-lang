{-|
Module      : Once.Backend.X86.StackAlloc
Description : Stack allocation support for x86-64 backend
Copyright   : (c) 2024
License     : GPL-2.0

This module demonstrates how to integrate escape analysis with the x86-64 backend
for optimized memory allocation. Values that don't escape can be allocated on the
stack (faster) instead of the heap (slower).

IMPORTANT: This is a demonstration module showing how stack allocation would work.
Full integration requires threading AllocMode through the IR type.
-}

module Once.Backend.X86.StackAlloc
  ( AllocMode(..)
  , generateWithAlloc
  , allocatePair
  , allocateSum
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- | Allocation mode determined by escape analysis
data AllocMode = Stack | Heap
  deriving (Eq, Show)

-- | Generate assembly for pair allocation with specified mode
--
-- Stack allocation:
--   - Uses SUB RSP to allocate on stack
--   - Very fast, no malloc overhead
--   - Must ensure value doesn't outlive function
--
-- Heap allocation:
--   - Calls malloc to allocate on heap
--   - Slower due to malloc overhead
--   - Safe for escaping values
allocatePair :: AllocMode -> Text -> Text -> Text -> Int -> [Text]
allocatePair Stack inputReg tempReg outputReg labelCtr =
  [ "    ; pair (stack allocation)"
  , "    sub rsp, 16              ; Allocate 16 bytes on stack"
  , "    mov " <> outputReg <> ", rsp      ; Output = stack pointer"
  ]

allocatePair Heap inputReg tempReg outputReg labelCtr =
  [ "    ; pair (heap allocation)"
  , "    mov rdi, 16              ; Size = 16 bytes"
  , "    call malloc              ; Allocate on heap"
  , "    test rax, rax            ; Check for allocation failure"
  , "    jz .alloc_fail_" <> T.pack (show labelCtr)
  , "    mov " <> outputReg <> ", rax      ; Output = heap pointer"
  ]

-- | Generate assembly for sum (tagged union) allocation
allocateSum :: AllocMode -> Bool -> Text -> Text -> Int -> [Text]
allocateSum Stack isRight inputReg outputReg labelCtr =
  [ "    ; " <> (if isRight then "inr" else "inl") <> " (stack allocation)"
  , "    sub rsp, 16              ; Allocate 16 bytes on stack"
  , "    mov qword [rsp], " <> (if isRight then "1" else "0") <> "  ; Set tag"
  , "    mov [rsp+8], " <> inputReg <> "     ; Set value"
  , "    mov " <> outputReg <> ", rsp      ; Output = stack pointer"
  ]

allocateSum Heap isRight inputReg outputReg labelCtr =
  [ "    ; " <> (if isRight then "inr" else "inl") <> " (heap allocation)"
  , "    mov rdi, 16              ; Size = 16 bytes"
  , "    call malloc              ; Allocate on heap"
  , "    test rax, rax            ; Check for allocation failure"
  , "    jz .alloc_fail_" <> T.pack (show labelCtr)
  , "    mov qword [rax], " <> (if isRight then "1" else "0") <> "  ; Set tag"
  , "    mov [rax+8], " <> inputReg <> "     ; Set value"
  , "    mov " <> outputReg <> ", rax      ; Output = heap pointer"
  ]

-- | Generate code with escape analysis-based allocation
-- This demonstrates how the backend would use AllocMode information
generateWithAlloc :: AllocMode -> Text -> [Text]
generateWithAlloc mode name =
  [ "; Function: " <> name
  , "; Allocation mode: " <> T.pack (show mode)
  , ""
  , "section .text"
  , "global once_" <> name
  , "extern malloc                ; Import malloc for heap allocation"
  , ""
  , "once_" <> name <> ":"
  , "    push rbp"
  , "    mov rbp, rsp"
  , "    push r12                 ; Save callee-saved registers"
  , "    push r13"
  , "    push r14"
  , "    push r15"
  , ""
  ] ++
  examplePairAllocation mode ++
  [ ""
  , "    ; Cleanup and return"
  , "    pop r15"
  , "    pop r14"
  , "    pop r13"
  , "    pop r12"
  , "    pop rbp"
  , "    ret"
  , ""
  , ".alloc_fail_0:"
  , "    ; Handle allocation failure"
  , "    mov rax, -1              ; Return error code"
  , "    jmp .cleanup"
  , ""
  , ".cleanup:"
  , "    pop r15"
  , "    pop r14"
  , "    pop r13"
  , "    pop r12"
  , "    pop rbp"
  , "    ret"
  ]

-- | Example showing difference between stack and heap allocation
examplePairAllocation :: AllocMode -> [Text]
examplePairAllocation mode =
  [ "    ; Example: allocate a pair (x, y)" ] ++
  allocatePair mode "rdi" "r14" "rax" 0 ++
  [ "    ; Store values in the pair"
  , "    mov [rax], rdi           ; Store first element"
  , "    mov [rax+8], rsi         ; Store second element"
  ]

{-
Performance Comparison:

Stack allocation (non-escaping values):
- SUB RSP, 16:     1 cycle
- Total:           1 cycle + memory stores

Heap allocation (escaping values):
- CALL malloc:     ~100-1000 cycles (system call overhead)
- Error checking:  2-3 cycles
- Total:           100+ cycles + memory stores

The escape analysis optimization can provide 100x speedup for
non-escaping allocations!

Integration Plan:
1. Modify formal/Once/IR.agda to thread AllocMode through Pair/Inl/Inr
2. Update compiler/src/Once/IR.hs to include AllocMode in constructors
3. Modify elaboration to use escape analysis to set AllocMode
4. Update x86 backend to use this module for allocation
-}