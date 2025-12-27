{-# LANGUAGE RecordWildCards #-}
-- | x86-64 code generation for arithmetic expressions
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module generates x86-64 instructions from ArithIR,
-- mirroring the verified Agda implementation.
module Once.Arith.Backend.X86.CodeGen
  ( -- * Code generation
    compileArith
  , compileArithToAsm
    -- * Register allocation
  , AllocState (..)
  , initAlloc
    -- * Results
  , IntResult (..)
  , FloatResult (..)
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Int (Int64)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Once.Arith.IR
import Once.Arith.Backend.X86.Syntax
import Once.Arith.Backend.X86.Emit (emitProgram)

------------------------------------------------------------------------
-- Register allocation state
------------------------------------------------------------------------

-- | Available GPR registers for allocation (caller-saved)
-- We exclude RAX (return), RCX/RDX (division), RDI (first arg)
availableGPRs :: [GPReg]
availableGPRs = [R8, R9, R10, R11, RBX]

-- | Available XMM registers for allocation
availableXMMs :: [XMMReg]
availableXMMs = [XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7]

-- | Register allocation state
data AllocState = AllocState
  { nextGPR :: !Int           -- ^ Index into availableGPRs
  , nextXMM :: !Int           -- ^ Index into availableXMMs
  , varMap  :: Map Text GPReg -- ^ Variable to register mapping
  } deriving (Eq, Show)

-- | Initial allocation state
initAlloc :: AllocState
initAlloc = AllocState 0 0 Map.empty

-- | Get the nth GPR (wrapping if needed)
getGPR :: Int -> GPReg
getGPR n = availableGPRs !! (n `mod` length availableGPRs)

-- | Get the nth XMM
getXMM :: Int -> XMMReg
getXMM n = availableXMMs !! (n `mod` length availableXMMs)

-- | Allocate a GPR
allocGPR :: AllocState -> (GPReg, AllocState)
allocGPR st@AllocState{..} = (getGPR nextGPR, st { nextGPR = nextGPR + 1 })

-- | Allocate an XMM
allocXMM :: AllocState -> (XMMReg, AllocState)
allocXMM st@AllocState{..} = (getXMM nextXMM, st { nextXMM = nextXMM + 1 })

-- | Free a GPR (decrement counter)
freeGPR :: AllocState -> AllocState
freeGPR st@AllocState{..} = st { nextGPR = max 0 (nextGPR - 1) }

-- | Free an XMM
freeXMM :: AllocState -> AllocState
freeXMM st@AllocState{..} = st { nextXMM = max 0 (nextXMM - 1) }

------------------------------------------------------------------------
-- Code generation results
------------------------------------------------------------------------

-- | Result of compiling an integer expression
data IntResult = IntResult
  { intCode   :: ArithProgram  -- ^ Generated instructions
  , intResult :: GPReg         -- ^ Register holding result
  , intState  :: AllocState    -- ^ Updated allocation state
  } deriving (Eq, Show)

-- | Result of compiling a float expression
data FloatResult = FloatResult
  { floatCode   :: ArithProgram  -- ^ Generated instructions
  , floatResult :: XMMReg        -- ^ Register holding result
  , floatState  :: AllocState    -- ^ Updated allocation state
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- Integer code generation
------------------------------------------------------------------------

-- | Compile an integer arithmetic expression
compileInt :: ArithIR -> AllocState -> IntResult

-- Literal: load immediate into fresh register
compileInt (ALitInt _ n) st =
  let (r, st') = allocGPR st
  in IntResult
       { intCode   = [IntI (MovI r (ImmI (fromInteger n)))]
       , intResult = r
       , intState  = st'
       }

-- Variable: look up in varMap or load from memory
compileInt (AVar name _) st =
  case Map.lookup name (varMap st) of
    Just r  -> IntResult [] r st  -- Already in register
    Nothing ->
      let (r, st') = allocGPR st
          -- Placeholder: variables would be loaded from stack/memory
          -- For now, just allocate a register (caller must set it up)
      in IntResult
           { intCode   = [IntI (MovI r (MemI (Base RDI)))]
           , intResult = r
           , intState  = st' { varMap = Map.insert name r (varMap st') }
           }

-- Addition: compile both, add
compileInt (AAdd e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2 ++ [IntI (AddI r1 (RegI r2))]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Subtraction: compile both, subtract
compileInt (ASub e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2 ++ [IntI (SubI r1 (RegI r2))]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Multiplication: compile both, multiply
compileInt (AMul e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2 ++ [IntI (IMulI r1 (RegI r2))]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Division: uses RAX/RDX, more complex
compileInt (ADiv e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
      -- Move dividend to RAX, sign-extend, divide
      divCode =
        [ IntI (MovI RAX (RegI r1))  -- mov rax, r1
        , IntI Cqo                    -- cqo (sign-extend to rdx:rax)
        , IntI (IDivI (RegI r2))      -- idiv r2
        -- Result (quotient) is now in RAX
        , IntI (MovI r1 (RegI RAX))  -- mov r1, rax
        ]
  in IntResult
       { intCode   = intCode res1 ++ intCode res2 ++ divCode
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Modulo: similar to division but use remainder (RDX)
compileInt (AMod e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
      modCode =
        [ IntI (MovI RAX (RegI r1))  -- mov rax, r1
        , IntI Cqo                    -- cqo
        , IntI (IDivI (RegI r2))      -- idiv r2
        -- Remainder is in RDX
        , IntI (MovI r1 (RegI RDX))  -- mov r1, rdx
        ]
  in IntResult
       { intCode   = intCode res1 ++ intCode res2 ++ modCode
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Negation
compileInt (ANeg e) st =
  let res = compileInt e st
      r = intResult res
  in IntResult
       { intCode   = intCode res ++ [IntI (NegI r)]
       , intResult = r
       , intState  = intState res
       }

-- Comparison: compute difference, set flags (simplified)
compileInt (ACmp _ e1 e2) st =
  -- For now, just compute subtraction (flags would be set)
  compileInt (ASub e1 e2) st

-- Float literals/operations fall through to float path
compileInt (ALitFloat _ _) st = error "compileInt: got float literal"

------------------------------------------------------------------------
-- Float code generation
------------------------------------------------------------------------

-- | Compile a floating-point arithmetic expression
compileFloat :: ArithIR -> AllocState -> FloatResult

-- Float literal: need to load from memory (x86 can't mov imm to xmm)
-- For simplicity, we'll use a placeholder
compileFloat (ALitFloat ty d) st =
  let (r, st') = allocXMM st
      -- In practice, float literals are loaded from .rodata
      -- We emit a placeholder memory load
      instr = case ty of
        F32 -> FloatI (Movss r (MemF (Base RDI)))  -- Placeholder
        F64 -> FloatI (Movsd r (MemF (Base RDI)))  -- Placeholder
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = [instr]
       , floatResult = r
       , floatState  = st'
       }

-- Variable
compileFloat (AVar _ ty) st =
  let (r, st') = allocXMM st
      instr = case ty of
        F32 -> FloatI (Movss r (MemF (Base RDI)))
        F64 -> FloatI (Movsd r (MemF (Base RDI)))
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = [instr]
       , floatResult = r
       , floatState  = st'
       }

-- Addition
compileFloat (AAdd e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      addInstr = case ty of
        F32 -> FloatI (Addss r1 (RegF r2))
        F64 -> FloatI (Addsd r1 (RegF r2))
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [addInstr]
       , floatResult = r1
       , floatState  = freeXMM (floatState res2)
       }

-- Subtraction
compileFloat (ASub e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      subInstr = case ty of
        F32 -> FloatI (Subss r1 (RegF r2))
        F64 -> FloatI (Subsd r1 (RegF r2))
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [subInstr]
       , floatResult = r1
       , floatState  = freeXMM (floatState res2)
       }

-- Multiplication
compileFloat (AMul e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      mulInstr = case ty of
        F32 -> FloatI (Mulss r1 (RegF r2))
        F64 -> FloatI (Mulsd r1 (RegF r2))
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [mulInstr]
       , floatResult = r1
       , floatState  = freeXMM (floatState res2)
       }

-- Division
compileFloat (ADiv e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      divInstr = case ty of
        F32 -> FloatI (Divss r1 (RegF r2))
        F64 -> FloatI (Divsd r1 (RegF r2))
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [divInstr]
       , floatResult = r1
       , floatState  = freeXMM (floatState res2)
       }

-- Negation (xor with sign bit mask)
compileFloat (ANeg e) st =
  let ty = arithType e
      res = compileFloat e st
      r = floatResult res
      -- For negation, we'd xor with a sign bit mask
      -- This is a simplification - real impl needs the mask in a register
      negInstr = case ty of
        F32 -> FloatI (Xorps r r)  -- Placeholder (needs proper sign mask)
        F64 -> FloatI (Xorpd r r)  -- Placeholder
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res ++ [negInstr]
       , floatResult = r
       , floatState  = floatState res
       }

-- Mod not supported for floats
compileFloat (AMod _ _) _ = error "compileFloat: modulo not supported for floats"

-- Comparison
compileFloat (ACmp _ e1 e2) st = compileFloat (ASub e1 e2) st

-- Integer literals
compileFloat (ALitInt _ _) _ = error "compileFloat: got int literal"

------------------------------------------------------------------------
-- Main compilation entry point
------------------------------------------------------------------------

-- | Compile an arithmetic expression to x86-64 instructions
--
-- Result is left in RAX (integers) or XMM0 (floats)
compileArith :: ArithIR -> ArithProgram
compileArith expr =
  let ty = arithType expr
  in if isInteger ty
     then
       let res = compileInt expr initAlloc
           r = intResult res
           -- Move result to RAX if not already there
           moveToRax = if r == RAX then [] else [IntI (MovI RAX (RegI r))]
       in intCode res ++ moveToRax
     else
       let res = compileFloat expr initAlloc
           r = floatResult res
           -- Move result to XMM0 if not already there
           moveToXmm0 = case arithType expr of
             F32 -> if r == XMM0 then [] else [FloatI (Movss XMM0 (RegF r))]
             F64 -> if r == XMM0 then [] else [FloatI (Movsd XMM0 (RegF r))]
             _   -> []
       in floatCode res ++ moveToXmm0

-- | Compile to assembly text
compileArithToAsm :: ArithIR -> Text
compileArithToAsm = emitProgram . compileArith
