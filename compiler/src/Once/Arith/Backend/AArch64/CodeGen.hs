{-# LANGUAGE RecordWildCards #-}
-- | AArch64 code generation for arithmetic expressions
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
--
-- This module generates AArch64 instructions from ArithIR,
-- mirroring the verified Agda implementation.
module Once.Arith.Backend.AArch64.CodeGen
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
import Data.Int (Int64)
import Data.Bits ((.&.), shiftR)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Once.Arith.IR
import Once.Arith.Backend.AArch64.Syntax
import Once.Arith.Backend.AArch64.Emit (emitProgram)

------------------------------------------------------------------------
-- Register allocation state
------------------------------------------------------------------------

-- | Available GPR registers for allocation (caller-saved temporaries)
-- We use X9-X15 as temporaries, avoiding X0-X7 (arguments/return)
availableGPRs :: [GPReg]
availableGPRs = [X9, X10, X11, X12, X13, X14, X15]

-- | Available FP registers for allocation
-- D16-D23 are caller-saved and safe to use
availableFPs :: [FPReg]
availableFPs = [D16, D17, D18, D19, D20, D21, D22, D23]

-- | Register allocation state
data AllocState = AllocState
  { nextGPR :: !Int           -- ^ Index into availableGPRs
  , nextFP  :: !Int           -- ^ Index into availableFPs
  , varMap  :: Map Text GPReg -- ^ Variable to register mapping
  } deriving (Eq, Show)

-- | Initial allocation state
initAlloc :: AllocState
initAlloc = AllocState 0 0 Map.empty

-- | Get the nth GPR (wrapping if needed)
getGPR :: Int -> GPReg
getGPR n = availableGPRs !! (n `mod` length availableGPRs)

-- | Get the nth FP register
getFP :: Int -> FPReg
getFP n = availableFPs !! (n `mod` length availableFPs)

-- | Allocate a GPR
allocGPR :: AllocState -> (GPReg, AllocState)
allocGPR st@AllocState{..} = (getGPR nextGPR, st { nextGPR = nextGPR + 1 })

-- | Allocate an FP register
allocFP :: AllocState -> (FPReg, AllocState)
allocFP st@AllocState{..} = (getFP nextFP, st { nextFP = nextFP + 1 })

-- | Free a GPR (decrement counter)
freeGPR :: AllocState -> AllocState
freeGPR st@AllocState{..} = st { nextGPR = max 0 (nextGPR - 1) }

-- | Free an FP register
freeFP :: AllocState -> AllocState
freeFP st@AllocState{..} = st { nextFP = max 0 (nextFP - 1) }

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
  , floatResult :: FPReg         -- ^ Register holding result
  , floatState  :: AllocState    -- ^ Updated allocation state
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- 64-bit immediate loading
------------------------------------------------------------------------

-- | Load a 64-bit immediate into a register
-- AArch64 can only load 16 bits at a time with movz/movk
loadImm64 :: GPReg -> Int64 -> [ArithInstr]
loadImm64 reg n
  | n >= 0 && n < 65536 =
      -- Small positive: single movz
      [IntI (Movz reg n 0)]
  | otherwise =
      -- General case: up to 4 movz/movk instructions
      let chunk0 = n .&. 0xFFFF
          chunk1 = (n `shiftR` 16) .&. 0xFFFF
          chunk2 = (n `shiftR` 32) .&. 0xFFFF
          chunk3 = (n `shiftR` 48) .&. 0xFFFF
          -- Start with movz for first non-zero chunk, then movk
          instrs = [IntI (Movz reg chunk0 0)]
                ++ (if chunk1 /= 0 then [IntI (Movk reg chunk1 16)] else [])
                ++ (if chunk2 /= 0 then [IntI (Movk reg chunk2 32)] else [])
                ++ (if chunk3 /= 0 then [IntI (Movk reg chunk3 48)] else [])
      in instrs

------------------------------------------------------------------------
-- Integer code generation
------------------------------------------------------------------------

-- | Compile an integer arithmetic expression
compileInt :: ArithIR -> AllocState -> IntResult

-- Literal: load immediate into fresh register
compileInt (ALitInt _ n) st =
  let (r, st') = allocGPR st
  in IntResult
       { intCode   = loadImm64 r (fromInteger n)
       , intResult = r
       , intState  = st'
       }

-- Variable: look up or load from memory
compileInt (AVar name _) st =
  case Map.lookup name (varMap st) of
    Just r  -> IntResult [] r st
    Nothing ->
      let (r, st') = allocGPR st
      in IntResult
           { intCode   = [IntI (Mov r (RegOp X0))]  -- Placeholder
           , intResult = r
           , intState  = st' { varMap = Map.insert name r (varMap st') }
           }

-- Addition
compileInt (AAdd e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2
                  ++ [IntI (Add r1 r1 (RegOp r2))]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Subtraction
compileInt (ASub e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2
                  ++ [IntI (Sub r1 r1 (RegOp r2))]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Multiplication
compileInt (AMul e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2
                  ++ [IntI (Mul r1 r1 r2)]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Division (AArch64 has hardware sdiv)
compileInt (ADiv e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
  in IntResult
       { intCode   = intCode res1 ++ intCode res2
                  ++ [IntI (Sdiv r1 r1 r2)]
       , intResult = r1
       , intState  = freeGPR (intState res2)
       }

-- Modulo: a % b = a - (a / b) * b
-- Using msub: dst = acc - mul1 * mul2
compileInt (AMod e1 e2) st =
  let res1 = compileInt e1 st
      res2 = compileInt e2 (intState res1)
      r1 = intResult res1
      r2 = intResult res2
      (rTmp, st') = allocGPR (intState res2)
      modCode =
        [ IntI (Sdiv rTmp r1 r2)      -- tmp = a / b
        , IntI (Msub r1 rTmp r2 r1)   -- r1 = r1 - tmp * r2 = a - (a/b)*b
        ]
  in IntResult
       { intCode   = intCode res1 ++ intCode res2 ++ modCode
       , intResult = r1
       , intState  = freeGPR (freeGPR st')
       }

-- Negation
compileInt (ANeg e) st =
  let res = compileInt e st
      r = intResult res
  in IntResult
       { intCode   = intCode res ++ [IntI (Neg r r)]
       , intResult = r
       , intState  = intState res
       }

-- Comparison (simplified: compute difference)
compileInt (ACmp _ e1 e2) st = compileInt (ASub e1 e2) st

-- Float not handled here
compileInt (ALitFloat _ _) _ = error "compileInt: got float literal"

------------------------------------------------------------------------
-- Float code generation
------------------------------------------------------------------------

-- | Compile a floating-point arithmetic expression
compileFloat :: ArithIR -> AllocState -> FloatResult

-- Float literal (would need memory load in practice)
compileFloat (ALitFloat _ _) st =
  let (r, st') = allocFP st
  in FloatResult
       { floatCode   = [FPI (Fmov r (FPRegOp D0))]  -- Placeholder
       , floatResult = r
       , floatState  = st'
       }

-- Variable
compileFloat (AVar _ _) st =
  let (r, st') = allocFP st
  in FloatResult
       { floatCode   = [FPI (Fmov r (FPRegOp D0))]  -- Placeholder
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
        F32 -> FPI (FaddS r1 r1 r2)
        F64 -> FPI (Fadd r1 r1 r2)
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [addInstr]
       , floatResult = r1
       , floatState  = freeFP (floatState res2)
       }

-- Subtraction
compileFloat (ASub e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      subInstr = case ty of
        F32 -> FPI (FsubS r1 r1 r2)
        F64 -> FPI (Fsub r1 r1 r2)
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [subInstr]
       , floatResult = r1
       , floatState  = freeFP (floatState res2)
       }

-- Multiplication
compileFloat (AMul e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      mulInstr = case ty of
        F32 -> FPI (FmulS r1 r1 r2)
        F64 -> FPI (Fmul r1 r1 r2)
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [mulInstr]
       , floatResult = r1
       , floatState  = freeFP (floatState res2)
       }

-- Division
compileFloat (ADiv e1 e2) st =
  let ty = arithType e1
      res1 = compileFloat e1 st
      res2 = compileFloat e2 (floatState res1)
      r1 = floatResult res1
      r2 = floatResult res2
      divInstr = case ty of
        F32 -> FPI (FdivS r1 r1 r2)
        F64 -> FPI (Fdiv r1 r1 r2)
        _   -> error "compileFloat: not a float type"
  in FloatResult
       { floatCode   = floatCode res1 ++ floatCode res2 ++ [divInstr]
       , floatResult = r1
       , floatState  = freeFP (floatState res2)
       }

-- Negation
compileFloat (ANeg e) st =
  let ty = arithType e
      res = compileFloat e st
      r = floatResult res
      negInstr = case ty of
        F32 -> FPI (FnegS r r)
        F64 -> FPI (Fneg r r)
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

-- Integer not handled here
compileFloat (ALitInt _ _) _ = error "compileFloat: got int literal"

------------------------------------------------------------------------
-- Main compilation entry point
------------------------------------------------------------------------

-- | Compile an arithmetic expression to AArch64 instructions
--
-- Result is left in X0 (integers) or D0 (floats)
compileArith :: ArithIR -> ArithProgram
compileArith expr =
  let ty = arithType expr
  in if isInteger ty
     then
       let res = compileInt expr initAlloc
           r = intResult res
           -- Move result to X0 if not already there
           moveToX0 = if r == X0 then [] else [IntI (Mov X0 (RegOp r))]
       in intCode res ++ moveToX0
     else
       let res = compileFloat expr initAlloc
           r = floatResult res
           -- Move result to D0 if not already there
           moveToD0 = if r == D0 then [] else [FPI (Fmov D0 (FPRegOp r))]
       in floatCode res ++ moveToD0

-- | Compile to assembly text
compileArithToAsm :: ArithIR -> Text
compileArithToAsm = emitProgram . compileArith
