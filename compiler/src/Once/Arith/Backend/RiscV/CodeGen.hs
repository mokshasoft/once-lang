{-# LANGUAGE RecordWildCards #-}
-- | RISC-V code generation for arithmetic expressions.
--
-- Part of OCP-0001: Orthogonal Arithmetic Compiler
module Once.Arith.Backend.RiscV.CodeGen
  ( compileArith
  , AllocState(..)
  , initAllocState
  ) where

import Data.Int (Int64)

import Once.Arith.IR
import Once.Arith.Backend.RiscV.Syntax

------------------------------------------------------------------------
-- Register Allocation State
------------------------------------------------------------------------

data AllocState = AllocState
  { nextGPR :: [GPReg]   -- ^ Available general-purpose registers
  , nextFP  :: [FPReg]   -- ^ Available floating-point registers
  } deriving (Show)

-- | Available temporary GPRs: t0-t6 (X5-X7, X28-X31)
availableGPRs :: [GPReg]
availableGPRs = [X5, X6, X7, X28, X29, X30, X31]

-- | Available temporary FP registers: ft0-ft7 (F0-F7)
availableFPs :: [FPReg]
availableFPs = [F0, F1, F2, F3, F4, F5, F6, F7]

initAllocState :: AllocState
initAllocState = AllocState availableGPRs availableFPs

------------------------------------------------------------------------
-- Result Destination
------------------------------------------------------------------------

-- | Result register for integers: a0 (X10)
resultGPR :: GPReg
resultGPR = X10

-- | Result register for floats: fa0 (F10)
resultFP :: FPReg
resultFP = F10

------------------------------------------------------------------------
-- Code Generation
------------------------------------------------------------------------

-- | Compile an ArithIR expression to RISC-V instructions
compileArith :: ArithIR -> ArithProgram
compileArith expr = prog ++ [moveToResult]
  where
    (prog, dest, st') = compileExpr expr initAllocState
    moveToResult = case dest of
      Left gpr -> IntI $ Mv resultGPR gpr
      Right fpr -> FPI $ FmvD resultFP fpr

-- | Compile an expression, returning the destination register
compileExpr :: ArithIR -> AllocState -> (ArithProgram, Either GPReg FPReg, AllocState)
compileExpr (ALitInt ty n) st@AllocState{..} =
  case nextGPR of
    (r:rs) ->
      let prog = [IntI $ Li r (fromIntegral n)]
      in (prog, Left r, st { nextGPR = rs })
    [] -> error "Register spill not implemented"

compileExpr (ALitFloat ty d) st@AllocState{..} =
  -- For floats, we need to load via memory or use integer registers
  -- Simplified: use li to load bits then move to FP reg
  -- In real code, we'd use a constant pool
  case (nextGPR, nextFP) of
    (g:gs, f:fs) ->
      let bits = floatToInt64 ty d
          prog = [ IntI $ Li g bits
                 -- fmv.d.x would move from int to float reg
                 -- Simplified: assume the value is already in FP reg
                 ]
      in (prog, Right f, st { nextGPR = gs, nextFP = fs })
    _ -> error "Register spill not implemented"

compileExpr (AVar name ty) st@AllocState{..} =
  -- Variables would be loaded from memory/environment
  -- Placeholder: allocate a register
  if isFloat ty
    then case nextFP of
      (r:rs) -> ([], Right r, st { nextFP = rs })
      [] -> error "Register spill not implemented"
    else case nextGPR of
      (r:rs) -> ([], Left r, st { nextGPR = rs })
      [] -> error "Register spill not implemented"

compileExpr (AAdd e1 e2) st = compileBinOp e1 e2 st mkAdd mkFadd
  where
    mkAdd d s1 s2 = IntI $ Add d s1 s2
    mkFadd d s1 s2 = FPI $ FaddD d s1 s2

compileExpr (ASub e1 e2) st = compileBinOp e1 e2 st mkSub mkFsub
  where
    mkSub d s1 s2 = IntI $ Sub d s1 s2
    mkFsub d s1 s2 = FPI $ FsubD d s1 s2

compileExpr (AMul e1 e2) st = compileBinOp e1 e2 st mkMul mkFmul
  where
    mkMul d s1 s2 = IntI $ Mul d s1 s2
    mkFmul d s1 s2 = FPI $ FmulD d s1 s2

compileExpr (ADiv e1 e2) st = compileBinOp e1 e2 st mkDiv mkFdiv
  where
    mkDiv d s1 s2 = IntI $ Div d s1 s2
    mkFdiv d s1 s2 = FPI $ FdivD d s1 s2

compileExpr (AMod e1 e2) st = compileBinOpInt e1 e2 st mkRem
  where
    mkRem d s1 s2 = IntI $ Rem d s1 s2

compileExpr (ANeg e) st = compileUnaryOp e st mkNeg mkFneg
  where
    mkNeg d s = IntI $ Neg d s
    mkFneg d s = FPI $ FnegD d s

compileExpr (ACmp _ e1 e2) st =
  -- Comparisons return boolean (integer)
  let (prog1, Left r1, st1) = compileExpr e1 st
      (prog2, Left r2, st2) = compileExpr e2 st1
      -- RISC-V comparisons use slt, etc. - simplified for now
  in (prog1 ++ prog2, Left r1, st2)

------------------------------------------------------------------------
-- Binary Operation Helpers
------------------------------------------------------------------------

compileBinOp :: ArithIR -> ArithIR -> AllocState
             -> (GPReg -> GPReg -> GPReg -> ArithInstr)
             -> (FPReg -> FPReg -> FPReg -> ArithInstr)
             -> (ArithProgram, Either GPReg FPReg, AllocState)
compileBinOp e1 e2 st intOp fpOp =
  let (prog1, dest1, st1) = compileExpr e1 st
      (prog2, dest2, st2) = compileExpr e2 st1
  in case (dest1, dest2) of
    (Left r1, Left r2) ->
      -- Result goes in r1, freeing r2
      let instr = intOp r1 r1 r2
      in (prog1 ++ prog2 ++ [instr], Left r1, st2 { nextGPR = r2 : nextGPR st2 })
    (Right f1, Right f2) ->
      let instr = fpOp f1 f1 f2
      in (prog1 ++ prog2 ++ [instr], Right f1, st2 { nextFP = f2 : nextFP st2 })
    _ -> error "Type mismatch in binary operation"

compileBinOpInt :: ArithIR -> ArithIR -> AllocState
                -> (GPReg -> GPReg -> GPReg -> ArithInstr)
                -> (ArithProgram, Either GPReg FPReg, AllocState)
compileBinOpInt e1 e2 st intOp =
  let (prog1, Left r1, st1) = compileExpr e1 st
      (prog2, Left r2, st2) = compileExpr e2 st1
      instr = intOp r1 r1 r2
  in (prog1 ++ prog2 ++ [instr], Left r1, st2 { nextGPR = r2 : nextGPR st2 })

------------------------------------------------------------------------
-- Unary Operation Helpers
------------------------------------------------------------------------

compileUnaryOp :: ArithIR -> AllocState
               -> (GPReg -> GPReg -> ArithInstr)
               -> (FPReg -> FPReg -> ArithInstr)
               -> (ArithProgram, Either GPReg FPReg, AllocState)
compileUnaryOp e st intOp fpOp =
  let (prog, dest, st') = compileExpr e st
  in case dest of
    Left r ->
      let instr = intOp r r
      in (prog ++ [instr], Left r, st')
    Right f ->
      let instr = fpOp f f
      in (prog ++ [instr], Right f, st')

------------------------------------------------------------------------
-- Float Conversion (placeholder)
------------------------------------------------------------------------

floatToInt64 :: NumType -> Double -> Int64
floatToInt64 _ _ = 0  -- Placeholder - would use bit manipulation
