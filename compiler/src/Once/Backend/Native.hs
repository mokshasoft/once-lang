-- | Native code generation
--
-- This module provides native code generators for multiple architectures.
-- The verified MAlonzo code generators are not currently available -
-- run `cd formal && make malonzo` to generate them.
--
-- For now, uses Haskell-based code generation that calls into
-- interpretation functions (once_<primitive>).
--
-- Supported targets:
--   - AArch64 (ARM64)
--   - x86-64
--   - RISC-V 64-bit
module Once.Backend.Native
  ( -- * Compilation functions
    compileToAArch64
  , compileToX86
  , compileToRiscV64
    -- * Full IR compilation (including primitives)
  , compileFullToAArch64
  , compileFullToX86
  , compileFullToRiscV64
    -- * IR analysis
  , containsPrimitives
  , collectPrimitives
    -- * Types
  , Target (..)
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Text.Read (readMaybe)

import qualified Once.IR as H
import qualified Once.Type as H

-- MAlonzo verified code generators
-- NOTE: Backend generators temporarily disabled for QTT integration
import qualified MAlonzo.Code.Once.IR as M
import qualified MAlonzo.Code.Once.Type as M
-- import qualified MAlonzo.Code.Once.Backend.X86.CodeGen as MX86
-- import qualified MAlonzo.Code.Once.Backend.X86.Emit as MX86Emit
-- import qualified MAlonzo.Code.Once.Backend.AArch64.CodeGen as MAArch64
-- import qualified MAlonzo.Code.Once.Backend.AArch64.Emit as MAArch64Emit
-- import qualified MAlonzo.Code.Once.Backend.RiscV64.CodeGen as MRiscV
-- import qualified MAlonzo.Code.Once.Backend.RiscV64.Emit as MRiscVEmit

-- Import MAlonzo bridge functions
import Once.MAlonzo (canConvertIR, toMAlonzoType, toMAlonzoIR)
import qualified Once.MAlonzo as MBridge (getInputType, getOutputType)

------------------------------------------------------------------------
-- Target enumeration
------------------------------------------------------------------------

-- | Supported native targets
data Target
  = TargetAArch64
  | TargetX86_64
  | TargetRiscV64
  deriving (Eq, Show)


------------------------------------------------------------------------
-- Helper functions
------------------------------------------------------------------------

-- | Parse an integer primitive name like "__int_42" and return the value
parseIntPrim :: Text -> Maybe Integer
parseIntPrim name = case T.stripPrefix "__int_" name of
  Just numText -> readMaybe (T.unpack numText)
  Nothing -> Nothing

-- | Get the output type of an IR expression
getOutputType :: H.IR -> Maybe H.Type
getOutputType ir = case ir of
  H.Id t -> Just t
  H.Compose g _ -> getOutputType g
  H.Fst a _ -> Just a
  H.Snd _ b -> Just b
  H.Pair f g -> H.TProduct <$> getOutputType f <*> getOutputType g
  H.Terminal _ -> Just H.TUnit
  H.Inl a b -> Just (H.TSum a b)
  H.Inr a b -> Just (H.TSum a b)
  H.Case f _ -> getOutputType f
  H.Initial t -> Just t
  H.Curry _ f -> do
    fIn <- getInputType f
    fOut <- getOutputType f
    case fIn of
      H.TProduct _ b -> Just (H.TArrow b fOut)
      _ -> Nothing
  H.Apply _ b -> Just b
  H.Fold t -> Just (H.TFix t)
  H.Unfold t -> Just t
  H.Prim _ _ outT -> Just outT
  H.Let _ _ e2 -> getOutputType e2
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Just (H.TString H.Utf8)
  H.Arith _ _ -> Just H.TInt  -- Arithmetic returns Int

-- | Get the input type of an IR expression
getInputType :: H.IR -> Maybe H.Type
getInputType ir = case ir of
  H.Id t -> Just t
  H.Compose _ f -> getInputType f
  H.Fst a b -> Just (H.TProduct a b)
  H.Snd a b -> Just (H.TProduct a b)
  H.Pair f _ -> getInputType f
  H.Terminal t -> Just t
  H.Inl a _ -> Just a
  H.Inr _ b -> Just b
  H.Case _ _ -> Nothing  -- Complex
  H.Initial _ -> Just H.TVoid
  H.Curry _ f -> do
    fIn <- getInputType f
    case fIn of
      H.TProduct a _ -> Just a
      _ -> Nothing
  H.Apply a _ -> Just (H.TProduct (H.TArrow a H.TUnit) a)
  H.Fold t -> Just t
  H.Unfold t -> Just (H.TFix t)
  H.Prim _ inT _ -> Just inT
  H.Let _ _ _ -> Nothing
  H.Var _ -> Nothing
  H.LocalVar _ -> Nothing
  H.FunRef _ -> Nothing
  H.StringLit _ -> Just H.TUnit
  H.Arith _ _ -> Just H.TUnit  -- Arithmetic has trivial input

------------------------------------------------------------------------
-- Compilation functions (verified via MAlonzo extraction)
------------------------------------------------------------------------

-- | Compile Haskell IR to x86-64 assembly text (verified)
--
-- Uses MAlonzo-extracted code from formal Agda proofs.
-- Returns Nothing if IR contains primitives or other non-categorical constructs.
--
-- NOTE: Temporarily disabled for QTT integration
compileToX86 :: H.IR -> Maybe Text
compileToX86 _ir = Nothing  -- Backend generators disabled for QTT integration
  -- TODO: Re-enable after QTT integration complete
  -- | canConvertIR ir =
  --     let mInTy  = MBridge.getInputType ir
  --         mOutTy = MBridge.getOutputType ir
  --         mIR    = toMAlonzoIR ir
  --         instrs = MX86.d_compile'45'x86_32 mInTy mOutTy mIR
  --     in Just $ MX86Emit.d_programToText_76 instrs
  -- | otherwise = Nothing

-- | Compile Haskell IR to AArch64 assembly text (verified)
--
-- Uses MAlonzo-extracted code from formal Agda proofs.
-- Returns Nothing if IR contains primitives or other non-categorical constructs.
--
-- NOTE: Temporarily disabled for QTT integration
compileToAArch64 :: H.IR -> Maybe Text
compileToAArch64 _ir = Nothing  -- Backend generators disabled for QTT integration
  -- TODO: Re-enable after QTT integration complete
  -- | canConvertIR ir =
  --     let mInTy  = MBridge.getInputType ir
  --         mOutTy = MBridge.getOutputType ir
  --         mIR    = toMAlonzoIR ir
  --         instrs = MAArch64.d_compile'45'aarch64_32 mInTy mOutTy mIR
  --     in Just $ MAArch64Emit.d_programToText_104 instrs
  -- | otherwise = Nothing

-- | Compile Haskell IR to RISC-V 64-bit assembly text (verified)
--
-- Uses MAlonzo-extracted code from formal Agda proofs.
-- Returns Nothing if IR contains primitives or other non-categorical constructs.
--
-- NOTE: Temporarily disabled for QTT integration
compileToRiscV64 :: H.IR -> Maybe Text
compileToRiscV64 _ir = Nothing  -- Backend generators disabled for QTT integration
  -- TODO: Re-enable after QTT integration complete
  -- | canConvertIR ir =
  --     let mInTy  = MBridge.getInputType ir
  --         mOutTy = MBridge.getOutputType ir
  --         mIR    = toMAlonzoIR ir
  --         instrs = MRiscV.d_compile'45'riscv_34 mInTy mOutTy mIR
  --     in Just $ MRiscVEmit.d_programToText_278 instrs
  -- | otherwise = Nothing

------------------------------------------------------------------------
-- IR Analysis
------------------------------------------------------------------------

-- | Check if IR contains any primitives (requires linking interpretation code)
containsPrimitives :: H.IR -> Bool
containsPrimitives ir = case ir of
  H.Id _ -> False
  H.Compose g f -> containsPrimitives g || containsPrimitives f
  H.Fst _ _ -> False
  H.Snd _ _ -> False
  H.Pair f g -> containsPrimitives f || containsPrimitives g
  H.Inl _ _ -> False
  H.Inr _ _ -> False
  H.Case f g -> containsPrimitives f || containsPrimitives g
  H.Terminal _ -> False
  H.Initial _ -> False
  H.Curry _ f -> containsPrimitives f
  H.Apply _ _ -> False
  H.Fold _ -> False
  H.Unfold _ -> False
  H.Prim {} -> True
  H.Var _ -> True  -- Function calls also need linking
  H.LocalVar _ -> False
  H.FunRef _ -> True
  H.StringLit _ -> True  -- String literals need special handling
  H.Let _ e1 e2 -> containsPrimitives e1 || containsPrimitives e2
  H.Arith _ _ -> False  -- Arithmetic is self-contained

-- | Collect all primitive names used in IR
collectPrimitives :: H.IR -> Set Text
collectPrimitives ir = case ir of
  H.Id _ -> Set.empty
  H.Compose g f -> collectPrimitives g `Set.union` collectPrimitives f
  H.Fst _ _ -> Set.empty
  H.Snd _ _ -> Set.empty
  H.Pair f g -> collectPrimitives f `Set.union` collectPrimitives g
  H.Inl _ _ -> Set.empty
  H.Inr _ _ -> Set.empty
  H.Case f g -> collectPrimitives f `Set.union` collectPrimitives g
  H.Terminal _ -> Set.empty
  H.Initial _ -> Set.empty
  H.Curry _ f -> collectPrimitives f
  H.Apply _ _ -> Set.empty
  H.Fold _ -> Set.empty
  H.Unfold _ -> Set.empty
  H.Prim name _ _ -> Set.singleton name
  H.Var name -> Set.singleton name
  H.LocalVar _ -> Set.empty
  H.FunRef name -> Set.singleton name
  H.StringLit _ -> Set.empty
  H.Let _ e1 e2 -> collectPrimitives e1 `Set.union` collectPrimitives e2
  H.Arith _ _ -> Set.empty  -- Arithmetic has no primitives

------------------------------------------------------------------------
-- Full IR Compilation (Haskell-based, supports primitives)
------------------------------------------------------------------------

-- | Compile any IR to x86-64 assembly (Haskell-based, not verified)
-- This handles primitives by generating call instructions.
-- ABI: input in %rdi, output in %rax
-- Variables are stored on the stack, tracked by environment.
compileFullToX86 :: H.IR -> Text
compileFullToX86 ir = genX86WithEnv Map.empty 0 ir
  where
    -- Environment maps variable names to stack offsets (relative to rbp)
    -- Offset is negative: [rbp-8] is first variable, [rbp-16] is second, etc.

    -- Generate x86-64 assembly with variable environment
    -- Input is in %rdi, output goes to %rax
    -- stackDepth tracks current stack usage for new variables
    genX86WithEnv :: Map.Map Text Int -> Int -> H.IR -> Text
    genX86WithEnv env depth expr = case expr of
      -- Identity: just move input to output
      H.Id _ -> "    movq %rdi, %rax"

      -- Composition: f then g
      H.Compose g f ->
        genX86WithEnv env depth f <> "\n" <>
        "    movq %rax, %rdi\n" <>
        genX86WithEnv env depth g

      -- Projections: input is pair pointer, load from memory
      H.Fst _ _ -> "    movq (%rdi), %rax"
      H.Snd _ _ -> "    movq 8(%rdi), %rax"

      -- Pair construction: allocate on stack, compute both
      -- Uses callee-saved registers (r14, r15, rbp) to survive nested pairs
      -- This matches the verified Agda code in Once.Backend.X86.CodeGen
      H.Pair f g ->
        -- Stack grows by: push r14 (8) + push r15 (8) + push rbp (8) + sub 16 = 40
        let pairDepth = depth + 40
        in
        -- Save callee-saved registers
        "    pushq %r14\n" <>
        "    pushq %r15\n" <>
        "    pushq %rbp\n" <>
        -- Set frame pointer
        "    movq %rsp, %rbp\n" <>
        -- Allocate 16 bytes for pair
        "    subq $16, %rsp\n" <>
        -- r15 = stable pair address (survives nested calls)
        "    movq %rsp, %r15\n" <>
        -- r14 = saved input (survives nested calls)
        "    movq %rdi, %r14\n" <>
        -- Compute f (may allocate more stack, may nest pairs)
        genX86WithEnv env pairDepth f <> "\n" <>
        -- Store f result at [r15] (stable address)
        "    movq %rax, (%r15)\n" <>
        -- Restore input for g
        "    movq %r14, %rdi\n" <>
        -- Compute g (uses same depth - stack restored by f's cleanup)
        genX86WithEnv env pairDepth g <> "\n" <>
        -- Store g result at [r15 + 8]
        "    movq %rax, 8(%r15)\n" <>
        -- Return pair pointer
        "    movq %r15, %rax\n" <>
        -- Restore stack to frame base
        "    movq %rbp, %rsp\n" <>
        -- Restore callee-saved registers
        "    popq %rbp\n" <>
        "    popq %r15\n" <>
        "    popq %r14"

      -- Terminal: return NULL (Unit)
      H.Terminal _ -> "    xorq %rax, %rax"

      -- Initial: absurd (from Void) - should never be called
      H.Initial _ -> "    ud2"

      -- Sum injection: allocate tagged value on stack
      H.Inl _ _ ->
        "    subq $16, %rsp\n" <>
        "    movq $0, (%rsp)\n" <>      -- tag = 0
        "    movq %rdi, 8(%rsp)\n" <>   -- value
        "    movq %rsp, %rax"           -- return pointer

      H.Inr _ _ ->
        "    subq $16, %rsp\n" <>
        "    movq $1, (%rsp)\n" <>      -- tag = 1
        "    movq %rdi, 8(%rsp)\n" <>   -- value
        "    movq %rsp, %rax"           -- return pointer

      -- Case analysis: check tag, branch
      H.Case l r ->
        let labelSuffix = T.pack $ show (hash expr)
        in "    movq (%rdi), %r11\n" <>       -- load tag
           "    movq 8(%rdi), %rdi\n" <>       -- load value for branch
           "    testq %r11, %r11\n" <>
           "    jnz .Lcase_right_" <> labelSuffix <> "\n" <>
           genX86WithEnv env depth l <> "\n" <>
           "    jmp .Lcase_done_" <> labelSuffix <> "\n" <>
           ".Lcase_right_" <> labelSuffix <> ":\n" <>
           genX86WithEnv env depth r <> "\n" <>
           ".Lcase_done_" <> labelSuffix <> ":"

      -- Curry/Apply - simplified (closures need more work)
      H.Curry _ body ->
        -- For now, just evaluate the body with input as pair
        genX86WithEnv env depth body
      H.Apply _ _ ->
        -- Apply closure: load code ptr and call
        "    movq 8(%rdi), %r11\n" <>  -- code ptr
        "    movq (%rdi), %rdi\n" <>   -- env/arg
        "    call *%r11"

      -- Fold/Unfold - identity at runtime
      H.Fold _ -> "    movq %rdi, %rax"
      H.Unfold _ -> "    movq %rdi, %rax"

      -- Primitive: inline integer constants, call others
      H.Prim name _ _ -> case parseIntPrim name of
        Just n -> "    movq $" <> T.pack (show n) <> ", %rax"
        Nothing -> "    call once_" <> name

      -- Function reference: call it with current input
      H.Var name ->
        "    call once_" <> name

      -- Local variable: load from stack using environment
      -- Variables are stored at positive offsets from current %rsp
      -- since we push them as we go. We track the depth and variable offset.
      H.LocalVar name ->
        case Map.lookup name env of
          -- Variable is at (depth - offset) from current %rsp
          -- offset is the depth when variable was stored
          Just varDepth ->
            let rspOffset = depth - varDepth
            in "    movq " <> T.pack (show rspOffset) <> "(%rsp), %rax"
          Nothing -> "    # ERROR: undefined variable " <> name <> "\n    xorq %rax, %rax"

      -- Function pointer
      H.FunRef name ->
        "    leaq once_" <> name <> "(%rip), %rax"

      -- String literal - not supported in pure native yet
      H.StringLit _ ->
        "    xorq %rax, %rax"  -- return NULL

      -- Let binding: compute value, store on stack, evaluate body
      -- Store current depth+8 as the variable's "address" - after push, it's at 0(%rsp)
      -- but as we push more, it moves to higher offsets
      H.Let varName e1 e2 ->
        let newDepth = depth + 8
            newEnv = Map.insert varName newDepth env  -- store depth AFTER push
        in genX86WithEnv env depth e1 <> "\n" <>
           "    pushq %rax\n" <>  -- store value on stack (now at depth+8)
           genX86WithEnv newEnv newDepth e2 <> "\n" <>
           "    addq $8, %rsp"    -- pop the variable

      -- Arithmetic expression: handled separately via C backend
      H.Arith _ _ -> "    # arith: handled via C backend"

    -- Simple hash for unique labels (no Show needed)
    hash :: H.IR -> Int
    hash = irHash
      where
        irHash ir = case ir of
          H.Id _ -> 1
          H.Compose g f -> irHash g * 31 + irHash f
          H.Fst _ _ -> 2
          H.Snd _ _ -> 3
          H.Pair a b -> irHash a * 17 + irHash b + 4
          H.Terminal _ -> 5
          H.Inl _ _ -> 6
          H.Inr _ _ -> 7
          H.Case a b -> irHash a * 23 + irHash b + 8
          H.Initial _ -> 9
          H.Curry _ f -> irHash f + 10
          H.Apply _ _ -> 11
          H.Var _ -> 12
          H.LocalVar _ -> 13
          H.FunRef _ -> 14
          H.Prim _ _ _ -> 15
          H.StringLit _ -> 16
          H.Fold _ -> 17
          H.Unfold _ -> 18
          H.Let _ e b -> irHash e * 29 + irHash b + 19
          H.Arith _ _ -> 20  -- MAlonzo types, use constant

-- | Compile any IR to AArch64 assembly (Haskell-based, not verified)
-- ABI: input in x0, output in x0
compileFullToAArch64 :: H.IR -> Text
compileFullToAArch64 ir = genAArch64 ir
  where
    genAArch64 :: H.IR -> Text
    genAArch64 expr = case expr of
      H.Id _ -> "    // id: x0 unchanged"

      H.Compose g f ->
        genAArch64 f <> "\n" <>
        genAArch64 g

      H.Fst _ _ -> "    // fst: x0 already has first element"
      H.Snd _ _ -> "    mov x0, x1"

      H.Pair f g ->
        "    stp x0, x1, [sp, #-16]!\n" <>  -- save input
        genAArch64 f <> "\n" <>
        "    str x0, [sp, #-8]!\n" <>       -- save f result
        "    ldp x0, x1, [sp, #8]\n" <>     -- restore input
        genAArch64 g <> "\n" <>
        "    mov x1, x0\n" <>               -- g result to x1
        "    ldr x0, [sp], #8\n" <>         -- f result to x0
        "    add sp, sp, #16"               -- clean up

      H.Terminal _ -> "    mov x0, #0"

      H.Initial _ -> "    mov x0, #0"

      H.Inl _ _ -> "    // inl: x0 unchanged"
      H.Inr _ _ -> "    // inr: x0 unchanged"

      H.Case l r ->
        "    cbz x0, .Lcase_left_" <> labelSuffix <> "\n" <>
        "    mov x0, x1\n" <>
        genAArch64 r <> "\n" <>
        "    b .Lcase_done_" <> labelSuffix <> "\n" <>
        ".Lcase_left_" <> labelSuffix <> ":\n" <>
        "    mov x0, x1\n" <>
        genAArch64 l <> "\n" <>
        ".Lcase_done_" <> labelSuffix <> ":"
        where labelSuffix = T.pack $ show (hash expr)

      H.Curry _ _ -> "    // curry: x0 unchanged"
      H.Apply _ _ -> "    // apply: x0 unchanged"

      H.Fold _ -> "    // fold: x0 unchanged"
      H.Unfold _ -> "    // unfold: x0 unchanged"

      H.Prim name _ _ -> case parseIntPrim name of
        Just n -> "    mov x0, #" <> T.pack (show n)
        Nothing -> "    bl once_" <> name

      H.Var name ->
        "    bl once_" <> name

      H.LocalVar _ -> "    // localvar: x0 unchanged"

      H.FunRef name ->
        "    adrp x0, once_" <> name <> "\n" <>
        "    add x0, x0, :lo12:once_" <> name

      H.StringLit _ -> "    mov x0, #0"

      H.Let _ e1 e2 ->
        genAArch64 e1 <> "\n" <>
        genAArch64 e2

      H.Arith _ _ -> "    // arith: handled separately"

    -- Simple hash for unique labels (no Show needed)
    hash :: H.IR -> Int
    hash = irHash
      where
        irHash i = case i of
          H.Id _ -> 1
          H.Compose g f -> irHash g * 31 + irHash f
          H.Fst _ _ -> 2
          H.Snd _ _ -> 3
          H.Pair a b -> irHash a * 17 + irHash b + 4
          H.Terminal _ -> 5
          H.Inl _ _ -> 6
          H.Inr _ _ -> 7
          H.Case a b -> irHash a * 23 + irHash b + 8
          H.Initial _ -> 9
          H.Curry _ f -> irHash f + 10
          H.Apply _ _ -> 11
          H.Var _ -> 12
          H.LocalVar _ -> 13
          H.FunRef _ -> 14
          H.Prim _ _ _ -> 15
          H.StringLit _ -> 16
          H.Fold _ -> 17
          H.Unfold _ -> 18
          H.Let _ e b -> irHash e * 29 + irHash b + 19
          H.Arith _ _ -> 20

-- | Compile any IR to RISC-V 64 assembly (Haskell-based, not verified)
-- ABI: input in a0, output in a0
compileFullToRiscV64 :: H.IR -> Text
compileFullToRiscV64 ir = genRiscV ir
  where
    genRiscV :: H.IR -> Text
    genRiscV expr = case expr of
      H.Id _ -> "    # id: a0 unchanged"

      H.Compose g f ->
        genRiscV f <> "\n" <>
        genRiscV g

      H.Fst _ _ -> "    # fst: a0 already has first element"
      H.Snd _ _ -> "    mv a0, a1"

      H.Pair f g ->
        "    addi sp, sp, -24\n" <>
        "    sd a0, 0(sp)\n" <>
        "    sd a1, 8(sp)\n" <>
        genRiscV f <> "\n" <>
        "    sd a0, 16(sp)\n" <>
        "    ld a0, 0(sp)\n" <>
        "    ld a1, 8(sp)\n" <>
        genRiscV g <> "\n" <>
        "    mv a1, a0\n" <>
        "    ld a0, 16(sp)\n" <>
        "    addi sp, sp, 24"

      H.Terminal _ -> "    li a0, 0"

      H.Initial _ -> "    li a0, 0"

      H.Inl _ _ -> "    # inl: a0 unchanged"
      H.Inr _ _ -> "    # inr: a0 unchanged"

      H.Case l r ->
        "    bnez a0, .Lcase_right_" <> labelSuffix <> "\n" <>
        "    mv a0, a1\n" <>
        genRiscV l <> "\n" <>
        "    j .Lcase_done_" <> labelSuffix <> "\n" <>
        ".Lcase_right_" <> labelSuffix <> ":\n" <>
        "    mv a0, a1\n" <>
        genRiscV r <> "\n" <>
        ".Lcase_done_" <> labelSuffix <> ":"
        where labelSuffix = T.pack $ show (hash expr)

      H.Curry _ _ -> "    # curry: a0 unchanged"
      H.Apply _ _ -> "    # apply: a0 unchanged"

      H.Fold _ -> "    # fold: a0 unchanged"
      H.Unfold _ -> "    # unfold: a0 unchanged"

      H.Prim name _ _ -> case parseIntPrim name of
        Just n -> "    li a0, " <> T.pack (show n)
        Nothing -> "    call once_" <> name

      H.Var name ->
        "    call once_" <> name

      H.LocalVar _ -> "    # localvar: a0 unchanged"

      H.FunRef name ->
        "    la a0, once_" <> name

      H.StringLit _ -> "    li a0, 0"

      H.Let _ e1 e2 ->
        genRiscV e1 <> "\n" <>
        genRiscV e2

      H.Arith _ _ -> "    # arith: handled separately"

    -- Simple hash for unique labels (no Show needed)
    hash :: H.IR -> Int
    hash = irHash
      where
        irHash i = case i of
          H.Id _ -> 1
          H.Compose g f -> irHash g * 31 + irHash f
          H.Fst _ _ -> 2
          H.Snd _ _ -> 3
          H.Pair a b -> irHash a * 17 + irHash b + 4
          H.Terminal _ -> 5
          H.Inl _ _ -> 6
          H.Inr _ _ -> 7
          H.Case a b -> irHash a * 23 + irHash b + 8
          H.Initial _ -> 9
          H.Curry _ f -> irHash f + 10
          H.Apply _ _ -> 11
          H.Var _ -> 12
          H.LocalVar _ -> 13
          H.FunRef _ -> 14
          H.Prim _ _ _ -> 15
          H.StringLit _ -> 16
          H.Fold _ -> 17
          H.Unfold _ -> 18
          H.Let _ e b -> irHash e * 29 + irHash b + 19
          H.Arith _ _ -> 20
