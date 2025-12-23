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

import qualified Once.IR as H
import qualified Once.Type as H

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

------------------------------------------------------------------------
-- Compilation functions (verified - currently stubbed)
------------------------------------------------------------------------

-- | Compile Haskell IR to AArch64 assembly text (verified)
-- Returns Nothing - MAlonzo modules need to be generated
compileToAArch64 :: H.IR -> Maybe Text
compileToAArch64 _ = Nothing  -- TODO: run `cd formal && make malonzo`

-- | Compile Haskell IR to x86-64 assembly text (verified)
-- Returns Nothing - MAlonzo modules need to be generated
compileToX86 :: H.IR -> Maybe Text
compileToX86 _ = Nothing  -- TODO: run `cd formal && make malonzo`

-- | Compile Haskell IR to RISC-V 64-bit assembly text (verified)
-- Returns Nothing - MAlonzo modules need to be generated
compileToRiscV64 :: H.IR -> Maybe Text
compileToRiscV64 _ = Nothing  -- TODO: run `cd formal && make malonzo`

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

------------------------------------------------------------------------
-- Full IR Compilation (Haskell-based, supports primitives)
------------------------------------------------------------------------

-- | Compile any IR to x86-64 assembly (Haskell-based, not verified)
-- This handles primitives by generating call instructions.
-- ABI: input in %rdi, output in %rax
compileFullToX86 :: H.IR -> Text
compileFullToX86 ir = genX86 ir
  where
    -- Generate x86-64 assembly for IR
    -- Input is in %rdi, output goes to %rax
    genX86 :: H.IR -> Text
    genX86 expr = case expr of
      -- Identity: just move input to output
      H.Id _ -> "    movq %rdi, %rax"

      -- Composition: f then g
      H.Compose g f ->
        genX86 f <> "\n" <>
        "    movq %rax, %rdi\n" <>
        genX86 g

      -- Projections: input is pair (fst in %rdi, snd in %rsi)
      H.Fst _ _ -> "    movq %rdi, %rax"
      H.Snd _ _ -> "    movq %rsi, %rax"

      -- Pair construction: run both branches, combine results
      H.Pair f g ->
        -- Save input
        "    pushq %rdi\n" <>
        "    pushq %rsi\n" <>
        -- Compute f
        genX86 f <> "\n" <>
        "    pushq %rax\n" <>  -- save f result
        -- Restore input, compute g
        "    movq 16(%rsp), %rdi\n" <>
        "    movq 8(%rsp), %rsi\n" <>
        genX86 g <> "\n" <>
        -- Result: (f result, g result) in (%rdi, %rsi) for pair
        -- But we return in %rax, so we need to pack it
        -- For simplicity, return f result in %rdi, g result in %rsi
        "    movq %rax, %rsi\n" <>  -- g result to %rsi
        "    popq %rdi\n" <>        -- f result to %rdi
        "    addq $16, %rsp\n" <>   -- clean up saved input
        "    movq %rdi, %rax"       -- return fst as %rax (caller handles pair)

      -- Terminal: return NULL (Unit)
      H.Terminal _ -> "    xorq %rax, %rax"

      -- Initial: absurd (from Void) - should never be called
      H.Initial _ -> "    xorq %rax, %rax"

      -- Sum injection
      H.Inl _ _ ->
        -- tag=0, value=input
        "    movq %rdi, %rax"  -- value in rax, tag would be 0

      H.Inr _ _ ->
        -- tag=1, value=input
        "    movq %rdi, %rax"  -- value in rax

      -- Case analysis: check tag, branch
      H.Case l r ->
        -- Input is sum: tag in %rdi, value in %rsi (or similar encoding)
        -- Simplified: assume tag==0 means left
        "    testq %rdi, %rdi\n" <>
        "    jnz .Lcase_right_" <> labelSuffix <> "\n" <>
        "    movq %rsi, %rdi\n" <>
        genX86 l <> "\n" <>
        "    jmp .Lcase_done_" <> labelSuffix <> "\n" <>
        ".Lcase_right_" <> labelSuffix <> ":\n" <>
        "    movq %rsi, %rdi\n" <>
        genX86 r <> "\n" <>
        ".Lcase_done_" <> labelSuffix <> ":"
        where labelSuffix = T.pack $ show (hash expr)

      -- Curry/Apply - simplified
      H.Curry _ _ -> "    movq %rdi, %rax"
      H.Apply _ _ -> "    movq %rdi, %rax"

      -- Fold/Unfold - identity at runtime
      H.Fold _ -> "    movq %rdi, %rax"
      H.Unfold _ -> "    movq %rdi, %rax"

      -- Primitive: call the interpretation function
      H.Prim name _ _ ->
        "    call once_" <> name

      -- Function reference: call it
      H.Var name ->
        "    call once_" <> name

      -- Local variable - move to output
      H.LocalVar name ->
        "    movq " <> name <> ", %rax"

      -- Function pointer
      H.FunRef name ->
        "    leaq once_" <> name <> "(%rip), %rax"

      -- String literal - not supported in pure native yet
      H.StringLit _ ->
        "    xorq %rax, %rax"  -- return NULL

      -- Let binding
      H.Let _ e1 e2 ->
        genX86 e1 <> "\n" <>
        "    movq %rax, %rdi\n" <>
        genX86 e2

    -- Simple hash for unique labels
    hash :: H.IR -> Int
    hash = length . show

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

      H.Prim name _ _ ->
        "    bl once_" <> name

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

    hash :: H.IR -> Int
    hash = length . show

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

      H.Prim name _ _ ->
        "    call once_" <> name

      H.Var name ->
        "    call once_" <> name

      H.LocalVar _ -> "    # localvar: a0 unchanged"

      H.FunRef name ->
        "    la a0, once_" <> name

      H.StringLit _ -> "    li a0, 0"

      H.Let _ e1 e2 ->
        genRiscV e1 <> "\n" <>
        genRiscV e2

    hash :: H.IR -> Int
    hash = length . show
