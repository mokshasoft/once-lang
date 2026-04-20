{-# LANGUAGE ScopedTypeVariables #-}
-- | Bridge module between Haskell and MAlonzo-generated Agda code
--
-- This module provides a stable Haskell API that abstracts over the
-- MAlonzo-generated names. When regenerating MAlonzo code, only this
-- file needs to be updated.
--
-- Usage:
--   import Once.Compile.Bridge (Stage(..), CompileResult(..), compile)
--
module Once.Compile.Bridge
  ( -- * Types
    Stage (..)
  , Arch (..)
  , CompileResult (..)
  , FunSig (..)
    -- * Compilation
  , compile
  ) where

import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

-- MAlonzo imports (update these after regenerating)
import qualified MAlonzo.Code.Once.Compile as MC
import qualified MAlonzo.Code.Once.Parser as MP
import qualified MAlonzo.Code.Once.Type as MT

------------------------------------------------------------------------
-- Haskell types (stable API)
------------------------------------------------------------------------

-- | Compilation stage
data Stage
  = Parse   -- ^ Just parse, return function signatures
  | Check   -- ^ Parse + typecheck, no codegen
  | Build   -- ^ Full pipeline including codegen
  deriving (Eq, Show)

-- | Target architecture
data Arch
  = X86_64
  deriving (Eq, Show)

-- | Function signature (name and type as text)
data FunSig = FunSig
  { funSigName :: Text
  , funSigType :: Text
  } deriving (Eq, Show)

-- | Compilation result
data CompileResult
  = Parsed [FunSig]    -- ^ Parse succeeded, here are the function signatures
  | Checked            -- ^ Typecheck succeeded
  | Built Text         -- ^ Codegen succeeded, here's the assembly
  | Error Text         -- ^ Any stage failed
  deriving (Eq, Show)

------------------------------------------------------------------------
-- MAlonzo conversion (update after regenerating)
------------------------------------------------------------------------

-- | Convert Haskell Stage to MAlonzo Stage
toMStage :: Stage -> MC.T_Stage_282
toMStage Parse = MC.C_Parse_284
toMStage Check = MC.C_Check_286
toMStage Build = MC.C_Build_288

-- | Convert Haskell Arch to MAlonzo Arch
toMArch :: Arch -> MC.T_Arch_262
toMArch X86_64 = MC.C_x86'45'64_264

-- | Convert MAlonzo AgdaAny to Text (Agda String → Haskell Text)
agdaToText :: a -> Text
agdaToText = unsafeCoerce

-- | Convert MAlonzo FunInfo to Haskell FunSig
fromMFunInfo :: MP.T_FunInfo_38 -> FunSig
fromMFunInfo fi = FunSig
  { funSigName = agdaToText (MP.d_funName_48 fi)
  , funSigType = agdaToText (MT.d_showType_132 (MP.d_funType_50 fi))
  }

-- | Convert MAlonzo FunInfo list to Haskell FunSig list
fromMFunInfos :: [MP.T_FunInfo_38] -> [FunSig]
fromMFunInfos = map fromMFunInfo

-- | Convert MAlonzo CompileResult to Haskell CompileResult
fromMResult :: MC.T_CompileResult_290 -> CompileResult
fromMResult (MC.C_Parsed_292 funInfos) = Parsed (fromMFunInfos funInfos)
fromMResult (MC.C_Checked_294 _)       = Checked
fromMResult (MC.C_Built_296 asm)       = Built (agdaToText asm)
fromMResult (MC.C_Error_298 err)       = Error (agdaToText err)

------------------------------------------------------------------------
-- Public API (stable)
------------------------------------------------------------------------

-- | Compile source code
--
-- @
-- compile Parse _ _ source      -- parse only
-- compile Check _ _ source      -- typecheck (doOpt and arch ignored)
-- compile Build doOpt arch source  -- full compile
-- @
compile :: Stage -> Bool -> Arch -> Text -> CompileResult
compile stage doOpt arch source =
  fromMResult (MC.d_compile_312 (toMStage stage) doOpt (toMArch arch) source)
