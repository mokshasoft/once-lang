{-# LANGUAGE ScopedTypeVariables #-}
-- | System assembler invocation
--
-- This module provides functionality to invoke the system assembler
-- and optionally linker to produce object files or executables from
-- assembly source files.
--
-- Environment variables for configuration:
--   AS        - Assembler for native target
--   AS_ARM64  - Assembler for AArch64 cross-compilation
--   AS_RISCV  - Assembler for RISC-V cross-compilation
--   LD        - Linker for native target
--   LD_ARM64  - Linker for AArch64
--   LD_RISCV  - Linker for RISC-V
module Once.Backend.Assembler
  ( -- * Assembly
    assemble
  , link
    -- * Configuration
  , Target (..)
  , getAssembler
  , getLinker
    -- * Errors
  , AssemblerError (..)
  ) where

import Control.Exception (try, IOException)
import Data.Text (Text)
import qualified Data.Text as T
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | Target architecture
data Target
  = X86_64
  | AArch64
  | RiscV64
  deriving (Eq, Show)

-- | Errors from assembly/linking
data AssemblerError
  = AssemblerNotFound FilePath
  | AssemblyFailed FilePath String  -- ^ (assembler, stderr)
  | LinkerNotFound FilePath
  | LinkFailed FilePath String      -- ^ (linker, stderr)
  | IOError String
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

-- | Get the assembler for a target
-- Checks environment variables, falls back to defaults
getAssembler :: Target -> IO FilePath
getAssembler target = do
  -- Check target-specific env var first
  specific <- lookupEnv specificVar
  -- Then check generic AS
  generic <- lookupEnv "AS"
  pure $ case (specific, generic) of
    (Just s, _) -> s      -- Target-specific takes priority
    (_, Just g) -> g      -- Generic AS
    (_, _)      -> defAs  -- Default
  where
    (specificVar, defAs) = case target of
      X86_64  -> ("AS", "as")
      AArch64 -> ("AS_ARM64", "aarch64-linux-gnu-as")
      RiscV64 -> ("AS_RISCV", "riscv64-linux-gnu-as")

-- | Get the linker for a target
getLinker :: Target -> IO FilePath
getLinker target = do
  specific <- lookupEnv specificVar
  generic <- lookupEnv "LD"
  pure $ case (specific, generic) of
    (Just s, _) -> s
    (_, Just g) -> g
    (_, _)      -> defLd
  where
    (specificVar, defLd) = case target of
      X86_64  -> ("LD", "ld")
      AArch64 -> ("LD_ARM64", "aarch64-linux-gnu-ld")
      RiscV64 -> ("LD_RISCV", "riscv64-linux-gnu-ld")

------------------------------------------------------------------------
-- Assembly
------------------------------------------------------------------------

-- | Assemble a .s file to .o
-- Returns the path to the object file on success
assemble :: Target -> FilePath -> FilePath -> IO (Either AssemblerError FilePath)
assemble target asmFile objFile = do
  as <- getAssembler target
  result <- try $ readProcessWithExitCode as [asmFile, "-o", objFile] ""
  case result of
    Left (e :: IOException) ->
      pure $ Left $ IOError (show e)
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right objFile
        ExitFailure _ -> pure $ Left $ AssemblyFailed as stderr

------------------------------------------------------------------------
-- Linking
------------------------------------------------------------------------

-- | Link object files to an executable
link :: Target -> [FilePath] -> FilePath -> IO (Either AssemblerError FilePath)
link target objFiles output = do
  ld <- getLinker target
  let args = objFiles ++ ["-o", output]
  result <- try $ readProcessWithExitCode ld args ""
  case result of
    Left (e :: IOException) ->
      pure $ Left $ IOError (show e)
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right output
        ExitFailure _ -> pure $ Left $ LinkFailed ld stderr
