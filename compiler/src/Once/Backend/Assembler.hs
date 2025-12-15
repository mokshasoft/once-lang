{-# LANGUAGE ScopedTypeVariables #-}
-- | System assembler invocation
--
-- This module provides functionality to invoke the system assembler
-- and optionally linker to produce object files or executables from
-- assembly source files.
--
-- Environment variables for configuration:
--   AS  - Assembler (default: as)
--   LD  - Linker (default: ld)
--
-- For cross-compilation, set AS and LD appropriately:
--   AS=aarch64-linux-gnu-as LD=aarch64-linux-gnu-ld   for ARM64
--   AS=riscv64-linux-gnu-as LD=riscv64-linux-gnu-ld  for RISC-V64
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

-- | Get the assembler
-- Checks AS environment variable, falls back to "as"
getAssembler :: IO FilePath
getAssembler = do
  as <- lookupEnv "AS"
  pure $ maybe "as" id as

-- | Get the linker
-- Checks LD environment variable, falls back to "ld"
getLinker :: IO FilePath
getLinker = do
  ld <- lookupEnv "LD"
  pure $ maybe "ld" id ld

------------------------------------------------------------------------
-- Assembly
------------------------------------------------------------------------

-- | Assemble a .s file to .o
-- Returns the path to the object file on success
assemble :: FilePath -> FilePath -> IO (Either AssemblerError FilePath)
assemble asmFile objFile = do
  as <- getAssembler
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
link :: [FilePath] -> FilePath -> IO (Either AssemblerError FilePath)
link objFiles output = do
  ld <- getLinker
  let args = objFiles ++ ["-o", output]
  result <- try $ readProcessWithExitCode ld args ""
  case result of
    Left (e :: IOException) ->
      pure $ Left $ IOError (show e)
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right output
        ExitFailure _ -> pure $ Left $ LinkFailed ld stderr
