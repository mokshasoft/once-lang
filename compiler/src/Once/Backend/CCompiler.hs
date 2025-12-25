{-# LANGUAGE ScopedTypeVariables #-}
-- | C compiler invocation
--
-- This module provides functionality to invoke the C compiler (gcc)
-- to compile C source files to object files or executables.
--
-- Environment variables for configuration:
--   CC      - C compiler (default: gcc)
--   CFLAGS  - Extra compiler flags
--
-- For cross-compilation, set CC appropriately:
--   CC=aarch64-linux-gnu-gcc   for ARM64
--   CC=riscv64-linux-gnu-gcc   for RISC-V64
module Once.Backend.CCompiler
  ( -- * Compilation
    compile
  , compileToObj
  , linkWithCC
    -- * Configuration
  , getCompiler
    -- * Errors
  , CCompilerError (..)
  ) where

import Control.Exception (try, IOException)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | Errors from C compilation
data CCompilerError
  = CompilerNotFound FilePath
  | CompilationFailed FilePath String  -- ^ (compiler, stderr)
  | LinkFailed FilePath String         -- ^ (compiler, stderr)
  | IOError String
  deriving (Eq, Show)

------------------------------------------------------------------------
-- Configuration
------------------------------------------------------------------------

-- | Get the C compiler
-- Checks CC environment variable, falls back to gcc
getCompiler :: IO FilePath
getCompiler = do
  cc <- lookupEnv "CC"
  pure $ maybe "gcc" id cc

-- | Get extra compiler flags from CFLAGS
getCFlags :: IO [String]
getCFlags = do
  cflags <- lookupEnv "CFLAGS"
  pure $ maybe [] words cflags

------------------------------------------------------------------------
-- Compilation
------------------------------------------------------------------------

-- | Compile a .c file directly to an executable
compile :: [FilePath] -> FilePath -> IO (Either CCompilerError FilePath)
compile cFiles output = do
  cc <- getCompiler
  cflags <- getCFlags
  let args = cflags ++ cFiles ++ ["-o", output, "-lm"]  -- -lm for math functions
  result <- try $ readProcessWithExitCode cc args ""
  case result of
    Left (e :: IOException) ->
      pure $ Left $ IOError (show e)
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right output
        ExitFailure _ -> pure $ Left $ CompilationFailed cc stderr

-- | Compile a .c file to a .o object file
compileToObj :: FilePath -> FilePath -> IO (Either CCompilerError FilePath)
compileToObj cFile objFile = do
  cc <- getCompiler
  cflags <- getCFlags
  let args = cflags ++ ["-c", cFile, "-o", objFile]
  result <- try $ readProcessWithExitCode cc args ""
  case result of
    Left (e :: IOException) ->
      pure $ Left $ IOError (show e)
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right objFile
        ExitFailure _ -> pure $ Left $ CompilationFailed cc stderr

-- | Link object files using the C compiler (for hybrid linking with libc)
linkWithCC :: [FilePath] -> FilePath -> IO (Either CCompilerError FilePath)
linkWithCC objFiles output = do
  cc <- getCompiler
  cflags <- getCFlags
  let args = cflags ++ objFiles ++ ["-o", output, "-lm"]  -- -lm for math functions
  result <- try $ readProcessWithExitCode cc args ""
  case result of
    Left (e :: IOException) ->
      pure $ Left $ IOError (show e)
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right output
        ExitFailure _ -> pure $ Left $ LinkFailed cc stderr
