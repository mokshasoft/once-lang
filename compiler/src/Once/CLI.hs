{-# LANGUAGE ScopedTypeVariables #-}
-- | Simplified CLI for Once compiler
--
-- Architecture:
--   Haskell CLI: I/O only (read files, write files, invoke as/ld)
--   Agda (MAlonzo): all compilation logic (parse → elaborate → optimize → codegen → emit)
--
-- For x86_64 target, the entire pipeline is in Agda via MAlonzo.
-- Other targets return "Not yet implemented".
module Once.CLI
  ( run
  , Command (..)
  , BuildOptions (..)
  , CheckOptions (..)
  , OutputMode (..)
  , Target (..)
  , AllocStrategy (..)
  , InterpType (..)
  , targetExtension
  , parseTarget
  , parseInterpType
  ) where

import Control.Exception (try, SomeException)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (removeFile)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.FilePath (takeBaseName)
import System.Environment (lookupEnv)
import System.Process (readProcessWithExitCode)
import Unsafe.Coerce (unsafeCoerce)

-- MAlonzo-extracted Agda compilation entry point
import qualified MAlonzo.Code.Once.CompileX86v3 as MCompile
import qualified MAlonzo.Code.Data.Sum.Base as MSum

-- | Convert MAlonzo AgdaAny to Text (Agda String → Haskell Text)
agdaToText :: a -> Text
agdaToText = unsafeCoerce

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | CLI commands
data Command
  = Build BuildOptions
  | Check CheckOptions
  deriving (Eq, Show)

-- | Output mode for build command
data OutputMode
  = Library     -- ^ Generate assembly library
  | Executable  -- ^ Generate standalone executable with main()
  deriving (Eq, Show)

-- | Target architecture
data Target
  = TargetC       -- ^ C backend (not yet implemented)
  | TargetX86_64  -- ^ x86-64 assembly (active)
  | TargetArm64   -- ^ ARM64 assembly (not yet implemented)
  | TargetRiscV64 -- ^ RISC-V 64-bit (not yet implemented)
  deriving (Eq, Show)

-- | Allocation strategy (for future use)
data AllocStrategy
  = AllocStack    -- ^ Stack allocation
  | AllocHeap     -- ^ Heap allocation
  | AllocPool     -- ^ Pool allocation
  | AllocArena    -- ^ Arena allocation
  | AllocConst    -- ^ Constant/static allocation
  deriving (Eq, Show)

-- | Interpretation type for explicit imports (for future use)
data InterpType
  = InterpC       -- ^ C interpretation
  | InterpX86_64  -- ^ x86-64 interpretation
  | InterpArm64   -- ^ ARM64 interpretation
  | InterpRiscV64 -- ^ RISC-V interpretation
  deriving (Eq, Show)

-- | File extension for each target
targetExtension :: Target -> String
targetExtension TargetC = ".c"
targetExtension TargetX86_64 = ".s"
targetExtension TargetArm64 = ".s"
targetExtension TargetRiscV64 = ".s"

-- | Parse target from string
parseTarget :: String -> Maybe Target
parseTarget "c" = Just TargetC
parseTarget "x86_64" = Just TargetX86_64
parseTarget "arm64" = Just TargetArm64
parseTarget "riscv64" = Just TargetRiscV64
parseTarget _ = Nothing

-- | Parse interpretation type from string
parseInterpType :: String -> Maybe InterpType
parseInterpType "C" = Just InterpC
parseInterpType "x86_64" = Just InterpX86_64
parseInterpType "arm64" = Just InterpArm64
parseInterpType "riscv64" = Just InterpRiscV64
parseInterpType _ = Nothing

-- | Options for the build command
data BuildOptions = BuildOptions
  { buildInput  :: FilePath
  , buildOutput :: Maybe FilePath       -- ^ Output base name (without extension)
  , buildMode   :: OutputMode           -- ^ Library or executable
  , buildInterp :: Maybe FilePath       -- ^ Legacy: interpretation path (not used by x86v3)
  , buildAlloc  :: Maybe AllocStrategy  -- ^ Default allocation strategy (not used by x86v3)
  , buildStrata :: Maybe FilePath       -- ^ Strata directory path (not used by x86v3)
  , buildTarget :: Target               -- ^ Target architecture (default: TargetC)
  , buildSaveTemps :: Bool              -- ^ Keep intermediate files (.s, .o)
  , buildExplicitInterps :: [(InterpType, FilePath)]  -- ^ Explicit interpretations (not used by x86v3)
  } deriving (Eq, Show)

-- | Options for the check command
data CheckOptions = CheckOptions
  { checkInput  :: FilePath
  , checkStrata :: Maybe FilePath       -- ^ Strata directory path (not used by x86v3)
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- Main Entry Point
------------------------------------------------------------------------

-- | Run the CLI with a command
run :: Command -> IO ()
run cmd = case cmd of
  Build opts -> runBuild opts
  Check opts -> runCheck opts

------------------------------------------------------------------------
-- Build Command
------------------------------------------------------------------------

-- | Run the build command
-- For x86_64: calls Agda pipeline via MAlonzo, then assembles/links
-- Other targets: not yet implemented
runBuild :: BuildOptions -> IO ()
runBuild opts = do
  let inputPath = buildInput opts
      outputBase = case buildOutput opts of
        Just base -> base
        Nothing -> takeBaseName inputPath
      target = buildTarget opts

  -- Read source file
  source <- TIO.readFile inputPath

  case target of
    TargetX86_64 -> do
      -- Call Agda compilation pipeline (parse → elaborate → optimize → codegen → emit)
      let result = MCompile.d_compileX86v3_92 source
      case result of
        MSum.C_inj'8321'_38 err -> do
          TIO.putStrLn $ "Compilation error: " <> agdaToText err
          exitFailure
        MSum.C_inj'8322'_42 asmSource -> do
          let asmText = agdaToText asmSource
              asmPath = outputBase ++ ".s"
              objPath = outputBase ++ ".o"

          -- Write assembly file
          TIO.writeFile asmPath asmText

          case buildMode opts of
            Library -> do
              TIO.putStrLn $ "Generated: " <> T.pack asmPath
              exitSuccess

            Executable -> do
              -- Assemble .s to .o
              asmResult <- assemble asmPath objPath
              case asmResult of
                Left err -> do
                  TIO.putStrLn $ "Assembly failed: " <> T.pack err
                  exitFailure
                Right _ -> do
                  -- Link .o to executable
                  linkResult <- link [objPath] outputBase
                  case linkResult of
                    Left err -> do
                      TIO.putStrLn $ "Link failed: " <> T.pack err
                      exitFailure
                    Right exePath -> do
                      -- Clean up intermediate files unless --save-temps
                      if buildSaveTemps opts
                        then TIO.putStrLn $ "Generated: " <> T.pack asmPath <> ", " <> T.pack objPath <> ", " <> T.pack exePath
                        else do
                          removeFile asmPath
                          removeFile objPath
                          TIO.putStrLn $ "Generated: " <> T.pack exePath
                      exitSuccess

    -- Other targets not yet implemented
    TargetC -> do
      TIO.putStrLn "Error: C backend not yet implemented"
      TIO.putStrLn "Use --target x86_64 for the active backend"
      exitFailure

    TargetArm64 -> do
      TIO.putStrLn "Error: ARM64 backend not yet implemented"
      TIO.putStrLn "Use --target x86_64 for the active backend"
      exitFailure

    TargetRiscV64 -> do
      TIO.putStrLn "Error: RISC-V backend not yet implemented"
      TIO.putStrLn "Use --target x86_64 for the active backend"
      exitFailure

------------------------------------------------------------------------
-- Check Command
------------------------------------------------------------------------

-- | Run the check command: parse and type check
runCheck :: CheckOptions -> IO ()
runCheck opts = do
  let inputPath = checkInput opts

  -- Read source file
  source <- TIO.readFile inputPath

  -- Use the same pipeline but only check for errors (no codegen output needed)
  let result = MCompile.d_compileX86v3_92 source
  case result of
    MSum.C_inj'8321'_38 err -> do
      TIO.putStrLn $ "Error: " <> agdaToText err
      exitFailure
    MSum.C_inj'8322'_42 _ -> do
      TIO.putStrLn "OK"
      exitSuccess

------------------------------------------------------------------------
-- Assembler/Linker Invocation
------------------------------------------------------------------------

-- | Assemble a .s file to .o using the system assembler
-- Checks AS environment variable, falls back to "as"
assemble :: FilePath -> FilePath -> IO (Either String FilePath)
assemble asmFile objFile = do
  as <- maybe "as" id <$> lookupEnv "AS"
  result <- try $ readProcessWithExitCode as [asmFile, "-o", objFile] ""
  case result of
    Left (e :: SomeException) ->
      pure $ Left $ "Assembler error: " ++ show e
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right objFile
        ExitFailure _ -> pure $ Left $ "Assembly failed (" ++ as ++ "): " ++ stderr

-- | Link object files to an executable using the system linker
-- Checks LD environment variable, falls back to "ld"
link :: [FilePath] -> FilePath -> IO (Either String FilePath)
link objFiles output = do
  ld <- maybe "ld" id <$> lookupEnv "LD"
  let args = objFiles ++ ["-o", output]
  result <- try $ readProcessWithExitCode ld args ""
  case result of
    Left (e :: SomeException) ->
      pure $ Left $ "Linker error: " ++ show e
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right output
        ExitFailure _ -> pure $ Left $ "Linking failed (" ++ ld ++ "): " ++ stderr
