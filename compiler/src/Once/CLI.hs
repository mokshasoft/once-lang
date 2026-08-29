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
  , StageOptions (..)
  , CheckOptions (..)
  , ParseOptions (..)
  , OutputMode (..)
  , Target (..)
  , AllocStrategy (..)
  , InterpType (..)
  , targetExtension
  , parseTarget
  , parseInterpType
  ) where

import Control.Exception (try, SomeException)
import Control.Monad (foldM)
import Data.Char (isSpace)
import Data.List (isPrefixOf, intercalate)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (removeFile, doesFileExist, doesDirectoryExist, getCurrentDirectory, makeAbsolute)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import System.FilePath (takeBaseName, takeDirectory, (</>))
import System.Environment (lookupEnv)
import System.Process (readProcessWithExitCode)

-- Bridge to MAlonzo-generated code (stable API)
import Once.Compile.Bridge (CompileResult(..), FunSig(..), PolyFunSig(..))
import qualified Once.Compile.Bridge as Bridge
import qualified Once.Target.SymbolName as SymName

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

-- | CLI commands
data Command
  = Build BuildOptions
  | Check CheckOptions
  | Parse ParseOptions
  | Preprocess StageOptions
  | Elaborate StageOptions
  | Optimize StageOptions
  | Escape StageOptions
  | CodeGen StageOptions
  deriving (Eq, Show)

-- | Common options for pipeline-inspection stages
-- (preprocess, elaborate, optimize, escape, codegen).
-- Output goes to stdout unless stageOutput is Just FILE.
data StageOptions = StageOptions
  { stageInput  :: FilePath
  , stageOutput :: Maybe FilePath
  } deriving (Eq, Show)

-- | Output mode for build command.
-- The DEFAULT is `Infer`: program-vs-library is determined by whether the
-- module defines `main` (the anchor), not by a flag. `--lib`/`--exe` are
-- explicit overrides (with `--exe` asserting a `main` exists).
data OutputMode
  = Library     -- ^ Generate assembly library (no entry point)
  | Executable  -- ^ Generate standalone executable (requires a `main`)
  | Infer       -- ^ Default: Executable iff the module defines `main`, else Library
  deriving (Eq, Show)

-- | Target architecture
data Target
  = TargetC       -- ^ C backend (not yet implemented)
  | TargetX86_64  -- ^ x86-64 assembly (active, full IR coverage)
  | TargetX86_32  -- ^ x86-32 assembly (active via abstract-trace, simple-IR subset)
  | TargetArm64   -- ^ ARM64 assembly (not yet implemented)
  | TargetRiscV64 -- ^ RISC-V 64-bit (active via abstract-trace, simple-IR subset)
  deriving (Eq, Show)

-- | File extension for each target
targetExtension :: Target -> String
targetExtension TargetC = ".c"
targetExtension TargetX86_64 = ".s"
targetExtension TargetX86_32 = ".s"
targetExtension TargetArm64 = ".s"
targetExtension TargetRiscV64 = ".s"

-- | Parse target from string
parseTarget :: String -> Maybe Target
parseTarget "c" = Just TargetC
parseTarget "x86_64" = Just TargetX86_64
parseTarget "x86_32" = Just TargetX86_32
parseTarget "arm64" = Just TargetArm64
parseTarget "riscv64" = Just TargetRiscV64
parseTarget _ = Nothing

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
  | InterpX86_32  -- ^ x86-32 interpretation
  | InterpArm64   -- ^ ARM64 interpretation
  | InterpRiscV64 -- ^ RISC-V interpretation
  deriving (Eq, Show)

-- | Parse interpretation type from string
parseInterpType :: String -> Maybe InterpType
parseInterpType "C" = Just InterpC
parseInterpType "x86_64" = Just InterpX86_64
parseInterpType "x86_32" = Just InterpX86_32
parseInterpType "arm64" = Just InterpArm64
parseInterpType "riscv64" = Just InterpRiscV64
parseInterpType _ = Nothing

-- | Options for the build command
data BuildOptions = BuildOptions
  { buildInput     :: FilePath
  , buildOutput    :: Maybe FilePath              -- ^ Output base name (without extension)
  , buildMode      :: OutputMode                  -- ^ Library or executable
  , buildTarget    :: Target                      -- ^ Target architecture (default: TargetC)
  , buildSaveTemps :: Bool                        -- ^ Keep intermediate files (.s, .o)
  , buildOptimize  :: Bool                        -- ^ Run optimizer (default: True)
  -- Future options (not yet wired to Agda)
  , buildStrata    :: Maybe FilePath              -- ^ Strata directory path
  , buildAlloc     :: Maybe AllocStrategy         -- ^ Default allocation strategy
  , buildInterp    :: Maybe FilePath              -- ^ Legacy interpretation path
  , buildExplicitInterps :: [(InterpType, FilePath)]  -- ^ Explicit interpretations
  } deriving (Eq, Show)

-- | Options for the check command
data CheckOptions = CheckOptions
  { checkInput  :: FilePath
  , checkOutput :: Maybe FilePath
  } deriving (Eq, Show)

-- | Options for the parse command
data ParseOptions = ParseOptions
  { parseInput  :: FilePath
  , parseOutput :: Maybe FilePath
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- Main Entry Point
------------------------------------------------------------------------

-- | Run the CLI with a command
run :: Command -> IO ()
run cmd = case cmd of
  Build opts      -> runBuild opts
  Check opts      -> runCheck opts
  Parse opts      -> runParse opts
  Preprocess opts -> runPreprocess opts
  Elaborate opts  -> runNotWired "elaborate" opts
  Optimize opts   -> runNotWired "optimize" opts
  Escape opts     -> runNotWired "escape" opts
  CodeGen opts    -> runNotWired "codegen" opts

-- | Emit the output text to the stage's configured destination.
-- Nothing means stdout; Just path writes to that file. "-" also means stdout.
emitStage :: Maybe FilePath -> T.Text -> IO ()
emitStage Nothing     text = TIO.putStr text
emitStage (Just "-")  text = TIO.putStr text
emitStage (Just path) text = TIO.writeFile path text

-- | Stage not yet wired to the verified pipeline. Prints a clear
-- message so the CLI shape is discoverable without needing Agda-side
-- pretty-printers first.
runNotWired :: String -> StageOptions -> IO ()
runNotWired name _ = do
  TIO.putStrLn $ "Error: stage `" <> T.pack name <> "` is not yet wired to the Agda pipeline."
  TIO.putStrLn "This requires show functions in Agda for the intermediate IR, and corresponding"
  TIO.putStrLn "Stage/CompileResult constructors. See plan: \"Agda show functions for IRs\"."
  exitFailure

------------------------------------------------------------------------
-- Result Handling
------------------------------------------------------------------------

-- | Format function signatures for display
showFunSigs :: [FunSig] -> T.Text
showFunSigs [] = ""
showFunSigs sigs = T.unlines [funSigName sig <> " : " <> funSigType sig | sig <- sigs]

-- | Format polymorphic function signatures for display
showPolyFunSigs :: [PolyFunSig] -> T.Text
showPolyFunSigs [] = ""
showPolyFunSigs sigs =
  T.unlines [polyFunSigName sig <> " : " <> polyFunSigType sig | sig <- sigs]

------------------------------------------------------------------------
-- Parse Command
------------------------------------------------------------------------

-- | Run the preprocess command: parse + resolve imports, dump the
-- flat signature listing from the resolved Module. Exposes exactly
-- the decls the typechecker will see after the verified Agda
-- resolver has run. Imported primitives appear as
-- `<alias>.<name> : <type>`.
runPreprocess :: StageOptions -> IO ()
runPreprocess opts = do
  let inputPath = stageInput opts
  source <- TIO.readFile inputPath
  loadResult <- loadAndResolve inputPath Nothing source
  case loadResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right (mod_, _, _) ->
      case Bridge.compileFromModule Bridge.AllocHeap Bridge.Parse False Bridge.X86_64 mod_ of
        Parsed sigs polySigs -> do
          emitStage (stageOutput opts) (showFunSigs sigs <> showPolyFunSigs polySigs)
          exitSuccess
        Error err -> do
          TIO.putStrLn $ "Error: " <> err
          exitFailure
        _ -> do
          TIO.putStrLn "Internal error: unexpected result from preprocess"
          exitFailure

-- | Run the parse command: parse + resolve imports, show signatures.
runParse :: ParseOptions -> IO ()
runParse opts = do
  let inputPath = parseInput opts
  source <- TIO.readFile inputPath
  loadResult <- loadAndResolve inputPath Nothing source
  case loadResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right (mod_, _, _) ->
      case Bridge.compileFromModule Bridge.AllocHeap Bridge.Parse False Bridge.X86_64 mod_ of
        Parsed sigs polySigs -> do
          emitStage (parseOutput opts)
                    (showFunSigs sigs <> showPolyFunSigs polySigs <> "Parse OK\n")
          exitSuccess
        Error err -> do
          TIO.putStrLn $ "Error: " <> err
          exitFailure
        _ -> do
          TIO.putStrLn "Internal error: unexpected result from parse"
          exitFailure

------------------------------------------------------------------------
-- Check Command
------------------------------------------------------------------------

-- | Run the check command: parse + resolve imports + type check.
runCheck :: CheckOptions -> IO ()
runCheck opts = do
  let inputPath = checkInput opts
  source <- TIO.readFile inputPath
  loadResult <- loadAndResolve inputPath Nothing source
  case loadResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right (mod_, _, _) -> do
      -- The arch is fixed here, so these are x86-64's warnings; `build --target`
      -- reports the ones for the target actually being built.
      emitWarnings Bridge.X86_64 mod_
      -- doOpt is irrelevant for Check stage (optimizer runs after type checking)
      case Bridge.compileFromModule Bridge.AllocHeap Bridge.Check False Bridge.X86_64 mod_ of
        Checked -> do
          emitStage (checkOutput opts) "Typecheck OK\n"
          exitSuccess
        Error err -> do
          TIO.putStrLn $ "Error: " <> err
          exitFailure
        _ -> do
          TIO.putStrLn "Internal error: unexpected result from check"
          exitFailure

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
      doOpt = buildOptimize opts
      strataOpt = buildStrata opts

  -- Read source file
  source <- TIO.readFile inputPath

  -- Resolve imports (AST-level, via verified Agda resolver)
  loadResult <- loadAndResolve inputPath strataOpt source
  case loadResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right (mod_, strataDir, importPaths) -> case target of
      TargetX86_64  -> runVerifiedBuild opts outputBase Bridge.X86_64  mod_ strataDir importPaths
      TargetX86_32  -> runVerifiedBuild opts outputBase Bridge.X86_32  mod_ strataDir importPaths
      TargetRiscV64 -> runVerifiedBuild opts outputBase Bridge.RiscV64 mod_ strataDir importPaths

      -- Other targets not yet implemented
      TargetC -> do
        TIO.putStrLn "Error: C backend not yet implemented"
        TIO.putStrLn "Use --target {x86_64|x86_32|riscv64} for the active backends"
        exitFailure

      TargetArm64 -> do
        TIO.putStrLn "Error: ARM64 backend not yet implemented"
        TIO.putStrLn "Use --target {x86_64|x86_32|riscv64} for the active backends"
        exitFailure

-- | Run the verified pipeline for a Bridge.Arch and write the resulting
-- assembly. Shared by all wired backends (x86_64, x86_32, riscv64).
--
-- Plan 0.11: also assembles and statically links the per-arch impl
-- files (`Strata/Interpretations/<…>.<arch>`) for every transitive
-- import. This is how SigOp `call once_<name>` references resolve to
-- actual code (e.g. an `exit` syscall body lives in
-- `Strata/Interpretations/<interp>/Syscalls.<arch>`'s `once_exit`).
-- | D123/D116: print the target's rounding warnings to stderr.
--
-- `Bridge.moduleWarnings` is a pure query of the module and the arch, so this
-- is a REPORT, not a pipeline stage — it cannot change what is compiled. It is
-- what makes D116's "the refusal is replaced by a warning" true rather than
-- half true: before this, `Once.Warnings` computed the exact error and the ulps
-- and nothing called it.
--
-- Arch-relative on purpose (D113): the same literal is exact at one target's
-- format and rounded at another's.
emitWarnings :: Bridge.Arch -> Bridge.Module -> IO ()
emitWarnings arch m = mapM_ (hPutStrLn stderr . T.unpack) (Bridge.moduleWarnings arch m)

runVerifiedBuild :: BuildOptions -> FilePath -> Bridge.Arch -> Bridge.Module
                 -> FilePath -> [[T.Text]] -> IO ()
runVerifiedBuild opts outputBase arch mod_ strataDir importPaths =
  let allocMode = case buildAlloc opts of
        Just AllocStack -> Bridge.AllocStack
        Just AllocHeap  -> Bridge.AllocHeap
        -- Other strategies (Pool/Arena/Const) not yet supported by the
        -- elaborator's AllocMode; treat as Heap.
        _               -> Bridge.AllocHeap
  in do
  emitWarnings arch mod_
  case Bridge.compileFromModule allocMode Bridge.Build (buildOptimize opts) arch mod_ of
    Built asmText -> do
      let asmPath = outputBase ++ ".s"
          objPath = outputBase ++ ".o"

      -- Write assembly file
      TIO.writeFile asmPath asmText

      let hasMain = Bridge.moduleHasMain mod_
      effMode <- case buildMode opts of
        Infer   -> pure (if hasMain then Executable else Library)
        Library -> pure Library
        Executable
          | hasMain   -> pure Executable
          | otherwise -> do
              TIO.putStrLn "Error: --exe requires a `main` function, but this module defines none (it is a library). Use --lib, or omit the flag to infer the mode."
              exitFailure
      case effMode of
        Library -> do
          TIO.putStrLn $ "Generated: " <> T.pack asmPath
          exitSuccess

        Executable -> do
          -- Assemble user .s → .o
          asmResult <- assemble arch asmPath objPath
          case asmResult of
            Left err -> do
              TIO.putStrLn $ "Assembly failed: " <> T.pack err
              exitFailure
            Right _ -> do
              -- Plan 0.11: collect + assemble per-arch impl files for
              -- imported Strata/Interpretations modules (e.g.
              -- Strata/Interpretations/<interp>/Syscalls.<arch>). Each
              -- one becomes a .o that gets linked into the binary,
              -- providing the `once_<name>` symbols that
              -- `compile-sigOp` calls into.
              implResult <- assembleImplFiles strataDir arch importPaths
              case implResult of
                Left err -> do
                  TIO.putStrLn $ "Impl-file assembly failed: " <> T.pack err
                  exitFailure
                Right implObjs -> do
                  -- Link all .o files (user + impls) to executable
                  linkResult <- link arch (objPath : implObjs) outputBase
                  case linkResult of
                    Left err -> do
                      TIO.putStrLn $ "Link failed: " <> T.pack err
                      exitFailure
                    Right exePath -> do
                      if buildSaveTemps opts
                        then TIO.putStrLn $ "Generated: " <> T.pack asmPath <> ", " <> T.pack objPath <> ", " <> T.pack exePath
                        else do
                          removeFile asmPath
                          removeFile objPath
                          mapM_ removeFile implObjs
                          TIO.putStrLn $ "Generated: " <> T.pack exePath
                      exitSuccess

        -- unreachable: `Infer` is resolved to Library/Executable above
        Infer -> exitFailure

    Error err -> do
      TIO.putStrLn $ "Compilation error: " <> err
      exitFailure

    _ -> do
      TIO.putStrLn "Internal error: unexpected result from build"
      exitFailure

-- | Plan 0.11: assemble per-arch impl files for the given list of
-- import paths. Returns the list of `.o` paths produced (same order
-- as input). Skips imports that have no `.<arch>` companion file.
assembleImplFiles :: FilePath -> Bridge.Arch -> [[T.Text]] -> IO (Either String [FilePath])
assembleImplFiles strataDir arch paths = go paths []
  where
    go []           acc = pure (Right (reverse acc))
    go (p : rest)   acc = do
      let implPath = importPathToImplPath strataDir arch p
      exists <- doesFileExist implPath
      if not exists
        then go rest acc  -- Skip: no impl for this arch (may be intentional)
        else do
          let objPath = implPath ++ ".o"
          asmResult <- assemble arch implPath objPath
          case asmResult of
            Left err  -> pure (Left ("Failed to assemble " ++ implPath ++ ": " ++ err))
            Right _   -> do
              -- Rename each operation's CLEAN symbol (its bare signature name,
              -- as written in the impl file) to the mangled symbol the codegen
              -- calls. `objcopy --redefine-sym` is a no-op on absent symbols, so
              -- an impl that still hard-codes the mangled symbol is untouched.
              ops <- interpOpNames (importPathToFilePath strataDir p)
              let renames = [ (op, SymName.onceSymbolPath (canonicalParts p ++ [T.unpack op]))
                            | op <- ops ]
              redefResult <- redefineSymbols objPath renames
              case redefResult of
                Left err -> pure (Left ("Failed to alias symbols in " ++ implPath ++ ": " ++ err))
                Right _  -> go rest (objPath : acc)

    -- The canonical name segments for an interpretation module: the import
    -- path with the `I` → `Interpretations` rule applied (matching
    -- importPathToImplPath and what the codegen mangles).
    canonicalParts :: [T.Text] -> [String]
    canonicalParts pathParts = case map T.unpack pathParts of
      ("I" : rest) -> "Interpretations" : rest
      other        -> other

-- | Extract an interpretation module's operation names — the `signature <name>`
-- declarations in its `.once` file. These are the external SigOps whose symbols
-- the companion impl file provides. Missing/unreadable file ⇒ no ops.
interpOpNames :: FilePath -> IO [T.Text]
interpOpNames oncePath = do
  exists <- doesFileExist oncePath
  if not exists
    then pure []
    else do
      contents <- TIO.readFile oncePath
      pure [ name
           | l <- T.lines contents
           , kw : name : _ <- [T.words l]
           , kw == T.pack "signature" ]

-- | Rewrite symbol names in an object file in place (`objcopy --redefine-sym`).
-- Honors the OBJCOPY env var, else "objcopy". An empty rename list is skipped.
redefineSymbols :: FilePath -> [(T.Text, String)] -> IO (Either String ())
redefineSymbols _       []      = pure (Right ())
redefineSymbols objPath renames = do
  objcopy <- maybe "objcopy" id <$> lookupEnv "OBJCOPY"
  let args = concat [ ["--redefine-sym", T.unpack clean ++ "=" ++ mangled]
                    | (clean, mangled) <- renames ]
             ++ [objPath]   -- single file ⇒ objcopy edits it in place
  result <- try $ readProcessWithExitCode objcopy args ""
  case result of
    Left (e :: SomeException) ->
      pure $ Left $ "objcopy error: " ++ show e
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess   -> pure $ Right ()
        ExitFailure _ -> pure $ Left $ "objcopy failed (" ++ objcopy ++ "): " ++ stderr

------------------------------------------------------------------------
-- Assembler/Linker Invocation
------------------------------------------------------------------------

-- | Plan 0.57: per-arch assembler/linker flags. x86-32 uses the NATIVE
-- as/ld with 32-bit flags; x86-64 uses defaults; riscv64 goes through the
-- cross toolchain selected via the AS/LD env vars (no extra flags here).
archAsFlags :: Bridge.Arch -> [String]
archAsFlags Bridge.X86_32 = ["--32"]
archAsFlags _             = []

archLdFlags :: Bridge.Arch -> [String]
archLdFlags Bridge.X86_32 = ["-m", "elf_i386"]
archLdFlags _             = []

-- | Assemble a .s file to .o using the system assembler
-- Checks AS environment variable, falls back to "as"
assemble :: Bridge.Arch -> FilePath -> FilePath -> IO (Either String FilePath)
assemble arch asmFile objFile = do
  as <- maybe "as" id <$> lookupEnv "AS"
  result <- try $ readProcessWithExitCode as (archAsFlags arch ++ [asmFile, "-o", objFile]) ""
  case result of
    Left (e :: SomeException) ->
      pure $ Left $ "Assembler error: " ++ show e
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right objFile
        ExitFailure _ -> pure $ Left $ "Assembly failed (" ++ as ++ "): " ++ stderr

-- | Link object files to an executable using the system linker
-- Checks LD environment variable, falls back to "ld"
link :: Bridge.Arch -> [FilePath] -> FilePath -> IO (Either String FilePath)
link arch objFiles output = do
  ld <- maybe "ld" id <$> lookupEnv "LD"
  let args = archLdFlags arch ++ objFiles ++ ["-o", output]
  result <- try $ readProcessWithExitCode ld args ""
  case result of
    Left (e :: SomeException) ->
      pure $ Left $ "Linker error: " ++ show e
    Right (exitCode, _stdout, stderr) ->
      case exitCode of
        ExitSuccess -> pure $ Right output
        ExitFailure _ -> pure $ Left $ "Linking failed (" ++ ld ++ "): " ++ stderr

------------------------------------------------------------------------
-- AST-level Import Resolution (drives verified Agda resolver)
------------------------------------------------------------------------

-- | Map an import path (`["I","Foo","Bar"]`) to its disk
-- location, applying the `I` → `Interpretations` prefix rule.
importPathToFilePath :: FilePath -> [T.Text] -> FilePath
importPathToFilePath strataDir pathParts =
  let mapped = case map T.unpack pathParts of
        ("I" : rest) -> "Interpretations" : rest
        other        -> other
  in strataDir </> intercalate "/" mapped ++ ".once"

-- | Plan 0.11: per-arch implementation file extension.
-- For each Bridge.Arch, returns the file extension used by
-- Strata/Interpretations/<...>.<ext> companion files providing
-- runtime symbol implementations.
archImplExtension :: Bridge.Arch -> String
archImplExtension Bridge.X86_64  = "x86_64"
archImplExtension Bridge.X86_32  = "x86_32"
archImplExtension Bridge.RiscV64 = "riscv64"

-- | Plan 0.11: map an import path to its per-arch implementation file
-- (e.g. `["I","Foo","Bar"]` + X86_64 →
-- `Strata/Interpretations/Foo/Bar.x86_64`).
importPathToImplPath :: FilePath -> Bridge.Arch -> [T.Text] -> FilePath
importPathToImplPath strataDir arch pathParts =
  let mapped = case map T.unpack pathParts of
        ("I" : rest) -> "Interpretations" : rest
        other        -> other
  in strataDir </> intercalate "/" mapped ++ "." ++ archImplExtension arch

-- | Find the Strata directory (containing Interpretations/) by walking
-- up from the input file, then up from the CWD. Falls back to ./Strata.
findStrataDir :: FilePath -> Maybe FilePath -> IO FilePath
findStrataDir inputPath mStrataOpt = case mStrataOpt of
  Just dir -> pure dir
  Nothing  -> do
    absInputPath <- makeAbsolute inputPath
    let inputDir = takeDirectory absInputPath
    mFromInput <- findStrataUp inputDir
    case mFromInput of
      Just dir -> pure dir
      Nothing  -> do
        cwd <- getCurrentDirectory
        mFromCwd <- findStrataUp cwd
        case mFromCwd of
          Just dir -> pure dir
          Nothing  -> pure "Strata"
  where
    findStrataUp :: FilePath -> IO (Maybe FilePath)
    findStrataUp dir = do
      let candidate = dir </> "Strata"
      -- Interpretation-agnostic sentinel: a Strata dir is identified by its
      -- `Interpretations/` subtree, never by any specific interpretation.
      exists <- doesDirectoryExist (candidate </> "Interpretations")
      if exists
        then pure (Just candidate)
        else if dir == "/" || dir == "."
          then pure Nothing
          else findStrataUp (takeDirectory dir)

-- | Resolve imports at the AST level: parse the user's source via
-- Agda, recursively parse + resolve transitive imports, call Agda's
-- verified `resolveImports` with the populated ModuleMap, return the
-- flat Module ready for `compileFromModule`.
--
-- Import cycles are detected during the recursive descent (any path
-- visited twice on the same chain triggers an error).
loadAndResolve :: FilePath -> Maybe FilePath -> T.Text
               -> IO (Either String (Bridge.Module, FilePath, [[T.Text]]))
loadAndResolve inputPath mStrataOpt source = do
  strataDir <- findStrataDir inputPath mStrataOpt
  case Bridge.parseSource source of
    Left err      -> pure (Left (T.unpack err))
    Right userMod -> do
      mapResult <- buildModuleMap strataDir [] (Bridge.moduleImports userMod)
      case mapResult of
        Left err     -> pure (Left err)
        Right modMap ->
          case Bridge.resolveImports modMap userMod of
            Left err    -> pure (Left (T.unpack err))
            Right flat  -> pure (Right (flat, strataDir, map fst modMap))
  where
    -- | Recursively load all transitive imports. Returns a ModuleMap
    -- where every entry is already fully resolved (its own DImport
    -- decls flattened), so a single call to the Agda resolver at the
    -- top suffices.
    --
    -- The `inProgress` list is the chain of paths currently being
    -- resolved; re-entering one means a cycle.
    buildModuleMap
      :: FilePath
      -> [[T.Text]]                         -- ^ in-progress (cycle detection)
      -> [Bridge.ImportRef]
      -> IO (Either String [([T.Text], Bridge.Module)])
    buildModuleMap _         _           []           = pure (Right [])
    buildModuleMap strataDir inProgress  (imp : rest) = do
      let path = Bridge.importPath imp
      if path `elem` inProgress
        then pure (Left ("Import cycle detected at: " ++ showPath path))
        else do
          -- Load + parse this module
          let filePath = importPathToFilePath strataDir path
          exists <- doesFileExist filePath
          if not exists
            then pure (Left ("Import error: module not found: " ++ filePath))
            else do
              moduleSource <- TIO.readFile filePath
              case Bridge.parseSource moduleSource of
                Left err   -> pure (Left ("Parse error in imported module " ++ filePath ++ ": " ++ T.unpack err))
                Right subM -> do
                  -- Recurse for subM's own imports FIRST, so when we
                  -- resolve subM itself, modMap is complete.
                  subResult <- buildModuleMap strataDir (path : inProgress)
                                              (Bridge.moduleImports subM)
                  case subResult of
                    Left err      -> pure (Left err)
                    Right subMap  ->
                      case Bridge.resolveImports subMap subM of
                        Left err     -> pure (Left (T.unpack err))
                        Right subFlat -> do
                          -- Continue with siblings, carrying this
                          -- module's resolved entry + sub-deps.
                          tailResult <- buildModuleMap strataDir inProgress rest
                          case tailResult of
                            Left err       -> pure (Left err)
                            Right tailMap  ->
                              pure (Right ((path, subFlat) : subMap ++ tailMap))

    showPath :: [T.Text] -> String
    showPath = intercalate "." . map T.unpack
