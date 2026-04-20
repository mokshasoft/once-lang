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
import System.Directory (removeFile, doesFileExist, getCurrentDirectory, makeAbsolute)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.FilePath (takeBaseName, takeDirectory, (</>))
import System.Environment (lookupEnv)
import System.Process (readProcessWithExitCode)

-- Bridge to MAlonzo-generated code (stable API)
import Once.Compile.Bridge (CompileResult(..), FunSig(..))
import qualified Once.Compile.Bridge as Bridge

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

-- | Parse interpretation type from string
parseInterpType :: String -> Maybe InterpType
parseInterpType "C" = Just InterpC
parseInterpType "x86_64" = Just InterpX86_64
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

------------------------------------------------------------------------
-- Parse Command
------------------------------------------------------------------------

-- | Run the parse command: parse only
runParse :: ParseOptions -> IO ()
runParse opts = do
  let inputPath = parseInput opts
  source <- TIO.readFile inputPath
  -- Resolve imports before parsing
  resolveResult <- resolveImports inputPath Nothing source
  case resolveResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right processedSource ->
      case Bridge.compile Bridge.Parse False Bridge.X86_64 processedSource of
        Parsed sigs -> do
          emitStage (parseOutput opts) (showFunSigs sigs <> "Parse OK\n")
          exitSuccess
        Error err -> do
          TIO.putStrLn $ "Error: " <> err
          exitFailure
        _ -> do
          TIO.putStrLn "Internal error: unexpected result from parse"
          exitFailure

-- | Run the preprocess command: resolve imports, dump the source that
-- the parser will actually see. Pure Haskell — no Agda call — because
-- import resolution is currently text-level (TODO: move to Agda).
runPreprocess :: StageOptions -> IO ()
runPreprocess opts = do
  let inputPath = stageInput opts
  source <- TIO.readFile inputPath
  resolveResult <- resolveImports inputPath Nothing source
  case resolveResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right processedSource -> do
      emitStage (stageOutput opts) processedSource
      exitSuccess

------------------------------------------------------------------------
-- Check Command
------------------------------------------------------------------------

-- | Run the check command: parse and type check
runCheck :: CheckOptions -> IO ()
runCheck opts = do
  let inputPath = checkInput opts
  source <- TIO.readFile inputPath
  -- Resolve imports before type checking
  resolveResult <- resolveImports inputPath Nothing source
  case resolveResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right processedSource ->
      -- doOpt is irrelevant for Check stage (optimizer runs after type checking)
      case Bridge.compile Bridge.Check False Bridge.X86_64 processedSource of
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

  -- Resolve imports before compilation
  resolveResult <- resolveImports inputPath strataOpt source
  case resolveResult of
    Left err -> do
      TIO.putStrLn $ "Error: " <> T.pack err
      exitFailure
    Right processedSource -> case target of
      TargetX86_64 ->
        case Bridge.compile Bridge.Build doOpt Bridge.X86_64 processedSource of
          Built asmText -> do
            let asmPath = outputBase ++ ".s"
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

          Error err -> do
            TIO.putStrLn $ "Compilation error: " <> err
            exitFailure

          _ -> do
            TIO.putStrLn "Internal error: unexpected result from build"
            exitFailure

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

------------------------------------------------------------------------
-- Import Resolution
------------------------------------------------------------------------

-- | Parsed import declaration
data ImportDecl = ImportDecl
  { importPath  :: [String]    -- ^ Module path segments (e.g., ["I", "Linux", "Syscalls"])
  , importAlias :: Maybe String -- ^ Optional alias (e.g., Just "S")
  } deriving (Eq, Show)

-- | Extract import declarations from source
-- Pattern: import Module.Path [as Alias]
extractImports :: T.Text -> [ImportDecl]
extractImports source = concatMap parseImportLine (T.lines source)
  where
    parseImportLine :: T.Text -> [ImportDecl]
    parseImportLine line =
      let stripped = T.strip line
          lineStr = T.unpack stripped
      in case words lineStr of
        ("import" : rest) -> maybeToList (parseImportWords rest)
        _ -> []

    parseImportWords :: [String] -> Maybe ImportDecl
    parseImportWords [] = Nothing
    parseImportWords (pathStr : rest) =
      let pathParts = splitOnDot pathStr
      in case rest of
        ("as" : alias : _) -> Just $ ImportDecl pathParts (Just alias)
        [] -> Just $ ImportDecl pathParts Nothing
        _ -> Just $ ImportDecl pathParts Nothing

    splitOnDot :: String -> [String]
    splitOnDot = go []
      where
        go acc [] = [reverse acc]
        go acc ('.' : cs) = reverse acc : go [] cs
        go acc (c : cs) = go (c : acc) cs

    maybeToList :: Maybe a -> [a]
    maybeToList Nothing = []
    maybeToList (Just x) = [x]

-- | Convert import path to Strata file path
-- "I" prefix maps to "Interpretations" directory
importPathToFilePath :: FilePath -> ImportDecl -> FilePath
importPathToFilePath strataDir imp =
  let pathParts = importPath imp
      -- Map "I" prefix to "Interpretations"
      mappedParts = case pathParts of
        ("I" : rest) -> "Interpretations" : rest
        other -> other
  in strataDir </> intercalate "/" mappedParts ++ ".once"

-- | Extract primitive declarations from a module source
-- Pattern: primitive name : Type
extractPrimitives :: T.Text -> [(String, String)]
extractPrimitives source = concatMap parsePrimLine (T.lines source)
  where
    parsePrimLine :: T.Text -> [(String, String)]
    parsePrimLine line =
      let stripped = T.strip line
          lineStr = T.unpack stripped
      in case words lineStr of
        ("primitive" : name : ":" : typeParts) ->
          [(name, unwords typeParts)]
        _ -> []

-- | Rename primitives with module alias
-- e.g., ("exit", "Eff Int Unit") with alias "S" -> ("S.exit", "Eff Int Unit")
-- This matches the lookup format: RQualified "exit" "S" looks up "S.exit"
qualifyPrimitives :: Maybe String -> [(String, String)] -> [(String, String)]
qualifyPrimitives Nothing prims = prims  -- No alias, keep original names
qualifyPrimitives (Just alias) prims =
  [(alias ++ "." ++ name, ty) | (name, ty) <- prims]

-- | Format primitives as Once source lines
formatPrimitives :: [(String, String)] -> T.Text
formatPrimitives prims = T.unlines
  [T.pack $ "primitive " ++ name ++ " : " ++ ty | (name, ty) <- prims]

-- | Find Strata directory relative to input file or from options
findStrataDir :: FilePath -> Maybe FilePath -> IO FilePath
findStrataDir inputPath mStrataOpt = case mStrataOpt of
  Just dir -> pure dir
  Nothing -> do
    -- Make input path absolute for reliable traversal
    absInputPath <- makeAbsolute inputPath
    -- Try to find Strata directory relative to input file
    -- Walk up directories looking for "Strata" folder
    let inputDir = takeDirectory absInputPath
    mStrataFromInput <- findStrataUp inputDir
    case mStrataFromInput of
      Just dir -> pure dir
      Nothing -> do
        -- Also try current working directory and its parents
        cwd <- getCurrentDirectory
        mStrataFromCwd <- findStrataUp cwd
        case mStrataFromCwd of
          Just dir -> pure dir
          Nothing -> pure "Strata"  -- Default fallback
  where
    findStrataUp :: FilePath -> IO (Maybe FilePath)
    findStrataUp dir = do
      let candidate = dir </> "Strata"
      exists <- doesFileExist (candidate </> "Interpretations" </> "Linux" </> "Syscalls.once")
      if exists
        then pure (Just candidate)
        else if dir == "/" || dir == "."
          then pure Nothing
          else findStrataUp (takeDirectory dir)

-- | Resolve imports and inline primitives with qualified names
-- Returns preprocessed source with all imported primitives inlined
resolveImports :: FilePath -> Maybe FilePath -> T.Text -> IO (Either String T.Text)
resolveImports inputPath mStrataOpt source = do
  strataDir <- findStrataDir inputPath mStrataOpt
  let imports = extractImports source
  result <- foldM (processImport strataDir) (Right []) imports
  case result of
    Left err -> pure $ Left err
    Right allPrims ->
      let primLines = formatPrimitives allPrims
          -- Insert primitives after any comments at the top
          processedSource = insertPrimitives primLines source
      in pure $ Right processedSource
  where
    processImport :: FilePath -> Either String [(String, String)]
                  -> ImportDecl -> IO (Either String [(String, String)])
    processImport _ (Left err) _ = pure $ Left err
    processImport strataDir (Right accPrims) imp = do
      let modulePath = importPathToFilePath strataDir imp
      exists <- doesFileExist modulePath
      if not exists
        then pure $ Left $ "Import error: module not found: " ++ modulePath
        else do
          moduleSource <- TIO.readFile modulePath
          let prims = extractPrimitives moduleSource
              qualifiedPrims = qualifyPrimitives (importAlias imp) prims
          pure $ Right (accPrims ++ qualifiedPrims)

    -- Insert primitive declarations after leading comments/blank lines
    insertPrimitives :: T.Text -> T.Text -> T.Text
    insertPrimitives prims src =
      let (header, body) = splitHeader src
      in header <> prims <> body

    -- Split source into comment header and body
    splitHeader :: T.Text -> (T.Text, T.Text)
    splitHeader src =
      let ls = T.lines src
          (headerLines, bodyLines) = span isHeaderLine ls
      in (T.unlines headerLines, T.unlines bodyLines)

    isHeaderLine :: T.Text -> Bool
    isHeaderLine line =
      let stripped = T.strip line
      in T.null stripped || T.isPrefixOf "--" stripped || T.isPrefixOf "import " stripped
