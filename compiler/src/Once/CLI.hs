{-# LANGUAGE ScopedTypeVariables #-}
module Once.CLI
  ( run
  , Command (..)
  , BuildOptions (..)
  , CheckOptions (..)
  , OutputMode (..)
  , AllocStrategy (..)
  , Target (..)
  , InterpType (..)
  , targetExtension
  , parseTarget
  , parseInterpType
  ) where

import Control.Applicative ((<|>))
import Control.Exception (try, SomeException)
import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified System.IO
import System.Directory (listDirectory, doesDirectoryExist, removeFile)
import System.Exit (ExitCode(..), exitFailure, exitSuccess)
import System.FilePath (takeBaseName, takeDirectory, (</>))
import System.Environment (lookupEnv)
import System.Process (readProcessWithExitCode)

import Once.Backend.CCompiler as CC
import Once.Module (ModuleEnv (..), emptyModuleEnv, resolveImports, formatModuleError,
                    LoadedModule (..), Import (..), AllocStrategy (..), extractImports,
                    buildImportsForTypeChecker)
import qualified MAlonzo.Code.Agda.Builtin.Sigma as Sigma
import Once.MAlonzo (fromMAlonzoType)
import qualified MAlonzo.Code.Once.Type as MT
import qualified MAlonzo.Code.Once.IR as MIR
import qualified MAlonzo.Code.Once.Optimize as MO
import qualified MAlonzo.Code.Once.Backend.C.CodeGen as MCG
import qualified MAlonzo.Code.Once.Backend.C.Emit as MCE
import qualified MAlonzo.Code.Once.Backend.Emit as MEmit
import Once.Type (Type (..))
-- Agda parser (MAlonzo-extracted)
import qualified MAlonzo.Code.Once.Parser as MP
import qualified MAlonzo.Code.Once.Parser.Module as MPM
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate as VTE
import qualified MAlonzo.Code.Once.Surface.Elaborate as VSE
import qualified MAlonzo.Code.Once.Surface.Syntax as VSS
import Unsafe.Coerce (unsafeCoerce)

-- | CLI commands
data Command
  = Build BuildOptions
  | Check CheckOptions
  deriving (Eq, Show)

-- | Output mode for build command
data OutputMode
  = Library     -- ^ Generate C library (header + source)
  | Executable  -- ^ Generate standalone executable with main()
  deriving (Eq, Show)

-- | Target architecture
data Target
  = TargetC       -- ^ C backend (default)
  | TargetX86_64  -- ^ x86-64 assembly
  | TargetArm64   -- ^ ARM64 assembly
  | TargetRiscV64 -- ^ RISC-V 64-bit
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

-- | Interpretation implementation type
data InterpType
  = InterpC       -- ^ C implementation (.c)
  | InterpX86_64  -- ^ x86-64 assembly (.x86_64)
  | InterpArm64   -- ^ ARM64 assembly (.arm64)
  | InterpRiscV64 -- ^ RISC-V assembly (.riscv64)
  deriving (Eq, Show)

-- | Parse interpretation type from string
parseInterpType :: String -> Maybe InterpType
parseInterpType "C" = Just InterpC
parseInterpType "c" = Just InterpC
parseInterpType "x86_64" = Just InterpX86_64
parseInterpType "arm64" = Just InterpArm64
parseInterpType "riscv64" = Just InterpRiscV64
parseInterpType _ = Nothing

-- | File extension for each interpretation type
interpTypeExtension :: InterpType -> String
interpTypeExtension InterpC = ".c"
interpTypeExtension InterpX86_64 = ".x86_64"
interpTypeExtension InterpArm64 = ".arm64"
interpTypeExtension InterpRiscV64 = ".riscv64"

-- | Options for the build command
data BuildOptions = BuildOptions
  { buildInput  :: FilePath
  , buildOutput :: Maybe FilePath       -- ^ Output base name (without extension)
  , buildMode   :: OutputMode           -- ^ Library or executable
  , buildInterp :: Maybe FilePath       -- ^ Path to interpretation directory (deprecated, use --strata)
  , buildAlloc  :: Maybe AllocStrategy  -- ^ Default allocation strategy (Nothing = use per-function annotations)
  , buildStrata :: Maybe FilePath       -- ^ Path to Strata directory (default: look relative to input file)
  , buildTarget :: Target               -- ^ Target architecture (default: TargetC)
  , buildSaveTemps :: Bool              -- ^ Keep intermediate files (.c, .s, .o)
  , buildExplicitInterps :: [(InterpType, String)]  -- ^ Explicit interpretations: -I:TYPE MODULE
  } deriving (Eq, Show)

-- | Options for the check command
data CheckOptions = CheckOptions
  { checkInput  :: FilePath
  , checkStrata :: Maybe FilePath  -- ^ Optional Strata directory path
  } deriving (Eq, Show)

-- | Run the CLI with a command
run :: Command -> IO ()
run cmd = case cmd of
  Build opts -> runBuild opts
  Check opts -> runCheck opts

-- | Run the build command: parse -> resolve imports -> typecheck -> elaborate -> optimize -> codegen
runBuild :: BuildOptions -> IO ()
runBuild opts = do
  let inputPath = buildInput opts
      outputBase = case buildOutput opts of
        Just base -> base
        Nothing -> takeBaseName inputPath
      mode = buildMode opts

  -- Determine Strata path and target
  strataPath <- findStrataPath opts inputPath
  let target = buildTarget opts
      targetExt = targetExtension target

  -- Read input file
  source <- TIO.readFile inputPath

  -- Parse (Agda parser via MAlonzo)
  case MP.d_parse_4 source of
    Nothing -> do
      TIO.putStrLn "Parse error: failed to parse module"
      exitFailure
    Just agdaModule -> do
      -- Extract imports from Agda module and resolve
      let imports = extractImports agdaModule
          initialEnv = emptyModuleEnv strataPath targetExt
      resolveResult <- resolveImports initialEnv imports
      case resolveResult of
        Left modErr -> do
          TIO.putStrLn $ "Module error: " <> formatModuleError modErr
          exitFailure
        Right modEnv -> do
              -- Extract primitives and functions via Agda
              let aliases = MP.d_extractAliases_18 agdaModule
                  primitives = extractAgdaPrimitives agdaModule
                  funInfos = MP.d_extractFunctions_58 aliases agdaModule
                  -- Don't inline: functions are now in context and will be called
                  allFunInfos = funInfos

              -- Generate C based on mode
              case mode of
                Library -> do
                  -- Library mode: generate code for all functions (no main required)
                  case allFunInfos of
                    [] -> do
                      TIO.putStrLn "Error: No functions found"
                      exitFailure
                    _ -> do
                      -- Elaborate all functions (Agda-verified, already inlined)
                      elaborateResult <- elaborateAllAgda modEnv allFunInfos
                      case elaborateResult of
                        Left err -> do
                          TIO.putStrLn $ "Elaboration error: " <> T.pack (show err)
                          exitFailure
                        Right elaboratedFunctions -> do
                          -- Branch based on target
                          case target of
                            TargetC -> do
                              -- Generate library with all functions (C backend via Agda codegen)
                              let (header, source') = generateLibraryAll elaboratedFunctions
                                  headerPath = outputBase ++ ".h"
                                  sourcePath = outputBase ++ ".c"
                              TIO.writeFile headerPath header
                              TIO.writeFile sourcePath source'
                              TIO.putStrLn $ "Generated: " <> T.pack headerPath <> ", " <> T.pack sourcePath
                              exitSuccess

                            nativeTarget -> do
                              -- Native targets: use MAlonzo-extracted verified backends
                              let asmSource = generateAssemblyAll nativeTarget elaboratedFunctions
                                  asmPath = outputBase ++ ".s"
                              TIO.writeFile asmPath asmSource
                              TIO.putStrLn $ "Generated: " <> T.pack asmPath
                              exitSuccess

                Executable -> do
                  -- Executable mode: requires main
                  case filter (\fi -> MP.d_funName_48 fi == "main") allFunInfos of
                    [] -> do
                      TIO.putStrLn "Error: No main function found"
                      exitFailure
                    (mainFi:_) -> do
                      -- D032: main must be effectful (Eff Unit Unit or IO Unit)
                      let mainTy = fromMAlonzoType (MP.d_funType_50 mainFi)
                      case mainTy of
                        TEff TUnit TUnit -> pure ()  -- OK: Eff Unit Unit or IO Unit
                        _ -> do
                          TIO.putStrLn $ "Error: main must have type 'Eff Unit Unit' or 'IO Unit', got: " <> T.pack (show mainTy)
                          TIO.putStrLn "Hint: Use 'main : IO Unit' or 'main : Eff Unit Unit'"
                          exitFailure

                      -- Elaborate all functions (Agda-verified, already inlined)
                      -- Put main first, then others
                      let otherFunInfos = filter (\fi -> MP.d_funName_48 fi /= "main") allFunInfos
                      elaborateResult <- elaborateAllAgda modEnv (mainFi : otherFunInfos)
                      case elaborateResult of
                        Left err -> do
                          TIO.putStrLn $ "Elaboration error: " <> T.pack (show err)
                          exitFailure
                        Right elaboratedFunctions -> do
                          -- Branch based on target
                          case target of
                            TargetC -> do
                              -- For executable, generate C with main() wrapper
                              -- Load interpretation C code from --interp (legacy)
                              interpCodeLegacy <- case buildInterp opts of
                                Nothing -> pure ""
                                Just interpPath -> loadInterpretationCode interpPath

                              -- Collect target-specific files from imported interpretation modules
                              let importedTargetFiles = collectTargetFiles modEnv
                              importedCode <- T.concat <$> mapM TIO.readFile importedTargetFiles

                              -- Resolve and load explicit interpretation files from -I:TYPE MODULE
                              let explicitFiles = resolveExplicitInterps strataPath (buildExplicitInterps opts)
                              explicitCode <- T.concat <$> mapM TIO.readFile explicitFiles

                              let sourcePath = outputBase ++ ".c"
                                  alloc = fromAgdaAlloc (MP.d_funAlloc_52 mainFi) <|> buildAlloc opts
                                  interpCode = interpCodeLegacy <> "\n" <> importedCode <> "\n" <> explicitCode
                                  source' = generateExecutableAll elaboratedFunctions alloc primitives interpCode
                              TIO.writeFile sourcePath source'

                              -- Compile C to executable
                              result <- CC.compile [sourcePath] outputBase
                              case result of
                                Left err -> do
                                  TIO.putStrLn $ "Compilation failed: " <> T.pack (show err)
                                  exitFailure
                                Right exePath -> do
                                  -- Clean up intermediate .c unless --save-temps
                                  if buildSaveTemps opts
                                    then TIO.putStrLn $ "Generated: " <> T.pack sourcePath <> ", " <> T.pack exePath
                                    else do
                                      removeFile sourcePath
                                      TIO.putStrLn $ "Generated: " <> T.pack exePath
                                  exitSuccess

                            nativeTarget -> do
                              -- Native targets: generate assembly and assemble/link
                              let asmSource = generateAssemblyAll nativeTarget elaboratedFunctions
                                  asmPath = outputBase ++ ".s"
                                  objPath = outputBase ++ ".o"
                              TIO.writeFile asmPath asmSource

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

-- | Find the Strata directory path
-- Priority: 1) --strata flag, 2) Strata/ relative to input, 3) Strata/ in current directory
findStrataPath :: BuildOptions -> FilePath -> IO FilePath
findStrataPath opts inputPath = case buildStrata opts of
  Just path -> pure path
  Nothing -> do
    -- Try relative to input file
    let inputDir = takeDirectory inputPath
        relativePath = inputDir </> "Strata"
    exists1 <- doesDirectoryExist relativePath
    if exists1
      then pure relativePath
      else do
        -- Try in current directory
        exists2 <- doesDirectoryExist "Strata"
        if exists2
          then pure "Strata"
          else pure relativePath  -- Return the first attempt (will error if used)

-- | Collect all target-specific file paths from loaded interpretation modules
collectTargetFiles :: ModuleEnv -> [FilePath]
collectTargetFiles env = [path | LoadedModule { lmTargetPath = Just path } <- Map.elems (meModules env)]

-- | Convert module path to file path
-- I.Linux.Syscalls → Interpretations/Linux/Syscalls
-- D.Canonical → Derived/Canonical
moduleToPath :: String -> FilePath
moduleToPath modPath = case modPath of
  'I':'.':rest -> "Interpretations" </> dotsToSlash rest
  'D':'.':rest -> "Derived" </> dotsToSlash rest
  _ -> dotsToSlash modPath
  where
    dotsToSlash = map (\c -> if c == '.' then '/' else c)

-- | Resolve explicit interpretation files from -I:TYPE MODULE flags
-- Returns list of resolved file paths
resolveExplicitInterps :: FilePath -> [(InterpType, String)] -> [FilePath]
resolveExplicitInterps strataPath = map resolve
  where
    resolve (itype, modPath) =
      strataPath </> moduleToPath modPath ++ interpTypeExtension itype

-- | Run the check command: parse -> typecheck
runCheck :: CheckOptions -> IO ()
runCheck opts = do
  let inputPath = checkInput opts

  -- Determine Strata path (for resolving imports)
  strataPath <- case checkStrata opts of
    Just path -> pure path
    Nothing -> do
      -- Try relative to input file
      let inputDir = takeDirectory inputPath
          relativePath = inputDir </> "Strata"
      exists1 <- doesDirectoryExist relativePath
      if exists1
        then pure relativePath
        else do
          -- Try in current directory
          exists2 <- doesDirectoryExist "Strata"
          pure $ if exists2 then "Strata" else relativePath

  let targetExt = ".c"  -- Default to C for type checking (doesn't affect checks)

  -- Read input file
  source <- TIO.readFile inputPath

  -- Parse (Agda parser via MAlonzo)
  case MP.d_parse_4 source of
    Nothing -> do
      TIO.putStrLn "Parse error: failed to parse module"
      exitFailure
    Just agdaModule -> do
      -- Resolve imports
      let imports = extractImports agdaModule
          initialEnv = emptyModuleEnv strataPath targetExt
      resolveResult <- resolveImports initialEnv imports
      case resolveResult of
        Left modErr -> do
          TIO.putStrLn $ "Module error: " <> formatModuleError modErr
          exitFailure
        Right modEnv -> do
          -- Type check by running elaboration (Agda is the type checker)
          let aliases = MP.d_extractAliases_18 agdaModule
              funInfos = MP.d_extractFunctions_58 aliases agdaModule
              -- Don't inline: functions are now in context and will be called
              allFunInfos = funInfos
          elaborateResult <- elaborateAllAgda modEnv allFunInfos
          case elaborateResult of
            Left err -> do
              TIO.putStrLn $ "Type error: " <> T.pack err
              exitFailure
            Right _ -> do
              TIO.putStrLn "OK"
              exitSuccess

-- | Load all C code from an interpretation directory
-- Concatenates all .c files found in the directory
loadInterpretationCode :: FilePath -> IO Text
loadInterpretationCode interpPath = do
  files <- listDirectory interpPath
  let cFiles = filter (".c" `isSuffixOf`) files
  cContents <- mapM (\f -> TIO.readFile (interpPath </> f)) cFiles
  pure (T.intercalate "\n\n" cContents)

-- | Extract primitives from an Agda-parsed module (converting types)
extractAgdaPrimitives :: MPM.T_Module_42 -> [(Text, Type)]
extractAgdaPrimitives (MPM.C_mkModule_48 decls) =
  [ (name, fromMAlonzoType ty) | MPM.C_DPrimitive_36 name ty <- decls ]

-- | Convert Agda AllocStrategy to Haskell AllocStrategy
fromAgdaAlloc :: Maybe MPM.T_AllocStrategy_6 -> Maybe AllocStrategy
fromAgdaAlloc Nothing = Nothing
fromAgdaAlloc (Just MPM.C_Stack_8) = Just AllocStack
fromAgdaAlloc (Just MPM.C_Heap_10) = Just AllocHeap
fromAgdaAlloc (Just MPM.C_Pool_12) = Just AllocPool
fromAgdaAlloc (Just MPM.C_Arena_14) = Just AllocArena
fromAgdaAlloc (Just MPM.C_Const_16) = Just AllocConst

-- | Elaborate all functions using the Agda-parsed FunInfo list.
--
-- For each function:
-- 1. Body is already inlined (via d_inlineAll_120)
-- 2. RawExpr is passed directly to Agda's inferElab (no Haskell conversion)
-- 3. Convert Surface.Expr → IR via Agda's elaborate
-- 4. Optimize using the verified Agda optimizer
--
-- Returns MAlonzo types and IR directly (no Haskell IR conversion).
elaborateAllAgda :: ModuleEnv -> [MP.T_FunInfo_38]
                 -> IO (Either String [(Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10)])
elaborateAllAgda modEnv fns = go [] fns
  where
    -- Base imports from loaded modules
    baseImportsHs = buildImportsForTypeChecker modEnv

    -- Accumulate defined function signatures as we process each function
    go _defined [] = pure (Right [])
    go defined (fi:rest) = do
      let name = MP.d_funName_48 fi
          rawExpr = MP.d_funBody_54 fi  -- Already T_RawExpr_34, no conversion!
          funMType = MP.d_funType_50 fi
          ty = fromMAlonzoType funMType
          alloc = fromAgdaAlloc (MP.d_funAlloc_52 fi)
      TIO.hPutStrLn System.IO.stderr $ "Type checking: " <> name
      verifiedResult <- try (pure $! elaborateOne defined name funMType rawExpr) :: IO (Either SomeException (Either String (MT.T_Type_32, MIR.T_IR_10)))
      case verifiedResult of
        Right (Right (inferredType, optimizedIR)) -> do
          TIO.hPutStrLn System.IO.stderr $ "  OK: " <> name
          -- Add this function to the defined list for subsequent functions
          restResult <- go ((name, funMType) : defined) rest
          pure $ case restResult of
            Left err -> Left err
            Right irs -> Right ((name, ty, alloc, inferredType, optimizedIR) : irs)
        Left exc -> do
          TIO.hPutStrLn System.IO.stderr $ "  FATAL: " <> name <> ": " <> T.pack (show exc)
          pure (Left $ T.unpack name ++ ": fatal error: " ++ show exc)
        Right (Left err) -> do
          TIO.hPutStrLn System.IO.stderr $ "  FAIL: " <> name <> ": " <> T.pack err
          pure (Left $ T.unpack name ++ ": " ++ err)

    -- Run Agda type checking + elaboration + optimization for a single expression.
    -- The context includes:
    -- 1. Imported primitives (from qualified imports)
    -- 2. Previously defined functions in this module
    -- 3. The function's own name (for recursion)
    -- Returns the MAlonzo type and optimized MAlonzo IR.
    elaborateOne defined funName funType rawExpr =
      -- Combine base imports with previously defined functions
      let allImportsHs = baseImportsHs ++ defined
          importsAgda = map (\(n, t) -> Sigma.C__'44'__32 (unsafeCoerce n) (unsafeCoerce t)) allImportsHs
          -- Add self-reference for recursion: function can call itself
          ctx = VTE.d_ctxWithImportsAndSelf_364 importsAgda (unsafeCoerce funName) (unsafeCoerce funType)
      -- Use checkElab (not inferElab) so lambda parameters get correct types from signature
      in case VTE.d_checkElab_1964 ctx rawExpr funType of
        VTE.C_failure_328 errMsg ->
          Left $ "Type checking failed: " ++ show errMsg
        VTE.C_success_326 surfaceExpr _depth _fresh _usage ->
          let irExpr = VSE.d_elaborate_112 0 (VSS.C_'8709'_8) funType surfaceExpr
              optimized = MO.d_optimize_1266 MT.C_Unit_34 funType (unsafeCoerce irExpr)
          in Right (funType, optimized)

-- | Compile a function body from MAlonzo IR to C expression text.
-- Handles the top-level curry unwrapping: the Agda elaborator produces
-- curry(body) : Unit → (A ⇒ B) for every function, but C functions receive
-- the argument directly. We unwrap the curry and compile the body with
-- a pair expression (OncePair){ .fst = NULL, .snd = x } representing (Unit, arg).
compileFuncBody :: MT.T_Type_32 -> MIR.T_IR_10 -> Text
compileFuncBody mType mIR = case mIR of
  MIR.C_curry_78 body _alloc -> case mType of
    MT.C__'8658''91'_'93'__42 inTy _q outTy ->
      let pairTy = MT.C__'42'__38 MT.C_Unit_34 inTy
          sndExpr = if isStructCType inTy then "(void*)&x" else "x"
          pairVar = "(OncePair){ .fst = ((void*)0), .snd = " <> sndExpr <> " }"
      in MCG.d_compile'45'c'45'expr_12 pairTy outTy body pairVar
    MT.C_Eff_44 inTy outTy ->
      let pairTy = MT.C__'42'__38 MT.C_Unit_34 inTy
          sndExpr = if isStructCType inTy then "(void*)&x" else "x"
          pairVar = "(OncePair){ .fst = ((void*)0), .snd = " <> sndExpr <> " }"
      in MCG.d_compile'45'c'45'expr_12 pairTy outTy body pairVar
    _ -> MCG.d_compile'45'c'45'expr_12 MT.C_Unit_34 mType mIR "x"
  _ -> MCG.d_compile'45'c'45'expr_12 MT.C_Unit_34 mType mIR "x"

-- | Check if a MAlonzo type maps to a C struct (passed by value, needs &x for void* storage)
isStructCType :: MT.T_Type_32 -> Bool
isStructCType (MT.C__'42'__38 _ _) = True   -- OncePair
isStructCType (MT.C__'43'__40 _ _) = True   -- OnceSum
isStructCType _ = False

-- | Generate C code for an executable with multiple functions
-- Uses Agda-extracted C codegen (MAlonzo) for function bodies.
-- Functions are reordered so main comes last (helpers first to avoid implicit declarations)
generateExecutableAll :: [(Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10)]
                      -> Maybe AllocStrategy
                      -> [(Text, Type)]
                      -> Text
                      -> Text
generateExecutableAll functions _defaultAlloc primitives interpCode = T.unlines
  [ "/* Generated by Once compiler */"
  , ""
  , "/* Type definitions */"
  , typeDefinitions
  , ""
  , "/* Interpretation code */"
  , interpCode
  , ""
  , "/* Primitive declarations (fallback) */"
  , primDecls
  , ""
  , "/* Once functions */"
  -- Generate helpers first, main last (to avoid implicit declarations)
  , T.unlines (map generateFunc orderedFunctions)
  , ""
  , "/* Main entry point */"
  , "int main(void) {"
  , "    once_main(((void*)0));"
  , "}"
  ]
  where
    -- Separate main from helpers, put main last
    (mainFuncs, helpers) = partition (\(n, _, _, _, _) -> n == "main") functions
    orderedFunctions = helpers ++ mainFuncs
    partition p xs = (filter p xs, filter (not . p) xs)

    -- Always emit all type definitions with include guard to avoid conflicts with interpretation files
    typeDefinitions = T.unlines
      [ "#include <stddef.h>"
      , ""
      , "#ifndef ONCE_TYPES_DEFINED"
      , "#define ONCE_TYPES_DEFINED"
      , "typedef struct { const char* data; size_t len; } OnceString;"
      , "typedef struct { void* data; size_t len; } OnceBuffer;"
      , "typedef struct { void* fst; void* snd; } OncePair;"
      , "typedef struct { int tag; void* value; } OnceSum;"
      , "#endif"
      ]

    generateFunc :: (Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10) -> Text
    generateFunc (n, t, _, mType, mIR) =
      let cBody = compileFuncBody mType mIR
      in case t of
        TArrow _ _ -> T.unlines
          [ mFuncDecl n mType <> " {"
          , "    return " <> cBody <> ";"
          , "}"
          ]
        TEff _ _ -> T.unlines
          [ mFuncDecl n mType <> " {"
          , "    return " <> cBody <> ";"
          , "}"
          ]
        -- Lift non-function types: generate void* -> void* function
        _ -> T.unlines
          [ "void* once_" <> n <> "(void* x) {"
          , "    (void)x;"
          , "    return " <> cBody <> ";"
          , "}"
          ]

    -- Function declaration from MAlonzo type
    mFuncDecl :: Text -> MT.T_Type_32 -> Text
    mFuncDecl n t = case t of
      MT.C__'8658''91'_'93'__42 inTy _q outTy ->
        MCE.d_cTypeName_62 outTy <> " once_" <> n <> "(" <> MCE.d_cTypeName_62 inTy <> " x)"
      MT.C_Eff_44 inTy outTy ->
        MCE.d_cTypeName_62 outTy <> " once_" <> n <> "(" <> MCE.d_cTypeName_62 inTy <> " x)"
      _ -> "void* once_" <> n <> "(void* x)"

    primDecls = T.unlines $ map primDecl primitives

    primDecl :: (Text, Type) -> Text
    primDecl (pname, pty) = case pty of
      TArrow inTy outTy ->
        "extern " <> cTypeName outTy <> " once_" <> pname <> "(" <> cTypeName inTy <> " x);"
      TEff inTy outTy ->
        "extern " <> cTypeName outTy <> " once_" <> pname <> "(" <> cTypeName inTy <> " x);"
      _ -> "/* primitive " <> pname <> " has non-function type */"

    cTypeName :: Type -> Text
    cTypeName t = case t of
      TVar _ -> "void*"
      TUnit -> "void*"
      TVoid -> "void"
      TInt -> "int"
      TFloat -> "double"
      TBuffer -> "OnceBuffer"
      TString _ -> "OnceString"
      TProduct _ _ -> "OncePair"
      TSum _ _ -> "OnceSum"
      TArrow _ _ -> "void*"
      TEff _ _ -> "void*"
      TApp _ _ -> "void*"
      TFix _ -> "void*"

-- | Generate library header and source for multiple functions (no main required)
-- Uses Agda-extracted C codegen (MAlonzo) for function bodies.
generateLibraryAll :: [(Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10)] -> (Text, Text)
generateLibraryAll functions = (header, source)
  where
    header = T.unlines $
      [ "/* Generated by Once compiler */"
      , "#pragma once"
      , "#include <stddef.h>"
      , ""
      , "/* Type definitions */"
      , "#ifndef ONCE_TYPES_DEFINED"
      , "#define ONCE_TYPES_DEFINED"
      , "typedef struct { const char* data; size_t len; } OnceString;"
      , "typedef struct { void* data; size_t len; } OnceBuffer;"
      , "typedef struct { void* fst; void* snd; } OncePair;"
      , "typedef struct { int tag; void* value; } OnceSum;"
      , "#endif"
      , ""
      , "/* Function declarations */"
      ] ++ map funcDecl functions

    source = T.unlines $
      [ "/* Generated by Once compiler */"
      , "#include <stddef.h>"
      , ""
      , "/* Type definitions */"
      , "#ifndef ONCE_TYPES_DEFINED"
      , "#define ONCE_TYPES_DEFINED"
      , "typedef struct { const char* data; size_t len; } OnceString;"
      , "typedef struct { void* data; size_t len; } OnceBuffer;"
      , "typedef struct { void* fst; void* snd; } OncePair;"
      , "typedef struct { int tag; void* value; } OnceSum;"
      , "#endif"
      , ""
      , "/* Function definitions */"
      ] ++ map funcDef functions

    funcDecl :: (Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10) -> Text
    funcDecl (name, _, _, mType, _) = mFuncDecl name mType <> ";"

    funcDef :: (Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10) -> Text
    funcDef (name, ty, _, mType, mIR) =
      let cBody = compileFuncBody mType mIR
      in case ty of
        TArrow _ _ ->
          mFuncDecl name mType <> " {\n" <>
          "    return " <> cBody <> ";\n" <>
          "}"
        TEff _ _ ->
          mFuncDecl name mType <> " {\n" <>
          "    return " <> cBody <> ";\n" <>
          "}"
        -- Lift non-function types: generate void* -> void* function
        _ -> "void* once_" <> name <> "(void* x) {\n" <>
          "    (void)x;\n" <>
          "    return " <> cBody <> ";\n" <>
          "}"

    -- Function declaration from MAlonzo type
    mFuncDecl :: Text -> MT.T_Type_32 -> Text
    mFuncDecl n t = case t of
      MT.C__'8658''91'_'93'__42 inTy _q outTy ->
        MCE.d_cTypeName_62 outTy <> " once_" <> n <> "(" <> MCE.d_cTypeName_62 inTy <> " x)"
      MT.C_Eff_44 inTy outTy ->
        MCE.d_cTypeName_62 outTy <> " once_" <> n <> "(" <> MCE.d_cTypeName_62 inTy <> " x)"
      _ -> "void* once_" <> n <> "(void* x)"

------------------------------------------------------------------------
-- Assembly generation for native targets
-- Uses MAlonzo-extracted verified backends
------------------------------------------------------------------------

-- | Generate assembly source for all functions using verified backends
generateAssemblyAll :: Target
                    -> [(Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10)]
                    -> Text
generateAssemblyAll target functions = T.unlines $ map (generateAssemblyFunc target) functions

-- | Generate assembly for a single function
generateAssemblyFunc :: Target -> (Text, Type, Maybe AllocStrategy, MT.T_Type_32, MIR.T_IR_10) -> Text
generateAssemblyFunc target (name, _, _, mType, mIR) =
  let (inTy, outTy) = extractTypes mType
      asmBody = case target of
        TargetX86_64  -> MEmit.d_compileX86ToText_24 inTy outTy mIR
        TargetArm64   -> MEmit.d_compileAArch64ToText_16 inTy outTy mIR
        TargetRiscV64 -> "/* RISC-V backend disabled - IR/IRS type mismatch */"
        TargetC       -> "/* C backend not assembly */"
  in T.unlines
    [ "/* Function: " <> name <> " */"
    , ".globl once_" <> name
    , "once_" <> name <> ":"
    , asmBody
    ]

-- | Extract domain and codomain types from MAlonzo function type
extractTypes :: MT.T_Type_32 -> (MT.T_Type_32, MT.T_Type_32)
extractTypes (MT.C__'8658''91'_'93'__42 inTy _q outTy) = (inTy, outTy)
extractTypes (MT.C_Eff_44 inTy outTy) = (inTy, outTy)
extractTypes _ = (MT.C_Unit_34, MT.C_Unit_34)  -- Fallback for non-function types

------------------------------------------------------------------------
-- Assembler/linker invocation (IO layer for native targets)
-- The pure specification (Target, directives, wrapping) is in
-- formal/Once/Backend/Assembler.agda
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
