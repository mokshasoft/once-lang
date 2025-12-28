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
import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (listDirectory, doesDirectoryExist, removeFile, doesFileExist)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeBaseName, takeDirectory, (</>))

import Once.Backend.C (generateC, CModule (..))
import Once.Arith.Recognize (isArithPrim)
import Once.Arith.CodeGen.C (arithToC)
import Once.Backend.CCompiler as CC
import Once.Backend.Native
  ( compileToAArch64, compileToX86, compileToRiscV64
  , compileFullToAArch64, compileFullToX86, compileFullToRiscV64
  , containsPrimitives, collectPrimitives
  )
import qualified Once.Backend.Assembler as Asm
import Once.Elaborate (elaborate, elaborateWithEnv)
import qualified Once.IR (IR (..))
import Once.Module (ModuleEnv (..), emptyModuleEnv, resolveImports, formatModuleError, LoadedModule (..))
import Once.Optimize (optimize, optimizeWith, OptimizerBackend (..))
import Once.Parser (parseModule)
import Once.Syntax (Module (..), Decl (..), Expr, AllocStrategy (..))
import Once.Type (Type (..))
import Once.TypeCheck (checkModule, checkModuleWithEnv, convertType)

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
  = TargetC       -- ^ C backend (current, default)
  | TargetX86_64  -- ^ x86-64 assembly (future)
  | TargetArm64   -- ^ ARM64 assembly (future)
  | TargetRiscV64 -- ^ RISC-V 64-bit (future)
  deriving (Eq, Show)

-- | File extension for each target
targetExtension :: Target -> String
targetExtension TargetC = ".c"
targetExtension TargetX86_64 = ".x86_64"
targetExtension TargetArm64 = ".arm64"
targetExtension TargetRiscV64 = ".riscv64"

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
  , buildOptimizer :: OptimizerBackend  -- ^ Which optimizer to use (default: HaskellOptimizer)
  , buildSaveTemps :: Bool              -- ^ Keep intermediate files (.c, .s, .o)
  , buildExplicitInterps :: [(InterpType, String)]  -- ^ Explicit interpretations: -I:TYPE MODULE
  , buildAutoResolve :: Maybe [InterpType]          -- ^ Auto-resolve priority: -A:TYPE:TYPE:...
  , buildArith :: Bool                  -- ^ Enable arithmetic compiler for pure numeric expressions
  } deriving (Eq, Show)

-- | Options for the check command
data CheckOptions = CheckOptions
  { checkInput :: FilePath
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

  -- Parse
  case parseModule source of
    Left err -> do
      TIO.putStrLn $ "Parse error: " <> T.pack (show err)
      exitFailure
    Right m -> do
      -- Resolve imports (load all imported modules)
      let initialEnv = emptyModuleEnv strataPath targetExt
      resolveResult <- resolveImports initialEnv (moduleImports m)
      case resolveResult of
        Left modErr -> do
          TIO.putStrLn $ "Module error: " <> formatModuleError modErr
          exitFailure
        Right modEnv -> do
          -- Type check with module environment
          case checkModuleWithEnv modEnv m of
            Left err -> do
              TIO.putStrLn $ "Type error: " <> T.pack (show err)
              exitFailure
            Right () -> do
              -- Extract primitives and all function definitions
              let primitives = extractPrimitives m
                  allFunctions = extractFunctions m

              -- Generate C based on mode
              case mode of
                Library -> do
                  -- Library mode: generate code for all functions (no main required)
                  case allFunctions of
                    [] -> do
                      TIO.putStrLn "Error: No functions found"
                      exitFailure
                    _ -> do
                      -- Elaborate all functions
                      case elaborateAllWithEnv modEnv allFunctions of
                        Left err -> do
                          TIO.putStrLn $ "Elaboration error: " <> T.pack (show err)
                          exitFailure
                        Right irFunctions -> do
                          -- Optimize and generate for each function
                          let opt = optimizeWith (buildOptimizer opts)
                          let optimizedFunctions = [(n, t, a, opt ir) | (n, t, a, ir) <- irFunctions]

                          -- Branch based on target
                          case target of
                            TargetC -> do
                              -- Generate library with all functions (C backend)
                              let (header, source') = generateLibraryAll optimizedFunctions
                                  headerPath = outputBase ++ ".h"
                                  sourcePath = outputBase ++ ".c"
                              TIO.writeFile headerPath header
                              TIO.writeFile sourcePath source'
                              TIO.putStrLn $ "Generated: " <> T.pack headerPath <> ", " <> T.pack sourcePath
                              exitSuccess

                            nativeTarget -> do
                              -- Native targets: generate assembly for ALL functions
                              -- Check if any function has primitives (affects codegen choice)
                              let hasPrimitives = any (\(_, _, _, ir') -> containsPrimitives ir') optimizedFunctions

                              -- Generate assembly for each function
                              let generateFuncAsm' :: (Text, Type, Maybe AllocStrategy, Once.IR.IR) -> (Text, Text)
                                  generateFuncAsm' (name', _, _, ir') =
                                    let code = if hasPrimitives || containsPrimitives ir'
                                          then case nativeTarget of
                                            TargetArm64 -> compileFullToAArch64 ir'
                                            TargetX86_64 -> compileFullToX86 ir'
                                            TargetRiscV64 -> compileFullToRiscV64 ir'
                                            TargetC -> error "unreachable"
                                          else case (case nativeTarget of
                                                 TargetArm64 -> compileToAArch64 ir'
                                                 TargetX86_64 -> compileToX86 ir'
                                                 TargetRiscV64 -> compileToRiscV64 ir'
                                                 TargetC -> error "unreachable") of
                                            Just c -> c
                                            Nothing -> case nativeTarget of
                                              TargetArm64 -> compileFullToAArch64 ir'
                                              TargetX86_64 -> compileFullToX86 ir'
                                              TargetRiscV64 -> compileFullToRiscV64 ir'
                                              TargetC -> error "unreachable"
                                    in (name', code)

                              let allFuncAsm = map generateFuncAsm' optimizedFunctions

                              -- Load interpretation files for native target
                              -- Convert target to InterpType for file extension
                              let targetInterpType = case nativeTarget of
                                    TargetArm64 -> InterpArm64
                                    TargetX86_64 -> InterpX86_64
                                    TargetRiscV64 -> InterpRiscV64
                                    TargetC -> error "unreachable"
                              -- Filter explicit interps to only those matching target
                              let targetInterps = [(t, m) | (t, m) <- buildExplicitInterps opts, t == targetInterpType]
                              let interpFiles = resolveExplicitInterps strataPath targetInterps
                              interpCode <- T.concat <$> mapM TIO.readFile interpFiles

                              -- Wrap all functions for library export with interpretation code
                              let wrappedAsm = interpCode <> "\n" <> wrapNativeLibAll nativeTarget allFuncAsm
                              let asmPath = outputBase ++ ".s"
                              TIO.writeFile asmPath wrappedAsm
                              TIO.putStrLn $ "Generated: " <> T.pack asmPath
                              exitSuccess

                Executable -> do
                  -- Executable mode: requires main
                  case filter (\(n, _, _, _) -> n == "main") allFunctions of
                    [] -> do
                      TIO.putStrLn "Error: No main function found"
                      exitFailure
                    ((mainName, mainTy, mainAlloc, mainExpr):_) -> do
                      -- D032: main must be effectful (Eff Unit Unit or IO Unit)
                      case mainTy of
                        TEff TUnit TUnit -> pure ()  -- OK: Eff Unit Unit or IO Unit
                        _ -> do
                          TIO.putStrLn $ "Error: main must have type 'Eff Unit Unit' or 'IO Unit', got: " <> T.pack (show mainTy)
                          TIO.putStrLn "Hint: Use 'main : IO Unit' or 'main : Eff Unit Unit'"
                          exitFailure

                      -- Elaborate all functions to IR (with module environment)
                      let otherFunctions = filter (\(n, _, _, _) -> n /= "main") allFunctions
                      case elaborateAllWithEnv modEnv ((mainName, mainTy, mainAlloc, mainExpr) : otherFunctions) of
                        Left err -> do
                          TIO.putStrLn $ "Elaboration error: " <> T.pack (show err)
                          exitFailure
                        Right irFunctions -> do
                          -- Optimize all IRs
                          let opt = optimizeWith (buildOptimizer opts)
                          let optimizedFunctions = [(n, t, a, opt ir) | (n, t, a, ir) <- irFunctions]

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
                                  alloc = mainAlloc <|> buildAlloc opts
                                  interpCode = interpCodeLegacy <> "\n" <> importedCode <> "\n" <> explicitCode
                                  source' = generateExecutableAll optimizedFunctions alloc primitives interpCode (buildArith opts)
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
                              -- Native targets: generate code for ALL functions
                              -- Check if any function has primitives (affects codegen choice)
                              let hasPrimitives = any (\(_, _, _, ir) -> containsPrimitives ir) optimizedFunctions

                              -- Generate assembly for each function
                              let generateFuncAsm :: (Text, Type, Maybe AllocStrategy, Once.IR.IR) -> (Text, Text)
                                  generateFuncAsm (name, _, _, ir) =
                                    let code = if hasPrimitives || containsPrimitives ir
                                          then case nativeTarget of
                                            TargetArm64 -> compileFullToAArch64 ir
                                            TargetX86_64 -> compileFullToX86 ir
                                            TargetRiscV64 -> compileFullToRiscV64 ir
                                            TargetC -> error "unreachable"
                                          else case (case nativeTarget of
                                                 TargetArm64 -> compileToAArch64 ir
                                                 TargetX86_64 -> compileToX86 ir
                                                 TargetRiscV64 -> compileToRiscV64 ir
                                                 TargetC -> error "unreachable") of
                                            Just c -> c
                                            Nothing -> case nativeTarget of
                                              TargetArm64 -> compileFullToAArch64 ir
                                              TargetX86_64 -> compileFullToX86 ir
                                              TargetRiscV64 -> compileFullToRiscV64 ir
                                              TargetC -> error "unreachable"
                                    in (name, code)

                              let allFuncAsm = map generateFuncAsm optimizedFunctions

                              -- Wrap all functions with _start entry point
                              let wrappedAsm = wrapNativeExeAll nativeTarget allFuncAsm
                              let asmPath = outputBase ++ ".s"
                                  objPath = outputBase ++ ".o"
                              TIO.writeFile asmPath wrappedAsm

                              -- Assemble main .s -> .o
                              asmResult' <- Asm.assemble asmPath objPath
                              case asmResult' of
                                Left err -> do
                                  TIO.putStrLn $ "Assembly failed: " <> T.pack (show err)
                                  exitFailure
                                Right _ -> do
                                  -- Collect interpretation files to link if we have primitives
                                  interpObjFiles <- if hasPrimitives
                                    then do
                                      -- Collect interpretation assembly files from:
                                      -- 1. Explicit -I:TYPE flags matching this target
                                      let explicitFiles = resolveExplicitNativeInterps strataPath nativeTarget (buildExplicitInterps opts)
                                      -- 2. Module env (from imports)
                                      let moduleFiles = collectNativeInterpFiles strataPath nativeTarget modEnv
                                      let interpAsmFiles = explicitFiles ++ moduleFiles
                                      -- Assemble each interpretation file
                                      assembleInterpFiles nativeTarget interpAsmFiles outputBase
                                    else pure []

                                  -- Link all .o files -> executable
                                  let allObjFiles = objPath : interpObjFiles
                                  linkResult <- Asm.link allObjFiles outputBase
                                  case linkResult of
                                    Left err -> do
                                      TIO.putStrLn $ "Linking failed: " <> T.pack (show err)
                                      exitFailure
                                    Right exePath -> do
                                      -- Clean up unless --save-temps
                                      if buildSaveTemps opts
                                        then TIO.putStrLn $ "Generated: " <> T.pack asmPath <> ", " <> T.pack objPath <> ", " <> T.pack exePath
                                        else do
                                          removeFile asmPath
                                          removeFile objPath
                                          mapM_ removeFile interpObjFiles
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

  -- Read input file
  source <- TIO.readFile inputPath

  -- Parse
  case parseModule source of
    Left err -> do
      TIO.putStrLn $ "Parse error: " <> T.pack (show err)
      exitFailure
    Right m -> do
      -- Type check
      case checkModule m of
        Left err -> do
          TIO.putStrLn $ "Type error: " <> T.pack (show err)
          exitFailure
        Right () -> do
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

-- | Extract all primitives from a module
-- Returns list of (name, type)
extractPrimitives :: Module -> [(Text, Type)]
extractPrimitives (Module _imports decls) =
  [ (name, convertType sty) | Primitive name sty <- decls ]

-- | Extract all function definitions from a module
-- Returns list of (name, type, allocation, expression)
extractFunctions :: Module -> [(Text, Type, Maybe AllocStrategy, Expr)]
extractFunctions (Module _imports decls) = go decls Nothing
  where
    go [] _ = []
    go (TypeSig name sty : FunDef name' alloc expr : rest) _
      | name == name' = (name, convertType sty, alloc, expr) : go rest Nothing
      | otherwise = go rest Nothing
    go (TypeSig name sty : rest) _ = go rest (Just (name, sty))
    go (_ : rest) ctx = go rest ctx

-- | Extract the main function from a module (backwards compatible)
-- Returns (name, type, allocation, expression)
extractFunction :: Module -> Maybe (Text, Type, Maybe AllocStrategy, Expr)
extractFunction m = case filter (\(n, _, _, _) -> n == "main") (extractFunctions m) of
  [] -> Nothing
  (f:_) -> Just f

-- | Wrap assembly code with proper directives for a given target (library mode)
wrapNativeAsm :: Target -> Text -> Text -> Text
wrapNativeAsm target name body = case target of
  TargetArm64 -> T.unlines
    [ "// Generated by Once (verified via MAlonzo)"
    , ".text"
    , ".globl once_" <> name
    , ".type once_" <> name <> ", %function"
    , "once_" <> name <> ":"
    , body
    , "    ret"
    , ".size once_" <> name <> ", .-once_" <> name
    ]
  TargetX86_64 -> T.unlines
    [ "# Generated by Once (verified via MAlonzo)"
    , ".text"
    , ".globl once_" <> name
    , ".type once_" <> name <> ", @function"
    , "once_" <> name <> ":"
    , body
    , "    retq"
    , ".size once_" <> name <> ", .-once_" <> name
    ]
  TargetRiscV64 -> T.unlines
    [ "# Generated by Once (verified via MAlonzo)"
    , ".text"
    , ".globl once_" <> name
    , ".type once_" <> name <> ", @function"
    , "once_" <> name <> ":"
    , body
    , "    ret"
    , ".size once_" <> name <> ", .-once_" <> name
    ]
  TargetC -> error "wrapNativeAsm: TargetC is not a native target"

-- | Wrap assembly code for executable mode (with _start and exit syscall)
wrapNativeExe :: Target -> Text -> Text -> Text
wrapNativeExe target name body = case target of
  TargetArm64 -> T.unlines
    [ "// Generated by Once (verified via MAlonzo)"
    , ".text"
    , ""
    , "// Once function"
    , ".globl once_" <> name
    , ".type once_" <> name <> ", %function"
    , "once_" <> name <> ":"
    , body
    , "    ret"
    , ".size once_" <> name <> ", .-once_" <> name
    , ""
    , "// Entry point"
    , ".globl _start"
    , ".type _start, %function"
    , "_start:"
    , "    mov x0, #0"            -- arg = NULL (Unit)
    , "    bl once_" <> name
    , "    mov x8, #93"           -- syscall: exit
    , "    mov x0, #0"            -- status = 0
    , "    svc #0"
    , ".size _start, .-_start"
    ]
  TargetX86_64 -> T.unlines
    [ "# Generated by Once (verified via MAlonzo)"
    , ".text"
    , ""
    , "# Once function"
    , ".globl once_" <> name
    , ".type once_" <> name <> ", @function"
    , "once_" <> name <> ":"
    , body
    , "    retq"
    , ".size once_" <> name <> ", .-once_" <> name
    , ""
    , "# Entry point"
    , ".globl _start"
    , ".type _start, @function"
    , "_start:"
    , "    xorq %rdi, %rdi"       -- arg = NULL (Unit)
    , "    call once_" <> name
    , "    movq $60, %rax"        -- syscall: exit
    , "    xorq %rdi, %rdi"       -- status = 0
    , "    syscall"
    , ".size _start, .-_start"
    ]
  TargetRiscV64 -> T.unlines
    [ "# Generated by Once (verified via MAlonzo)"
    , ".text"
    , ""
    , "# Once function"
    , ".globl once_" <> name
    , ".type once_" <> name <> ", @function"
    , "once_" <> name <> ":"
    , body
    , "    ret"
    , ".size once_" <> name <> ", .-once_" <> name
    , ""
    , "# Entry point"
    , ".globl _start"
    , ".type _start, @function"
    , "_start:"
    , "    li a0, 0"              -- arg = NULL (Unit)
    , "    call once_" <> name
    , "    li a7, 93"             -- syscall: exit
    , "    li a0, 0"              -- status = 0
    , "    ecall"
    , ".size _start, .-_start"
    ]
  TargetC -> error "wrapNativeExe: TargetC is not a native target"

-- | Generate a single function definition for native target (no header/entry point)
nativeFuncDef :: Target -> Text -> Text -> Text
nativeFuncDef target name body = case target of
  TargetArm64 -> T.unlines
    [ ".globl once_" <> name
    , ".type once_" <> name <> ", %function"
    , "once_" <> name <> ":"
    , body
    , "    ret"
    , ".size once_" <> name <> ", .-once_" <> name
    ]
  TargetX86_64 -> T.unlines
    [ ".globl once_" <> name
    , ".type once_" <> name <> ", @function"
    , "once_" <> name <> ":"
    , body
    , "    retq"
    , ".size once_" <> name <> ", .-once_" <> name
    ]
  TargetRiscV64 -> T.unlines
    [ ".globl once_" <> name
    , ".type once_" <> name <> ", @function"
    , "once_" <> name <> ":"
    , body
    , "    ret"
    , ".size once_" <> name <> ", .-once_" <> name
    ]
  TargetC -> error "nativeFuncDef: TargetC is not a native target"

-- | Wrap multiple function definitions with header and _start entry point
wrapNativeExeAll :: Target -> [(Text, Text)] -> Text
wrapNativeExeAll target funcs = case target of
  TargetArm64 -> T.unlines $
    [ "// Generated by Once compiler"
    , ".text"
    , ""
    ] ++
    [ nativeFuncDef target name body | (name, body) <- funcs ] ++
    [ ""
    , "// Entry point"
    , ".globl _start"
    , ".type _start, %function"
    , "_start:"
    , "    mov x0, #0"
    , "    bl once_main"
    , "    mov x8, #93"
    , "    mov x0, #0"
    , "    svc #0"
    , ".size _start, .-_start"
    ]
  TargetX86_64 -> T.unlines $
    [ "# Generated by Once compiler"
    , ".text"
    , ""
    ] ++
    [ nativeFuncDef target name body | (name, body) <- funcs ] ++
    [ ""
    , "# Entry point"
    , ".globl _start"
    , ".type _start, @function"
    , "_start:"
    , "    xorq %rdi, %rdi"
    , "    call once_main"
    , "    movq $60, %rax"
    , "    xorq %rdi, %rdi"
    , "    syscall"
    , ".size _start, .-_start"
    ]
  TargetRiscV64 -> T.unlines $
    [ "# Generated by Once compiler"
    , ".text"
    , ""
    ] ++
    [ nativeFuncDef target name body | (name, body) <- funcs ] ++
    [ ""
    , "# Entry point"
    , ".globl _start"
    , ".type _start, @function"
    , "_start:"
    , "    li a0, 0"
    , "    call once_main"
    , "    li a7, 93"
    , "    li a0, 0"
    , "    ecall"
    , ".size _start, .-_start"
    ]
  TargetC -> error "wrapNativeExeAll: TargetC is not a native target"

-- | Wrap multiple functions for native library (no _start, just exported functions)
wrapNativeLibAll :: Target -> [(Text, Text)] -> Text
wrapNativeLibAll target funcs = case target of
  TargetArm64 -> T.unlines $
    [ "// Generated by Once compiler"
    , ".text"
    , ""
    ] ++
    [ nativeFuncDef target name body | (name, body) <- funcs ]
  TargetX86_64 -> T.unlines $
    [ "# Generated by Once compiler"
    , ".text"
    , ""
    ] ++
    [ nativeFuncDef target name body | (name, body) <- funcs ]
  TargetRiscV64 -> T.unlines $
    [ "# Generated by Once compiler"
    , ".text"
    , ""
    ] ++
    [ nativeFuncDef target name body | (name, body) <- funcs ]
  TargetC -> error "wrapNativeLibAll: TargetC is not a native target"

-- | Elaborate all functions, returning elaborated IR or first error
elaborateAll :: [(Text, Type, Maybe AllocStrategy, Expr)]
             -> Either String [(Text, Type, Maybe AllocStrategy, Once.IR.IR)]
elaborateAll [] = Right []
elaborateAll ((name, ty, alloc, expr):rest) =
  case elaborate expr of
    Left err -> Left (show err)
    Right ir -> case elaborateAll rest of
      Left err -> Left err
      Right irs -> Right ((name, ty, alloc, ir) : irs)

-- | Elaborate all functions with module environment
elaborateAllWithEnv :: ModuleEnv
                    -> [(Text, Type, Maybe AllocStrategy, Expr)]
                    -> Either String [(Text, Type, Maybe AllocStrategy, Once.IR.IR)]
elaborateAllWithEnv _ [] = Right []
elaborateAllWithEnv env ((name, ty, alloc, expr):rest) =
  case elaborateWithEnv env expr of
    Left err -> Left (show err)
    Right ir -> case elaborateAllWithEnv env rest of
      Left err -> Left err
      Right irs -> Right ((name, ty, alloc, ir) : irs)

-- | Generate C code for an executable (with main function)
-- The allocation strategy affects how buffer/string outputs are allocated
generateExecutable :: Text -> Type -> Once.IR.IR -> Maybe AllocStrategy -> [(Text, Type)] -> Text -> Text
generateExecutable name ty ir alloc primitives interpCode = T.unlines
  [ "/* Generated by Once compiler */"
  , ""
  , "/* Interpretation code */"
  , interpCode
  , ""
  , "/* Primitive declarations (fallback) */"
  , primDecls
  , ""
  , "/* Once function */"
  , onceFuncCode name ty ir
  , ""
  , "/* Main entry point */"
  , "int main(void) {"
  , "    once_" <> name <> "(((void*)0));"
  , "}"
  ]
  where
    -- Generate Once function without include
    onceFuncCode :: Text -> Type -> Once.IR.IR -> Text
    onceFuncCode n t i = T.unlines
      [ funcDecl n t <> " {"
      , "    return " <> generateIRExpr i "x" <> ";"
      , "}"
      ]

    funcDecl :: Text -> Type -> Text
    funcDecl n t = case t of
      TArrow inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " x)"
      TEff inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " x)"  -- D032
      _ -> "void* once_" <> n <> "(void)"

    generateIRExpr :: Once.IR.IR -> Text -> Text
    generateIRExpr i v = case i of
      Once.IR.Id _ -> v
      -- When accessing nested pairs, intermediate .fst/.snd returns void*
      -- which needs to be cast to OncePair* before accessing its members
      Once.IR.Fst _ _ ->
        if needsPairCast v
          then "((OncePair*)" <> v <> ")->fst"
          else v <> ".fst"
      Once.IR.Snd _ _ ->
        if needsPairCast v
          then "((OncePair*)" <> v <> ")->snd"
          else v <> ".snd"
      Once.IR.Pair f g -> "(OncePair){ .fst = " <> generateIRExpr f v <> ", .snd = " <> generateIRExpr g v <> " }"
      Once.IR.Compose g f -> generateIRExpr g (generateIRExpr f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      Once.IR.Case l r -> "(" <> v <> ".tag == 0 ? " <> generateIRExpr l (v <> ".value") <> " : " <> generateIRExpr r (v <> ".value") <> ")"
      Once.IR.Initial _ -> v
      Once.IR.Curry paramName body ->
        "({ typeof(" <> v <> ") " <> paramName <> " = " <> v <> "; " <>
        generateIRExpr body paramName <> "; })"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'  -- Local variable: just use the name
      Once.IR.FunRef n' -> "(void*)once_" <> n'  -- Function reference (pointer, not call)
      Once.IR.Prim n' _ _ ->
        -- Inline integer primitives like __int_42
        case T.stripPrefix "__int_" n' of
          Just numStr -> "(void*)" <> numStr
          Nothing -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.StringLit s -> generateStringLit s
      -- Recursive type operations (identity at runtime)
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      -- Let binding: use GCC statement expression ({ ... })
      -- let x = e1 in e2 => ({ typeof(e1) x = e1; e2; })
      -- Using GCC typeof extension to infer the type automatically
      Once.IR.Let x' e1 e2 ->
        let e1Code = generateIRExpr e1 v
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> generateIRExpr e2 x' <> "; })"
      -- Arithmetic expression (OCP-0001)
      Once.IR.Arith arithExpr -> arithToC arithExpr

    -- Check if a variable expression needs to be cast to OncePair* before accessing .fst/.snd
    -- This happens when the expression is the result of a previous pair access:
    -- - ".fst" or ".snd" suffix (first level access like _tuple.fst)
    -- - ")->fst" or ")->snd" suffix (deeper level access like ((OncePair*)x)->fst)
    needsPairCast :: Text -> Bool
    needsPairCast v' =
      ".fst" `T.isSuffixOf` v' || ".snd" `T.isSuffixOf` v' ||
      ")->fst" `T.isSuffixOf` v' || ")->snd" `T.isSuffixOf` v'

    -- Generate string literal based on allocation strategy
    generateStringLit :: Text -> Text
    generateStringLit s =
      let escaped = escapeString s
          len = T.pack (show (T.length s))
      in case alloc of
        -- Default (Nothing) or const: static string in .rodata
        Nothing -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocConst -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        -- Stack: compound literal (auto storage duration)
        Just AllocStack -> "(OnceString){ .data = (char[]){\"" <> escaped <> "\"}, .len = " <> len <> " }"
        -- Heap: use MallocLike heap_string from interpretation layer
        Just AllocHeap -> "once_heap_string(" <> len <> ", (OnceBuffer){ .data = \"" <> escaped <> "\", .len = " <> len <> " })"
        -- Pool/Arena: fallback to static for now (TODO: implement via interpretation layer)
        Just AllocPool -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocArena -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"

    escapeString :: Text -> Text
    escapeString = T.concatMap escapeChar
      where
        escapeChar c = case c of
          '\n' -> "\\n"
          '\t' -> "\\t"
          '\r' -> "\\r"
          '\\' -> "\\\\"
          '"'  -> "\\\""
          _    -> T.singleton c

    -- Generate primitive declarations/implementations
    primDecls = T.unlines $ map primDecl primitives

    primDecl :: (Text, Type) -> Text
    primDecl (pname, pty) = case pty of
      TArrow inTy outTy ->
        -- Declare primitives as extern (interpretation provides them)
        -- Use once_ prefix to avoid conflicts with stdlib
        "extern " <> cTypeName outTy <> " once_" <> pname <> "(" <> cTypeName inTy <> " x);"
      TEff inTy outTy ->  -- D032: Effectful primitives
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
      TEff _ _ -> "void*"  -- D032: Eff same as Arrow at runtime
      TApp _ _ -> "void*"
      TFix _ -> "void*"

-- | Generate C code for an executable with multiple functions
-- Functions are reordered so main comes last (helpers first to avoid implicit declarations)
generateExecutableAll :: [(Text, Type, Maybe AllocStrategy, Once.IR.IR)]
                      -> Maybe AllocStrategy
                      -> [(Text, Type)]
                      -> Text
                      -> Bool  -- ^ Enable arithmetic inlining (--arith flag)
                      -> Text
generateExecutableAll functions defaultAlloc primitives interpCode arithMode = T.unlines
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
    (mainFuncs, helpers) = partition (\(n, _, _, _) -> n == "main") functions
    orderedFunctions = helpers ++ mainFuncs
    partition p xs = (filter p xs, filter (not . p) xs)

    -- Collect all types from functions and primitives
    allTypes = map (\(_, t, _, _) -> t) functions ++ map snd primitives

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

    needsPair :: Type -> Bool
    needsPair t = case t of
      TProduct _ _ -> True
      TSum a b -> needsPair a || needsPair b
      TArrow a b -> needsPair a || needsPair b
      TEff a b -> needsPair a || needsPair b
      _ -> False

    needsSum :: Type -> Bool
    needsSum t = case t of
      TSum _ _ -> True
      TProduct a b -> needsSum a || needsSum b
      TArrow a b -> needsSum a || needsSum b
      TEff a b -> needsSum a || needsSum b
      _ -> False

    needsBuffer :: Type -> Bool
    needsBuffer t = case t of
      TBuffer -> True
      TString _ -> True
      TProduct a b -> needsBuffer a || needsBuffer b
      TSum a b -> needsBuffer a || needsBuffer b
      TArrow a b -> needsBuffer a || needsBuffer b
      TEff a b -> needsBuffer a || needsBuffer b
      _ -> False

    needsString :: Type -> Bool
    needsString t = case t of
      TString _ -> True
      TProduct a b -> needsString a || needsString b
      TSum a b -> needsString a || needsString b
      TArrow a b -> needsString a || needsString b
      TEff a b -> needsString a || needsString b
      _ -> False

    generateFunc :: (Text, Type, Maybe AllocStrategy, Once.IR.IR) -> Text
    generateFunc (n, t, funcAlloc, ir) =
      let alloc = funcAlloc <|> defaultAlloc
      in generateFuncWithAlloc n t ir alloc

    generateFuncWithAlloc :: Text -> Type -> Once.IR.IR -> Maybe AllocStrategy -> Text
    generateFuncWithAlloc n t ir alloc = case t of
      TArrow _ _ -> T.unlines
        [ funcDecl n t <> " {"
        , "    return " <> generateIRExpr alloc ir "x" <> ";"
        , "}"
        ]
      TEff _ _ -> T.unlines
        [ funcDecl n t <> " {"
        , "    return " <> generateIRExpr alloc ir "x" <> ";"
        , "}"
        ]
      -- Lift non-function types: generate Unit -> T function
      _ -> T.unlines
        [ funcDecl n t <> " {"
        , "    (void)x;"
        , "    return " <> generateIRExpr alloc ir "x" <> ";"
        , "}"
        ]

    funcDecl :: Text -> Type -> Text
    funcDecl n t = case t of
      TArrow inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " x)"
      TEff inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " x)"  -- D032
      -- Lift non-function types to Unit -> T
      _ -> "void* once_" <> n <> "(void* x)"

    generateIRExpr :: Maybe AllocStrategy -> Once.IR.IR -> Text -> Text
    generateIRExpr alloc i v = case i of
      Once.IR.Id _ -> v
      Once.IR.Fst _ _ ->
        if needsPairCast v
          then "((OncePair*)" <> v <> ")->fst"
          else v <> ".fst"
      Once.IR.Snd _ _ ->
        if needsPairCast v
          then "((OncePair*)" <> v <> ")->snd"
          else v <> ".snd"
      Once.IR.Pair f g -> "(OncePair){ .fst = " <> generateIRExpr alloc f v <> ", .snd = " <> generateIRExpr alloc g v <> " }"
      Once.IR.Compose g f -> generateIRExpr alloc g (generateIRExpr alloc f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      Once.IR.Case l r -> "(" <> v <> ".tag == 0 ? " <> generateIRExpr alloc l (v <> ".value") <> " : " <> generateIRExpr alloc r (v <> ".value") <> ")"
      Once.IR.Initial _ -> v
      Once.IR.Curry paramName body ->
        "({ typeof(" <> v <> ") " <> paramName <> " = " <> v <> "; " <>
        generateIRExpr alloc body paramName <> "; })"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' ->
        -- When --arith is enabled, try to inline arithmetic primitives
        if arithMode
          then case inlineArithPrim n' v of
            Just expr -> expr
            Nothing -> "once_" <> n' <> "(" <> v <> ")"
          else "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'
      Once.IR.FunRef n' -> "(void*)once_" <> n'  -- Function reference (pointer, not call)
      Once.IR.Prim n' _ _ ->
        -- Inline integer primitives like __int_42
        case T.stripPrefix "__int_" n' of
          Just numStr -> "(void*)" <> numStr
          Nothing ->
            -- When --arith is enabled, try to inline arithmetic primitives
            if arithMode
              then case inlineArithPrim n' v of
                Just expr -> expr
                Nothing -> "once_" <> n' <> "(" <> v <> ")"
              else "once_" <> n' <> "(" <> v <> ")"
      Once.IR.StringLit s -> generateStringLit alloc s
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      Once.IR.Let x' e1 e2 ->
        let e1Code = generateIRExpr alloc e1 v
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> generateIRExpr alloc e2 x' <> "; })"
      -- Arithmetic expression (OCP-0001)
      Once.IR.Arith arithExpr -> arithToC arithExpr

    generateStringLit :: Maybe AllocStrategy -> Text -> Text
    generateStringLit alloc s =
      let escaped = escapeString s
          len = T.pack (show (T.length s))
      in case alloc of
        Nothing -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocConst -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocStack -> "(OnceString){ .data = (char[]){\"" <> escaped <> "\"}, .len = " <> len <> " }"
        Just AllocHeap -> "once_heap_string(" <> len <> ", (OnceBuffer){ .data = \"" <> escaped <> "\", .len = " <> len <> " })"
        Just AllocPool -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocArena -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"

    escapeString :: Text -> Text
    escapeString = T.concatMap escapeChar
      where
        escapeChar c = case c of
          '\n' -> "\\n"
          '\t' -> "\\t"
          '\r' -> "\\r"
          '\\' -> "\\\\"
          '"'  -> "\\\""
          _    -> T.singleton c

    primDecls = T.unlines $ map primDecl primitives

    primDecl :: (Text, Type) -> Text
    primDecl (pname, pty) = case pty of
      TArrow inTy outTy ->
        "extern " <> cTypeName outTy <> " once_" <> pname <> "(" <> cTypeName inTy <> " x);"
      TEff inTy outTy ->  -- D032: Eff same as Arrow at runtime
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
      TEff _ _ -> "void*"  -- D032: Eff same as Arrow at runtime
      TApp _ _ -> "void*"
      TFix _ -> "void*"

    -- Check if a variable expression needs to be cast to OncePair* before accessing .fst/.snd
    needsPairCast :: Text -> Bool
    needsPairCast v' =
      ".fst" `T.isSuffixOf` v' || ".snd" `T.isSuffixOf` v' ||
      ")->fst" `T.isSuffixOf` v' || ")->snd" `T.isSuffixOf` v'

-- | Generate library header and source for multiple functions (no main required)
generateLibraryAll :: [(Text, Type, Maybe AllocStrategy, Once.IR.IR)] -> (Text, Text)
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
      ] ++ map (funcDef Nothing) functions

    funcDecl :: (Text, Type, Maybe AllocStrategy, Once.IR.IR) -> Text
    funcDecl (name, ty, _, _) = case ty of
      TArrow inTy outTy ->
        libCTypeName outTy <> " once_" <> name <> "(" <> libCTypeName inTy <> " x);"
      TEff inTy outTy ->
        libCTypeName outTy <> " once_" <> name <> "(" <> libCTypeName inTy <> " x);"
      -- Lift non-function types to Unit -> T (constants become functions)
      _ -> "void* once_" <> name <> "(void* x);"

    funcDef :: Maybe AllocStrategy -> (Text, Type, Maybe AllocStrategy, Once.IR.IR) -> Text
    funcDef globalAlloc (name, ty, localAlloc, ir) = case ty of
      TArrow inTy outTy ->
        libCTypeName outTy <> " once_" <> name <> "(" <> libCTypeName inTy <> " x) {\n" <>
        "    return " <> libGenerateIRExpr (localAlloc <|> globalAlloc) ir "x" <> ";\n" <>
        "}"
      TEff inTy outTy ->
        libCTypeName outTy <> " once_" <> name <> "(" <> libCTypeName inTy <> " x) {\n" <>
        "    return " <> libGenerateIRExpr (localAlloc <|> globalAlloc) ir "x" <> ";\n" <>
        "}"
      -- Lift non-function types: generate Unit -> T function
      _ -> "void* once_" <> name <> "(void* x) {\n" <>
        "    (void)x;\n" <>
        "    return " <> libGenerateIRExpr (localAlloc <|> globalAlloc) ir "x" <> ";\n" <>
        "}"

    libCTypeName :: Type -> Text
    libCTypeName t = case t of
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

    libGenerateIRExpr :: Maybe AllocStrategy -> Once.IR.IR -> Text -> Text
    libGenerateIRExpr alloc ir v = case ir of
      Once.IR.Id _ -> v
      Once.IR.Fst _ _ ->
        if libNeedsPairCast v
          then "((OncePair*)" <> v <> ")->fst"
          else v <> ".fst"
      Once.IR.Snd _ _ ->
        if libNeedsPairCast v
          then "((OncePair*)" <> v <> ")->snd"
          else v <> ".snd"
      Once.IR.Pair f g -> "(OncePair){ .fst = " <> libGenerateIRExpr alloc f v <> ", .snd = " <> libGenerateIRExpr alloc g v <> " }"
      Once.IR.Compose g f -> libGenerateIRExpr alloc g (libGenerateIRExpr alloc f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      Once.IR.Case l r -> "(" <> v <> ".tag == 0 ? " <> libGenerateIRExpr alloc l (v <> ".value") <> " : " <> libGenerateIRExpr alloc r (v <> ".value") <> ")"
      Once.IR.Initial _ -> v
      Once.IR.Curry paramName body ->
        "({ typeof(" <> v <> ") " <> paramName <> " = " <> v <> "; " <>
        libGenerateIRExpr alloc body paramName <> "; })"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'
      Once.IR.FunRef n' -> "(void*)once_" <> n'
      Once.IR.Prim n' _ _ ->
        -- Inline integer primitives like __int_42
        case T.stripPrefix "__int_" n' of
          Just numStr -> "(void*)" <> numStr
          Nothing -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.StringLit s -> libGenerateStringLit alloc s
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      Once.IR.Let x' e1 e2 ->
        let e1Code = libGenerateIRExpr alloc e1 v
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> libGenerateIRExpr alloc e2 x' <> "; })"
      -- Arithmetic expression (OCP-0001)
      Once.IR.Arith arithExpr -> arithToC arithExpr

    libGenerateStringLit :: Maybe AllocStrategy -> Text -> Text
    libGenerateStringLit alloc s =
      let escaped = libEscapeString s
          len = T.pack (show (T.length s))
      in case alloc of
        Nothing -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocConst -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocStack -> "(OnceString){ .data = (char[]){\"" <> escaped <> "\"}, .len = " <> len <> " }"
        Just AllocHeap -> "once_heap_string(" <> len <> ", (OnceBuffer){ .data = \"" <> escaped <> "\", .len = " <> len <> " })"
        Just AllocPool -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"
        Just AllocArena -> "(OnceString){ .data = \"" <> escaped <> "\", .len = " <> len <> " }"

    libEscapeString :: Text -> Text
    libEscapeString = T.concatMap escapeChar
      where
        escapeChar c = case c of
          '\n' -> "\\n"
          '\t' -> "\\t"
          '\r' -> "\\r"
          '\\' -> "\\\\"
          '"'  -> "\\\""
          _    -> T.singleton c

    -- Check if a variable expression needs to be cast to OncePair* before accessing .fst/.snd
    libNeedsPairCast :: Text -> Bool
    libNeedsPairCast v' =
      ".fst" `T.isSuffixOf` v' || ".snd" `T.isSuffixOf` v' ||
      ")->fst" `T.isSuffixOf` v' || ")->snd" `T.isSuffixOf` v'

------------------------------------------------------------------------
-- Native target interpretation file handling
------------------------------------------------------------------------

-- | Get the file extension for native target interpretation files
nativeTargetExtension :: Target -> String
nativeTargetExtension TargetX86_64 = ".x86_64"
nativeTargetExtension TargetArm64 = ".arm64"
nativeTargetExtension TargetRiscV64 = ".riscv64"
nativeTargetExtension TargetC = ".c"

-- | Collect all interpretation assembly files for native targets from loaded modules
collectNativeInterpFiles :: FilePath -> Target -> ModuleEnv -> [FilePath]
collectNativeInterpFiles _strataPath _target env =
  -- Get target-specific files from loaded modules
  [path | LoadedModule { lmTargetPath = Just path } <- Map.elems (meModules env)]

-- | Resolve explicit interpretation files for native targets from -I:TYPE flags
-- Only returns files matching the target's InterpType
resolveExplicitNativeInterps :: FilePath -> Target -> [(InterpType, String)] -> [FilePath]
resolveExplicitNativeInterps strataPath target explicitInterps =
  let targetInterpType = case target of
        TargetX86_64 -> InterpX86_64
        TargetArm64 -> InterpArm64
        TargetRiscV64 -> InterpRiscV64
        TargetC -> InterpC
  in [ strataPath </> moduleToPath modPath ++ interpTypeExtension itype
     | (itype, modPath) <- explicitInterps
     , itype == targetInterpType
     ]

-- | Assemble interpretation files and return list of .o file paths
assembleInterpFiles :: Target -> [FilePath] -> FilePath -> IO [FilePath]
assembleInterpFiles _ [] _ = pure []
assembleInterpFiles target asmFiles outputBase = do
  -- For each .{arch} file, assemble to .o
  results <- mapM assembleOne (zip [0..] asmFiles)
  pure $ concat results
  where
    assembleOne :: (Int, FilePath) -> IO [FilePath]
    assembleOne (idx, asmPath) = do
      exists <- doesFileExist asmPath
      if exists
        then do
          let objPath = outputBase ++ "_interp_" ++ show idx ++ ".o"
          result <- Asm.assemble asmPath objPath
          case result of
            Left err -> do
              TIO.putStrLn $ "Warning: Failed to assemble " <> T.pack asmPath <> ": " <> T.pack (show err)
              pure []
            Right _ -> pure [objPath]
        else do
          TIO.putStrLn $ "Warning: Interpretation file not found: " <> T.pack asmPath
          pure []

------------------------------------------------------------------------
-- Arithmetic Primitive Inlining (OCP-0001)
------------------------------------------------------------------------

-- | Try to inline an arithmetic primitive as a C expression
-- Returns Just expr if it's an arithmetic primitive, Nothing otherwise
--
-- Binary ops expect input as a pair (v.fst op v.snd)
-- Unary ops expect input as a single value (-v)
inlineArithPrim :: Text -> Text -> Maybe Text
inlineArithPrim primName v = case primName of
  -- Addition (with and without __ prefix)
  -- Results cast to (void*) to maintain type compatibility with OncePair
  "__add_i8"  -> Just $ voidPtr (fstI8 v <> " + " <> sndI8 v)
  "__add_i16" -> Just $ voidPtr (fstI16 v <> " + " <> sndI16 v)
  "__add_i32" -> Just $ voidPtr (fstI32 v <> " + " <> sndI32 v)
  "__add_i64" -> Just $ voidPtr (fstI64 v <> " + " <> sndI64 v)
  "__add_f32" -> Just $ voidPtr (fstF32 v <> " + " <> sndF32 v)
  "__add_f64" -> Just $ voidPtr (fstF64 v <> " + " <> sndF64 v)
  "add_i8"  -> Just $ voidPtr (fstI8 v <> " + " <> sndI8 v)
  "add_i16" -> Just $ voidPtr (fstI16 v <> " + " <> sndI16 v)
  "add_i32" -> Just $ voidPtr (fstI32 v <> " + " <> sndI32 v)
  "add_i64" -> Just $ voidPtr (fstI64 v <> " + " <> sndI64 v)
  "add_f32" -> Just $ voidPtr (fstF32 v <> " + " <> sndF32 v)
  "add_f64" -> Just $ voidPtr (fstF64 v <> " + " <> sndF64 v)

  -- Subtraction
  "__sub_i8"  -> Just $ voidPtr (fstI8 v <> " - " <> sndI8 v)
  "__sub_i16" -> Just $ voidPtr (fstI16 v <> " - " <> sndI16 v)
  "__sub_i32" -> Just $ voidPtr (fstI32 v <> " - " <> sndI32 v)
  "__sub_i64" -> Just $ voidPtr (fstI64 v <> " - " <> sndI64 v)
  "__sub_f32" -> Just $ voidPtr (fstF32 v <> " - " <> sndF32 v)
  "__sub_f64" -> Just $ voidPtr (fstF64 v <> " - " <> sndF64 v)
  "sub_i8"  -> Just $ voidPtr (fstI8 v <> " - " <> sndI8 v)
  "sub_i16" -> Just $ voidPtr (fstI16 v <> " - " <> sndI16 v)
  "sub_i32" -> Just $ voidPtr (fstI32 v <> " - " <> sndI32 v)
  "sub_i64" -> Just $ voidPtr (fstI64 v <> " - " <> sndI64 v)
  "sub_f32" -> Just $ voidPtr (fstF32 v <> " - " <> sndF32 v)
  "sub_f64" -> Just $ voidPtr (fstF64 v <> " - " <> sndF64 v)

  -- Multiplication
  "__mul_i8"  -> Just $ voidPtr (fstI8 v <> " * " <> sndI8 v)
  "__mul_i16" -> Just $ voidPtr (fstI16 v <> " * " <> sndI16 v)
  "__mul_i32" -> Just $ voidPtr (fstI32 v <> " * " <> sndI32 v)
  "__mul_i64" -> Just $ voidPtr (fstI64 v <> " * " <> sndI64 v)
  "__mul_f32" -> Just $ voidPtr (fstF32 v <> " * " <> sndF32 v)
  "__mul_f64" -> Just $ voidPtr (fstF64 v <> " * " <> sndF64 v)
  "mul_i8"  -> Just $ voidPtr (fstI8 v <> " * " <> sndI8 v)
  "mul_i16" -> Just $ voidPtr (fstI16 v <> " * " <> sndI16 v)
  "mul_i32" -> Just $ voidPtr (fstI32 v <> " * " <> sndI32 v)
  "mul_i64" -> Just $ voidPtr (fstI64 v <> " * " <> sndI64 v)
  "mul_f32" -> Just $ voidPtr (fstF32 v <> " * " <> sndF32 v)
  "mul_f64" -> Just $ voidPtr (fstF64 v <> " * " <> sndF64 v)

  -- Division
  "__div_i8"  -> Just $ voidPtr (fstI8 v <> " / " <> sndI8 v)
  "__div_i16" -> Just $ voidPtr (fstI16 v <> " / " <> sndI16 v)
  "__div_i32" -> Just $ voidPtr (fstI32 v <> " / " <> sndI32 v)
  "__div_i64" -> Just $ voidPtr (fstI64 v <> " / " <> sndI64 v)
  "__div_f32" -> Just $ voidPtr (fstF32 v <> " / " <> sndF32 v)
  "__div_f64" -> Just $ voidPtr (fstF64 v <> " / " <> sndF64 v)
  "div_i8"  -> Just $ voidPtr (fstI8 v <> " / " <> sndI8 v)
  "div_i16" -> Just $ voidPtr (fstI16 v <> " / " <> sndI16 v)
  "div_i32" -> Just $ voidPtr (fstI32 v <> " / " <> sndI32 v)
  "div_i64" -> Just $ voidPtr (fstI64 v <> " / " <> sndI64 v)
  "div_f32" -> Just $ voidPtr (fstF32 v <> " / " <> sndF32 v)
  "div_f64" -> Just $ voidPtr (fstF64 v <> " / " <> sndF64 v)

  -- Modulo (integers only)
  "__mod_i8"  -> Just $ voidPtr (fstI8 v <> " % " <> sndI8 v)
  "__mod_i16" -> Just $ voidPtr (fstI16 v <> " % " <> sndI16 v)
  "__mod_i32" -> Just $ voidPtr (fstI32 v <> " % " <> sndI32 v)
  "__mod_i64" -> Just $ voidPtr (fstI64 v <> " % " <> sndI64 v)
  "mod_i8"  -> Just $ voidPtr (fstI8 v <> " % " <> sndI8 v)
  "mod_i16" -> Just $ voidPtr (fstI16 v <> " % " <> sndI16 v)
  "mod_i32" -> Just $ voidPtr (fstI32 v <> " % " <> sndI32 v)
  "mod_i64" -> Just $ voidPtr (fstI64 v <> " % " <> sndI64 v)

  -- Negation (unary) - cast void* to appropriate type, wrap result
  "__neg_i8"  -> Just $ voidPtr ("-(int8_t)(long)" <> v)
  "__neg_i16" -> Just $ voidPtr ("-(int16_t)(long)" <> v)
  "__neg_i32" -> Just $ voidPtr ("-(int32_t)(long)" <> v)
  "__neg_i64" -> Just $ voidPtr ("-(int64_t)(long)" <> v)
  "__neg_f32" -> Just $ voidPtr ("-*(float*)&" <> v)
  "__neg_f64" -> Just $ voidPtr ("-*(double*)&" <> v)
  "neg_i8"  -> Just $ voidPtr ("-(int8_t)(long)" <> v)
  "neg_i16" -> Just $ voidPtr ("-(int16_t)(long)" <> v)
  "neg_i32" -> Just $ voidPtr ("-(int32_t)(long)" <> v)
  "neg_i64" -> Just $ voidPtr ("-(int64_t)(long)" <> v)
  "neg_f32" -> Just $ voidPtr ("-*(float*)&" <> v)
  "neg_f64" -> Just $ voidPtr ("-*(double*)&" <> v)

  -- Comparisons (return int, wrapped to void*)
  "__lt_i8"  -> Just $ voidPtr (fstI8 v <> " < " <> sndI8 v)
  "__lt_i16" -> Just $ voidPtr (fstI16 v <> " < " <> sndI16 v)
  "__lt_i32" -> Just $ voidPtr (fstI32 v <> " < " <> sndI32 v)
  "__lt_i64" -> Just $ voidPtr (fstI64 v <> " < " <> sndI64 v)
  "__lt_f32" -> Just $ voidPtr (fstF32 v <> " < " <> sndF32 v)
  "__lt_f64" -> Just $ voidPtr (fstF64 v <> " < " <> sndF64 v)
  "lt_i8"  -> Just $ voidPtr (fstI8 v <> " < " <> sndI8 v)
  "lt_i16" -> Just $ voidPtr (fstI16 v <> " < " <> sndI16 v)
  "lt_i32" -> Just $ voidPtr (fstI32 v <> " < " <> sndI32 v)
  "lt_i64" -> Just $ voidPtr (fstI64 v <> " < " <> sndI64 v)
  "lt_f32" -> Just $ voidPtr (fstF32 v <> " < " <> sndF32 v)
  "lt_f64" -> Just $ voidPtr (fstF64 v <> " < " <> sndF64 v)

  "__le_i8"  -> Just $ voidPtr (fstI8 v <> " <= " <> sndI8 v)
  "__le_i16" -> Just $ voidPtr (fstI16 v <> " <= " <> sndI16 v)
  "__le_i32" -> Just $ voidPtr (fstI32 v <> " <= " <> sndI32 v)
  "__le_i64" -> Just $ voidPtr (fstI64 v <> " <= " <> sndI64 v)
  "le_i8"  -> Just $ voidPtr (fstI8 v <> " <= " <> sndI8 v)
  "le_i16" -> Just $ voidPtr (fstI16 v <> " <= " <> sndI16 v)
  "le_i32" -> Just $ voidPtr (fstI32 v <> " <= " <> sndI32 v)
  "le_i64" -> Just $ voidPtr (fstI64 v <> " <= " <> sndI64 v)

  "__gt_i8"  -> Just $ voidPtr (fstI8 v <> " > " <> sndI8 v)
  "__gt_i16" -> Just $ voidPtr (fstI16 v <> " > " <> sndI16 v)
  "__gt_i32" -> Just $ voidPtr (fstI32 v <> " > " <> sndI32 v)
  "__gt_i64" -> Just $ voidPtr (fstI64 v <> " > " <> sndI64 v)
  "gt_i8"  -> Just $ voidPtr (fstI8 v <> " > " <> sndI8 v)
  "gt_i16" -> Just $ voidPtr (fstI16 v <> " > " <> sndI16 v)
  "gt_i32" -> Just $ voidPtr (fstI32 v <> " > " <> sndI32 v)
  "gt_i64" -> Just $ voidPtr (fstI64 v <> " > " <> sndI64 v)

  "__ge_i8"  -> Just $ voidPtr (fstI8 v <> " >= " <> sndI8 v)
  "__ge_i16" -> Just $ voidPtr (fstI16 v <> " >= " <> sndI16 v)
  "__ge_i32" -> Just $ voidPtr (fstI32 v <> " >= " <> sndI32 v)
  "__ge_i64" -> Just $ voidPtr (fstI64 v <> " >= " <> sndI64 v)
  "ge_i8"  -> Just $ voidPtr (fstI8 v <> " >= " <> sndI8 v)
  "ge_i16" -> Just $ voidPtr (fstI16 v <> " >= " <> sndI16 v)
  "ge_i32" -> Just $ voidPtr (fstI32 v <> " >= " <> sndI32 v)
  "ge_i64" -> Just $ voidPtr (fstI64 v <> " >= " <> sndI64 v)

  "__eq_i8"  -> Just $ voidPtr (fstI8 v <> " == " <> sndI8 v)
  "__eq_i16" -> Just $ voidPtr (fstI16 v <> " == " <> sndI16 v)
  "__eq_i32" -> Just $ voidPtr (fstI32 v <> " == " <> sndI32 v)
  "__eq_i64" -> Just $ voidPtr (fstI64 v <> " == " <> sndI64 v)
  "__eq_f32" -> Just $ voidPtr (fstF32 v <> " == " <> sndF32 v)
  "__eq_f64" -> Just $ voidPtr (fstF64 v <> " == " <> sndF64 v)
  "eq_i8"  -> Just $ voidPtr (fstI8 v <> " == " <> sndI8 v)
  "eq_i16" -> Just $ voidPtr (fstI16 v <> " == " <> sndI16 v)
  "eq_i32" -> Just $ voidPtr (fstI32 v <> " == " <> sndI32 v)
  "eq_i64" -> Just $ voidPtr (fstI64 v <> " == " <> sndI64 v)
  "eq_f32" -> Just $ voidPtr (fstF32 v <> " == " <> sndF32 v)
  "eq_f64" -> Just $ voidPtr (fstF64 v <> " == " <> sndF64 v)

  "__ne_i8"  -> Just $ voidPtr (fstI8 v <> " != " <> sndI8 v)
  "__ne_i16" -> Just $ voidPtr (fstI16 v <> " != " <> sndI16 v)
  "__ne_i32" -> Just $ voidPtr (fstI32 v <> " != " <> sndI32 v)
  "__ne_i64" -> Just $ voidPtr (fstI64 v <> " != " <> sndI64 v)
  "ne_i8"  -> Just $ voidPtr (fstI8 v <> " != " <> sndI8 v)
  "ne_i16" -> Just $ voidPtr (fstI16 v <> " != " <> sndI16 v)
  "ne_i32" -> Just $ voidPtr (fstI32 v <> " != " <> sndI32 v)
  "ne_i64" -> Just $ voidPtr (fstI64 v <> " != " <> sndI64 v)

  _ -> Nothing
  where
    parens t = "(" <> t <> ")"
    -- Cast result to void* for storage in OncePair
    voidPtr t = "(void*)(" <> t <> ")"
    -- Cast void* to integer type
    fstI8 x = "(int8_t)(long)" <> x <> ".fst"
    sndI8 x = "(int8_t)(long)" <> x <> ".snd"
    fstI16 x = "(int16_t)(long)" <> x <> ".fst"
    sndI16 x = "(int16_t)(long)" <> x <> ".snd"
    fstI32 x = "(int32_t)(long)" <> x <> ".fst"
    sndI32 x = "(int32_t)(long)" <> x <> ".snd"
    fstI64 x = "(int64_t)(long)" <> x <> ".fst"
    sndI64 x = "(int64_t)(long)" <> x <> ".snd"
    -- For floats, we need to pass by value (stored directly in void* as bits)
    fstF32 x = "*(float*)&" <> x <> ".fst"
    sndF32 x = "*(float*)&" <> x <> ".snd"
    fstF64 x = "*(double*)&" <> x <> ".fst"
    sndF64 x = "*(double*)&" <> x <> ".snd"
    -- Old generic accessors (kept for reference)
    fstOf x = x <> ".fst"
    sndOf x = x <> ".snd"
