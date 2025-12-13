module Once.CLI
  ( run
  , Command (..)
  , BuildOptions (..)
  , CheckOptions (..)
  , OutputMode (..)
  , AllocStrategy (..)
  , Target (..)
  , targetExtension
  , parseTarget
  ) where

import Control.Applicative ((<|>))
import Data.List (isSuffixOf)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (listDirectory, doesDirectoryExist)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeBaseName, takeDirectory, (</>))

import Once.Backend.C (generateC, CModule (..))
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
                          -- Generate library with all functions
                          let (header, source') = generateLibraryAll optimizedFunctions
                              headerPath = outputBase ++ ".h"
                              sourcePath = outputBase ++ ".c"
                          TIO.writeFile headerPath header
                          TIO.writeFile sourcePath source'
                          TIO.putStrLn $ "Generated: " <> T.pack headerPath <> ", " <> T.pack sourcePath
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

                      -- Check if target is supported
                      case target of
                        TargetC -> pure ()  -- C is supported
                        other -> do
                          TIO.putStrLn $ "Error: Target '" <> T.pack (show other) <> "' not yet implemented"
                          TIO.putStrLn "Hint: Use --target c for C backend"
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

                          -- For executable, generate C with main() wrapper
                          -- Load interpretation C code from --interp and from imported modules
                          interpCodeLegacy <- case buildInterp opts of
                            Nothing -> pure ""
                            Just interpPath -> loadInterpretationCode interpPath

                          -- Collect target-specific files from imported interpretation modules
                          let importedTargetFiles = collectTargetFiles modEnv
                          importedCode <- T.concat <$> mapM TIO.readFile importedTargetFiles

                          let sourcePath = outputBase ++ ".c"
                              alloc = mainAlloc <|> buildAlloc opts
                              interpCode = interpCodeLegacy <> "\n" <> importedCode
                              source' = generateExecutableAll optimizedFunctions alloc primitives interpCode
                          TIO.writeFile sourcePath source'
                          TIO.putStrLn $ "Generated: " <> T.pack sourcePath
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
      Once.IR.Fst _ _ -> v <> ".fst"
      Once.IR.Snd _ _ -> v <> ".snd"
      Once.IR.Pair f g -> "(OncePair){ .fst = " <> generateIRExpr f v <> ", .snd = " <> generateIRExpr g v <> " }"
      Once.IR.Compose g f -> generateIRExpr g (generateIRExpr f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      Once.IR.Case l r -> "(" <> v <> ".tag == 0 ? " <> generateIRExpr l (v <> ".value") <> " : " <> generateIRExpr r (v <> ".value") <> ")"
      Once.IR.Initial _ -> v
      Once.IR.Curry _ -> "/* curry not yet implemented */ ((void*)0)"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'  -- Local variable: just use the name
      Once.IR.FunRef n' -> "(void*)once_" <> n'  -- Function reference (pointer, not call)
      Once.IR.Prim n' _ _ -> "once_" <> n' <> "(" <> v <> ")"
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
                      -> Text
generateExecutableAll functions defaultAlloc primitives interpCode = T.unlines
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

    -- Generate type definitions based on what's needed
    typeDefinitions = T.unlines $ concat
      [ if any needsPair allTypes then ["typedef struct { void* fst; void* snd; } OncePair;"] else []
      , if any needsSum allTypes then ["typedef struct { int tag; void* value; } OnceSum;"] else []
      , if any needsBuffer allTypes then ["typedef struct { const char* data; size_t len; } OnceBuffer;"] else []
      , if any needsString allTypes then ["typedef OnceBuffer OnceString;"] else []
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
    generateFuncWithAlloc n t ir alloc = T.unlines
      [ funcDecl n t <> " {"
      , "    return " <> generateIRExpr alloc ir "x" <> ";"
      , "}"
      ]

    funcDecl :: Text -> Type -> Text
    funcDecl n t = case t of
      TArrow inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " x)"
      TEff inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " x)"  -- D032
      _ -> "void* once_" <> n <> "(void)"

    generateIRExpr :: Maybe AllocStrategy -> Once.IR.IR -> Text -> Text
    generateIRExpr alloc i v = case i of
      Once.IR.Id _ -> v
      Once.IR.Fst _ _ -> v <> ".fst"
      Once.IR.Snd _ _ -> v <> ".snd"
      Once.IR.Pair f g -> "(OncePair){ .fst = " <> generateIRExpr alloc f v <> ", .snd = " <> generateIRExpr alloc g v <> " }"
      Once.IR.Compose g f -> generateIRExpr alloc g (generateIRExpr alloc f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      Once.IR.Case l r -> "(" <> v <> ".tag == 0 ? " <> generateIRExpr alloc l (v <> ".value") <> " : " <> generateIRExpr alloc r (v <> ".value") <> ")"
      Once.IR.Initial _ -> v
      Once.IR.Curry _ -> "/* curry not yet implemented */ ((void*)0)"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'
      Once.IR.FunRef n' -> "(void*)once_" <> n'  -- Function reference (pointer, not call)
      Once.IR.Prim n' _ _ -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.StringLit s -> generateStringLit alloc s
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      Once.IR.Let x' e1 e2 ->
        let e1Code = generateIRExpr alloc e1 v
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> generateIRExpr alloc e2 x' <> "; })"

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
      TBuffer -> "OnceBuffer"
      TString _ -> "OnceString"
      TProduct _ _ -> "OncePair"
      TSum _ _ -> "OnceSum"
      TArrow _ _ -> "void*"
      TEff _ _ -> "void*"  -- D032: Eff same as Arrow at runtime
      TApp _ _ -> "void*"
      TFix _ -> "void*"

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
      _ -> "/* " <> name <> " has non-function type */"

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
      _ -> "/* " <> name <> " has non-function type */"

    libCTypeName :: Type -> Text
    libCTypeName t = case t of
      TVar _ -> "void*"
      TUnit -> "void*"
      TVoid -> "void"
      TInt -> "int"
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
      Once.IR.Fst _ _ -> v <> ".fst"
      Once.IR.Snd _ _ -> v <> ".snd"
      Once.IR.Pair f g -> "(OncePair){ .fst = " <> libGenerateIRExpr alloc f v <> ", .snd = " <> libGenerateIRExpr alloc g v <> " }"
      Once.IR.Compose g f -> libGenerateIRExpr alloc g (libGenerateIRExpr alloc f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      Once.IR.Case l r -> "(" <> v <> ".tag == 0 ? " <> libGenerateIRExpr alloc l (v <> ".value") <> " : " <> libGenerateIRExpr alloc r (v <> ".value") <> ")"
      Once.IR.Initial _ -> v
      Once.IR.Curry _ -> "/* curry not yet implemented */ ((void*)0)"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'
      Once.IR.FunRef n' -> "(void*)once_" <> n'
      Once.IR.Prim n' _ _ -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.StringLit s -> libGenerateStringLit alloc s
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      Once.IR.Let x' e1 e2 ->
        let e1Code = libGenerateIRExpr alloc e1 v
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> libGenerateIRExpr alloc e2 x' <> "; })"

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
