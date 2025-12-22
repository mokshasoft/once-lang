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
import Data.Set (Set)
import qualified Data.Set as Set
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
import Once.Monomorphize (monomorphizeWithContext, extractPrimitiveFamilies, PrimitiveFamilies, applySubstToIR)
import Once.Optimize (optimize, optimizeWith, OptimizerBackend (..))
import Once.Parser (parseModule)
import Once.Syntax (Module (..), Decl (..), Expr, AllocStrategy (..))
import Once.Type (Type (..))
import qualified Once.TypeCheck
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
          -- Type check with module environment (returns substitutions per function)
          case checkModuleWithEnv modEnv m of
            Left err -> do
              TIO.putStrLn $ "Type error: " <> T.pack (show err)
              exitFailure
            Right typeSubsts -> do
              -- Extract primitives and all function definitions (including derived modules)
              -- Derived functions come first since main module may call them
              let primitives = extractPrimitives m
                  derivedFuncs = extractDerivedFunctions modEnv
                  allFunctions = derivedFuncs ++ extractFunctions m

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
                          -- Apply type substitutions to IR (instantiate type variables)
                          let substFunctions = [(n, t, a, applyFuncSubst typeSubsts n ir) | (n, t, a, ir) <- irFunctions]
                          -- Collect primitive families from main module and imports (D038)
                          let families = collectAllFamilies m modEnv
                          -- Monomorphize primitives using family mappings and function types
                          let monoFunctions = [(n, t, a, monomorphizeWithContext families t ir) | (n, t, a, ir) <- substFunctions]
                          -- Optimize
                          let opt = optimizeWith (buildOptimizer opts)
                          let optimizedFunctions = [(n, t, a, opt ir) | (n, t, a, ir) <- monoFunctions]
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
                          -- Apply type substitutions to IR (instantiate type variables)
                          let substFunctions = [(n, t, a, applyFuncSubst typeSubsts n ir) | (n, t, a, ir) <- irFunctions]
                          -- Collect primitive families from main module and imports (D038)
                          let families = collectAllFamilies m modEnv
                          -- Monomorphize primitives using family mappings and function types
                          let monoFunctions = [(n, t, a, monomorphizeWithContext families t ir) | (n, t, a, ir) <- substFunctions]
                          -- Optimize all IRs
                          let opt = optimizeWith (buildOptimizer opts)
                          let optimizedFunctions = [(n, t, a, opt ir) | (n, t, a, ir) <- monoFunctions]

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

-- | Collect all primitive families from the main module and imported modules
-- Combines families from:
-- 1. The main module being compiled
-- 2. All imported modules in the ModuleEnv
collectAllFamilies :: Module -> ModuleEnv -> PrimitiveFamilies
collectAllFamilies mainMod modEnv =
  let mainFamilies = extractPrimitiveFamilies mainMod
      importedFamilies = mconcat
        [ extractPrimitiveFamilies (lmModule lm)
        | lm <- Map.elems (meModules modEnv)
        ]
  in Map.union mainFamilies importedFamilies  -- main takes precedence

-- | Apply substitution for a specific function to its IR
-- Looks up the function's substitution and applies it to instantiate type variables
applyFuncSubst :: Map.Map Text Once.TypeCheck.Subst -> Text -> Once.IR.IR -> Once.IR.IR
applyFuncSubst substs funcName ir =
  case Map.lookup funcName substs of
    Just subst -> applySubstToIR subst ir
    Nothing -> ir  -- No substitution found, keep IR unchanged

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

-- | Extract functions from derived modules (modules without .c target files)
-- These need to be compiled as C functions
extractDerivedFunctions :: ModuleEnv -> [(Text, Type, Maybe AllocStrategy, Expr)]
extractDerivedFunctions modEnv =
  [ (name, ty, alloc, expr)
  | lm <- Map.elems (meModules modEnv)
  , Nothing <- [lmTargetPath lm]  -- Only modules without .c files
  , (name, ty, alloc, expr) <- extractFunctions (lmModule lm)
  ]

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
    onceFuncCode n t ir =
      -- D039: If function body is a Curry, use its variable name for the parameter
      let (paramName, body) = case ir of
            Once.IR.Curry varName bodyIR -> (varName, bodyIR)
            _ -> ("x", ir)
      in T.unlines
        [ funcDeclSimple n t paramName <> " {"
        , "    return " <> generateIRExpr Set.empty body paramName <> ";"
        , "}"
        ]

    funcDeclSimple :: Text -> Type -> Text -> Text
    funcDeclSimple n t param = case t of
      TArrow inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " " <> param <> ")"
      TEff inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " " <> param <> ")"  -- D032
      _ -> "void* once_" <> n <> "(void)"

    -- Check if an IR expression might produce an aggregate (OncePair)
    -- This is conservative: if we're unsure, return True to avoid invalid casts.
    -- Can't cast OncePair struct to intptr_t, so we must not cast these.
    -- Used for Case expressions where casting an aggregate would be an error.
    isPairIR :: Once.IR.IR -> Bool
    isPairIR (Once.IR.Pair _ _) = True  -- Definitely a pair
    isPairIR (Once.IR.Let _ _ e2) = isPairIR e2  -- Let returns e2
    isPairIR (Once.IR.Curry _ body) = isPairIR body  -- Curry evaluates body
    isPairIR (Once.IR.Case l r) = isPairIR l || isPairIR r  -- EITHER branch might be pair
    isPairIR (Once.IR.Compose g _) = isPairIR g  -- Compose returns g's result
    isPairIR (Once.IR.Var _) = True  -- Function calls might return pairs - be conservative
    isPairIR (Once.IR.LocalVar _) = True  -- Variables might hold pairs - be conservative
    isPairIR _ = False

    -- Check if an IR expression DEFINITELY produces a new pair value that needs heap allocation.
    -- This is structural: only returns True for Pair constructors, not for Var/LocalVar
    -- which might already hold heap-allocated pair pointers.
    constructsPair1 :: Once.IR.IR -> Bool
    constructsPair1 (Once.IR.Pair _ _) = True  -- Definitely constructs a pair
    constructsPair1 (Once.IR.Let _ _ e2) = constructsPair1 e2  -- Let returns e2
    constructsPair1 (Once.IR.Curry _ body) = constructsPair1 body  -- Curry evaluates body
    constructsPair1 (Once.IR.Case l r) = constructsPair1 l || constructsPair1 r  -- Either branch might construct pair
    constructsPair1 (Once.IR.Compose g _) = constructsPair1 g  -- Compose returns g's result
    constructsPair1 _ = False  -- Var/LocalVar don't construct new pairs, they reference existing values

    -- Wrap expressions for OncePair fields
    -- Nested pairs need to be heap-allocated since OncePair.snd is intptr_t
    -- OnceBuffer/OnceString values need to be cast to intptr_t
    wrapForPair :: Set Text -> Once.IR.IR -> Text -> Text
    wrapForPair pairVars ir expr
      | constructsPair1 ir = "({ OncePair* _tmp = malloc(sizeof(OncePair)); *_tmp = " <> expr <> "; (intptr_t)_tmp; })"
      | yieldsPointerType ir = "(intptr_t)(" <> expr <> ")"
      | otherwise = expr

    -- Check if an IR expression might yield a pointer type (OnceBuffer, OnceString)
    -- These need to be cast to intptr_t when stored in OncePair fields
    yieldsPointerType :: Once.IR.IR -> Bool
    yieldsPointerType ir = case ir of
      Once.IR.Prim _ _ outTy -> isPointerType outTy
      Once.IR.Var _ -> True  -- Function calls might return pointers
      Once.IR.LocalVar _ -> True  -- Variables might hold pointers
      Once.IR.Compose g _ -> yieldsPointerType g  -- Check the final result
      _ -> False

    isPointerType :: Type -> Bool
    isPointerType TBuffer = True
    isPointerType (TString _) = True
    isPointerType (TArray _) = True
    isPointerType _ = False

    -- Check if an expression looks like nested pair access or is a known pair variable
    isPairAccess :: Set Text -> Text -> Bool
    isPairAccess pairVars expr =
      ".snd" `T.isSuffixOf` expr ||
      ".fst" `T.isSuffixOf` expr ||
      expr `Set.member` pairVars

    -- Check if an expression might yield a POINTER to a pair (for dereferencing)
    -- This happens when extracting from a nested pair via Snd/Fst
    -- Pair constructions yield OncePair VALUES, not pointers
    yieldsPairPointer :: Once.IR.IR -> Bool
    yieldsPairPointer (Once.IR.Snd _ _) = True  -- Might extract a nested pair pointer
    yieldsPairPointer (Once.IR.Fst _ _) = True  -- Might extract a nested pair pointer
    yieldsPairPointer (Once.IR.Compose g _) = yieldsPairPointer g  -- Check the outer operation
    yieldsPairPointer _ = False

    -- pairVars: Set of variable names that might hold pair pointers (from Snd/Fst/Pair)
    generateIRExpr :: Set Text -> Once.IR.IR -> Text -> Text
    generateIRExpr pairVars i v = case i of
      Once.IR.Id _ -> v
      -- For Fst/Snd: if accessing from a nested pair (v ends with .snd/.fst or is a pair var),
      -- we need to dereference because nested pairs are heap-allocated
      Once.IR.Fst _ _ ->
        if isPairAccess pairVars v
        then "(*(OncePair*)(" <> v <> ")).fst"
        else v <> ".fst"
      Once.IR.Snd _ _ ->
        if isPairAccess pairVars v
        then "(*(OncePair*)(" <> v <> ")).snd"
        else v <> ".snd"
      Once.IR.Pair f g ->
        let fExpr = generateIRExpr pairVars f v
            gExpr = generateIRExpr pairVars g v
        in "(OncePair){ .fst = " <> wrapForPair pairVars f fExpr <> ", .snd = " <> wrapForPair pairVars g gExpr <> " }"
      Once.IR.Compose g f -> generateIRExpr pairVars g (generateIRExpr pairVars f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      -- For Case expressions: if either branch produces an aggregate (OncePair),
      -- don't cast. Otherwise cast both to intptr_t for pointer type compatibility.
      Once.IR.Case l r ->
        let lExpr = generateIRExpr pairVars l (v <> ".value")
            rExpr = generateIRExpr pairVars r (v <> ".value")
        in if isPairIR l || isPairIR r
           then "(" <> v <> ".tag == 0 ? " <> lExpr <> " : " <> rExpr <> ")"
           else "(" <> v <> ".tag == 0 ? (intptr_t)(" <> lExpr <> ") : (intptr_t)(" <> rExpr <> "))"
      Once.IR.Initial _ -> v
      -- D039: Curry inside expression (e.g., case branches) needs to bind the variable
      Once.IR.Curry varName body ->
        "({ typeof(" <> v <> ") " <> varName <> " = " <> v <> "; " <> generateIRExpr pairVars body varName <> "; })"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'  -- Local variable (let binding or lambda param)
      Once.IR.FunRef n' -> "(void*)once_" <> n'  -- Function reference (pointer, not call)
      -- Integer literals: __int_N -> just the number
      Once.IR.Prim n' _ TInt | "__int_" `T.isPrefixOf` n' ->
        let numStr = T.drop 6 n'  -- drop "__int_" prefix
        in "((int64_t)" <> numStr <> ")"
      -- Generic array read: read : Array A * Int -> A
      Once.IR.Prim "read" (TArrow (TProduct (TArray elemTy) TInt) _) _ ->
        case elemCType elemTy of
          Just cType ->
            "({ OncePair _arg = " <> v <> "; " <>
            "((" <> cType <> "*)((OnceBuffer)_arg.fst)->data)[(int64_t)_arg.snd]; })"
          Nothing -> error $ "Unsupported array element type for read: " ++ show elemTy
      -- Generic array write: write : Array A * (Int * A) -> Array A
      Once.IR.Prim "write" (TArrow (TProduct (TArray elemTy) (TProduct TInt _)) _) _ ->
        case elemCType elemTy of
          Just cType ->
            "({ OncePair _arg = " <> v <> "; " <>
            "OncePair* _iv = (OncePair*)_arg.snd; " <>
            "((" <> cType <> "*)((OnceBuffer)_arg.fst)->data)[(int64_t)_iv->fst] = (" <> cType <> ")_iv->snd; " <>
            "(OnceBuffer)_arg.fst; })"
          Nothing -> error $ "Unsupported array element type for write: " ++ show elemTy
      -- Generic array length: length : Array A -> Int
      Once.IR.Prim "length" (TArrow (TArray elemTy) TInt) _ ->
        case elemSz elemTy of
          Just size ->
            "(int64_t)(((OnceBuffer)" <> v <> ")->len / " <> size <> ")"
          Nothing -> error $ "Unsupported array element type for length: " ++ show elemTy
      -- Primitives: unpack product types into separate C function arguments
      -- When dealing with complex argument expressions (inline pairs with malloc),
      -- bind to a temporary variable first to avoid duplicating the expression
      Once.IR.Prim n' inTy _ ->
        let primCall argExpr = "once_" <> n' <> "(" <> unpackArgs inTy argExpr <> ")"
            isComplex = T.any (\c -> c == '{' || c == '(') v && needsUnpacking inTy
        in if isComplex
           then "({ OncePair _arg = " <> v <> "; " <> primCall "_arg" <> "; })"
           else primCall v
      Once.IR.StringLit s -> generateStringLit s
      -- Recursive type operations (identity at runtime)
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      -- Let binding: use GCC statement expression ({ ... })
      -- Track variables that might hold pair pointers (from Snd/Fst/Pair operations)
      Once.IR.Let x' e1 e2 ->
        let e1Code = generateIRExpr pairVars e1 v
            -- If e1 extracts from a pair (Snd/Fst), track x' as potentially holding a pair pointer
            newPairVars = if yieldsPairPointer e1 then Set.insert x' pairVars else pairVars
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> generateIRExpr newPairVars e2 x' <> "; })"

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

    -- Check if type contains TArray/TBuffer (which need special handling due to type erasure)
    needsUnpacking :: Type -> Bool
    needsUnpacking ty = case ty of
      TArray _ -> True
      TBuffer -> True
      TProduct a b -> needsUnpacking a || needsUnpacking b
      TArrow dom _ -> needsUnpacking dom
      TEff dom _ -> needsUnpacking dom
      _ -> False

    -- Unpack product types into separate C function arguments
    -- Only used for primitives that contain Array/Buffer types
    -- For primitives: (A * B) -> "v.fst, v.snd"
    -- For nested: (A * (B * C)) -> "v.fst, v.snd.fst, v.snd.snd"
    -- Cast each component to its C type since OncePair uses intptr_t
    unpackArgs :: Type -> Text -> Text
    unpackArgs ty v
      | needsUnpacking ty = unpackArgsImpl ty v
      | otherwise = v  -- Keep as single OncePair for scalar types

    unpackArgsImpl :: Type -> Text -> Text
    unpackArgsImpl ty v = case ty of
      -- Nested pair: .snd is stored as a pointer, need to dereference
      TProduct a b@(TProduct _ _) ->
        let sndExpr = "(*(OncePair*)(" <> v <> ".snd))"
        in unpackArgsImpl a (v <> ".fst") <> ", " <> unpackArgsImpl b sndExpr
      -- Simple pair: both elements stored directly
      TProduct a b -> unpackArgsImpl a (v <> ".fst") <> ", " <> unpackArgsImpl b (v <> ".snd")
      TArrow dom _ -> unpackArgsImpl dom v  -- Unwrap arrow type (primitive signature)
      TEff dom _ -> unpackArgsImpl dom v    -- Unwrap eff type
      -- Base types: cast from intptr_t to correct C type
      TInt -> "(int64_t)(" <> v <> ")"
      TFloat -> "(double)(" <> v <> ")"
      TByte -> "(uint8_t)(" <> v <> ")"
      TArray _ -> "(OnceBuffer)(" <> v <> ")"
      TBuffer -> "(OnceBuffer)(" <> v <> ")"
      TString _ -> "(OnceString)(" <> v <> ")"
      _ -> v  -- Other types: just use the value directly

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
      TInt -> "int64_t"
      TFloat -> "double"
      TByte -> "uint8_t"
      TBuffer -> "OnceBuffer"
      TArray _ -> "OnceBuffer"  -- D042: Array erases to Buffer
      TString _ -> "OnceString"
      TProduct _ _ -> "OncePair"
      TSum _ _ -> "OnceSum"
      TArrow _ _ -> "void*"
      TEff _ _ -> "void*"  -- D032: Eff same as Arrow at runtime
      TApp _ _ -> "void*"
      TFix _ -> "void*"

    -- D046: Get C type for primitive array element types
    elemCType :: Type -> Maybe Text
    elemCType TInt = Just "int64_t"
    elemCType TFloat = Just "double"
    elemCType TByte = Just "uint8_t"
    elemCType (TVar _) = Just "int64_t"  -- Fallback for unsubstituted type vars
    elemCType _ = Nothing

    -- D046: Get element size for primitive array element types
    elemSz :: Type -> Maybe Text
    elemSz TInt = Just "8"
    elemSz TFloat = Just "8"
    elemSz TByte = Just "1"
    elemSz (TVar _) = Just "8"  -- Fallback for unsubstituted type vars
    elemSz _ = Nothing

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

    -- Type definitions: Only emit includes here.
    -- Actual type definitions come from interpretation files which have proper guards.
    -- This avoids conflicts with pointer-based OnceBuffer in interpretations.
    typeDefinitions = T.unlines
      [ "#include <stdint.h>"   -- For intptr_t, int64_t
      , "#include <stddef.h>"   -- For size_t
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
      TArray _ -> True  -- D042: Array erases to Buffer
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
    generateFuncWithAlloc n t ir alloc =
      -- D039: If function body is a Curry, use its variable name for the parameter
      let (paramName, body) = case ir of
            Once.IR.Curry varName bodyIR -> (varName, bodyIR)
            _ -> ("x", ir)
          -- Get return type for casting (handle pair element extraction that returns intptr_t)
          returnType = case t of
            TArrow _ outTy -> outTy
            TEff _ outTy -> outTy
            _ -> TUnit
          bodyExpr = generateIRExpr alloc Set.empty returnType body paramName
          -- Cast return value if function returns a pointer type but body might yield intptr_t
          returnExpr = case returnType of
            TBuffer -> "(" <> cTypeName returnType <> ")(" <> bodyExpr <> ")"
            TString _ -> "(" <> cTypeName returnType <> ")(" <> bodyExpr <> ")"
            TArray _ -> "(" <> cTypeName returnType <> ")(" <> bodyExpr <> ")"
            TUnit -> "(void*)(" <> bodyExpr <> ")"  -- Cast to void* for Eff returns
            _ -> bodyExpr
      in T.unlines
        [ funcDeclWithParam n t paramName <> " {"
        , "    return " <> returnExpr <> ";"
        , "}"
        ]

    funcDeclWithParam :: Text -> Type -> Text -> Text
    funcDeclWithParam n t param = case t of
      TArrow inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " " <> param <> ")"
      TEff inTy outTy -> cTypeName outTy <> " once_" <> n <> "(" <> cTypeName inTy <> " " <> param <> ")"  -- D032
      _ -> "void* once_" <> n <> "(void)"

    -- Check if an IR expression might produce an aggregate (OncePair)
    -- This is conservative: if we're unsure, return True to avoid invalid casts.
    -- Can't cast OncePair struct to intptr_t, so we must not cast these.
    -- Used for Case expressions where casting an aggregate would be an error.
    isPairIR2 :: Once.IR.IR -> Bool
    isPairIR2 (Once.IR.Pair _ _) = True  -- Definitely a pair
    isPairIR2 (Once.IR.Let _ _ e2) = isPairIR2 e2  -- Let returns e2
    isPairIR2 (Once.IR.Curry _ body) = isPairIR2 body  -- Curry evaluates body
    isPairIR2 (Once.IR.Case l r) = isPairIR2 l || isPairIR2 r  -- EITHER branch might be pair
    isPairIR2 (Once.IR.Compose g _) = isPairIR2 g  -- Compose returns g's result
    isPairIR2 (Once.IR.Var _) = True  -- Function calls might return pairs - be conservative
    isPairIR2 (Once.IR.LocalVar _) = True  -- Variables might hold pairs - be conservative
    isPairIR2 _ = False

    -- Check if an IR expression DEFINITELY produces a new pair value that needs heap allocation.
    -- This is structural: only returns True for Pair constructors, not for Var/LocalVar
    -- which might already hold heap-allocated pair pointers.
    constructsPair :: Once.IR.IR -> Bool
    constructsPair (Once.IR.Pair _ _) = True  -- Definitely constructs a pair
    constructsPair (Once.IR.Let _ _ e2) = constructsPair e2  -- Let returns e2
    constructsPair (Once.IR.Curry _ body) = constructsPair body  -- Curry evaluates body
    constructsPair (Once.IR.Case l r) = constructsPair l || constructsPair r  -- Either branch might construct pair
    constructsPair (Once.IR.Compose g _) = constructsPair g  -- Compose returns g's result
    constructsPair _ = False  -- Var/LocalVar don't construct new pairs, they reference existing values

    -- Wrap expressions for OncePair fields
    -- Nested pairs need to be heap-allocated since OncePair.snd is intptr_t
    -- OnceBuffer/OnceString values need to be cast to intptr_t
    wrapForPair2 :: Once.IR.IR -> Text -> Text
    wrapForPair2 ir expr
      | constructsPair ir = "({ OncePair* _tmp = malloc(sizeof(OncePair)); *_tmp = " <> expr <> "; (intptr_t)_tmp; })"
      | yieldsPointerType2 ir = "(intptr_t)(" <> expr <> ")"
      | otherwise = expr

    -- Check if an IR expression might yield a pointer type (OnceBuffer, OnceString)
    yieldsPointerType2 :: Once.IR.IR -> Bool
    yieldsPointerType2 ir = case ir of
      Once.IR.Prim _ _ outTy -> isPointerType2 outTy
      Once.IR.Var _ -> True  -- Function calls might return pointers
      Once.IR.LocalVar _ -> True  -- Variables might hold pointers
      Once.IR.Compose g _ -> yieldsPointerType2 g  -- Check the final result
      _ -> False

    isPointerType2 :: Type -> Bool
    isPointerType2 TBuffer = True
    isPointerType2 (TString _) = True
    isPointerType2 (TArray _) = True
    isPointerType2 _ = False

    -- Check if an expression looks like nested pair access or is a known pair variable
    isPairAccess2 :: Set Text -> Text -> Bool
    isPairAccess2 pairVars expr =
      ".snd" `T.isSuffixOf` expr ||
      ".fst" `T.isSuffixOf` expr ||
      expr `Set.member` pairVars

    -- Check if an expression might yield a POINTER to a pair (for dereferencing)
    yieldsPairPointer2 :: Once.IR.IR -> Bool
    yieldsPairPointer2 (Once.IR.Snd _ _) = True
    yieldsPairPointer2 (Once.IR.Fst _ _) = True
    yieldsPairPointer2 (Once.IR.Compose g _) = yieldsPairPointer2 g
    yieldsPairPointer2 _ = False

    -- Check if a type is a product (pair) type
    isProductType :: Type -> Bool
    isProductType (TProduct _ _) = True
    isProductType _ = False

    generateIRExpr :: Maybe AllocStrategy -> Set Text -> Type -> Once.IR.IR -> Text -> Text
    generateIRExpr alloc pairVars retTy i v = case i of
      Once.IR.Id _ -> v
      Once.IR.Fst _ _ ->
        if isPairAccess2 pairVars v
        then "(*(OncePair*)(" <> v <> ")).fst"
        else v <> ".fst"
      Once.IR.Snd _ _ ->
        if isPairAccess2 pairVars v
        then "(*(OncePair*)(" <> v <> ")).snd"
        else v <> ".snd"
      Once.IR.Pair f g ->
        let fExpr = generateIRExpr alloc pairVars retTy f v
            gExpr = generateIRExpr alloc pairVars retTy g v
        in "(OncePair){ .fst = " <> wrapForPair2 f fExpr <> ", .snd = " <> wrapForPair2 g gExpr <> " }"
      Once.IR.Compose g f -> generateIRExpr alloc pairVars retTy g (generateIRExpr alloc pairVars retTy f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      -- For Case expressions: if function returns a product type (pair), don't cast.
      -- Otherwise cast both branches to intptr_t for pointer type compatibility.
      Once.IR.Case l r ->
        let lExpr = generateIRExpr alloc pairVars retTy l (v <> ".value")
            rExpr = generateIRExpr alloc pairVars retTy r (v <> ".value")
        in if isProductType retTy || constructsPair l || constructsPair r
           then "(" <> v <> ".tag == 0 ? " <> lExpr <> " : " <> rExpr <> ")"
           else "(" <> v <> ".tag == 0 ? (intptr_t)(" <> lExpr <> ") : (intptr_t)(" <> rExpr <> "))"
      Once.IR.Initial _ -> v
      -- D039: Curry inside expression (e.g., case branches) needs to bind the variable
      Once.IR.Curry varName body ->
        "({ typeof(" <> v <> ") " <> varName <> " = " <> v <> "; " <> generateIRExpr alloc pairVars retTy body varName <> "; })"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'  -- Local variable (let binding or lambda param)
      Once.IR.FunRef n' -> "(void*)once_" <> n'  -- Function reference (pointer, not call)
      -- Integer literals: __int_N -> just the number
      Once.IR.Prim n' _ TInt | "__int_" `T.isPrefixOf` n' ->
        let numStr = T.drop 6 n'  -- drop "__int_" prefix
        in "((int64_t)" <> numStr <> ")"
      -- Generic array read: unsafeRead : Array A * Int -> A
      -- The primitive's inType is the full arrow type TArrow (TProduct (TArray A) TInt) A
      -- D046: No bounds checking - caller must ensure valid index
      Once.IR.Prim "unsafeRead" (TArrow (TProduct (TArray elemTy) TInt) _) _ ->
        case elementCType elemTy of
          Just cType ->
            "({ OncePair _arg = " <> v <> "; " <>
            "((" <> cType <> "*)((OnceBuffer)_arg.fst)->data)[(int64_t)_arg.snd]; })"
          Nothing -> error $ "Unsupported array element type for unsafeRead: " ++ show elemTy
      -- Generic array write: unsafeWrite : Array A * (Int * A) -> Array A
      -- The primitive's inType is the full arrow type TArrow (TProduct (TArray A) (TProduct TInt A)) (TArray A)
      -- D046: No bounds checking - caller must ensure valid index
      Once.IR.Prim "unsafeWrite" (TArrow (TProduct (TArray elemTy) (TProduct TInt _)) _) _ ->
        case elementCType elemTy of
          Just cType ->
            "({ OncePair _arg = " <> v <> "; " <>
            "OncePair* _iv = (OncePair*)_arg.snd; " <>
            "((" <> cType <> "*)((OnceBuffer)_arg.fst)->data)[(int64_t)_iv->fst] = (" <> cType <> ")_iv->snd; " <>
            "(OnceBuffer)_arg.fst; })"
          Nothing -> error $ "Unsupported array element type for unsafeWrite: " ++ show elemTy
      -- Generic array length: length : Array A -> Int
      -- The primitive's inType is the full arrow type TArrow (TArray A) TInt
      Once.IR.Prim "length" (TArrow (TArray elemTy) TInt) _ ->
        case elementSize elemTy of
          Just size ->
            "(int64_t)(((OnceBuffer)" <> v <> ")->len / " <> size <> ")"
          Nothing -> error $ "Unsupported array element type for length: " ++ show elemTy
      -- Primitives: unpack product types into separate C function arguments
      -- When dealing with complex argument expressions (inline pairs with malloc),
      -- bind to a temporary variable first to avoid duplicating the expression
      Once.IR.Prim n' inTy _ ->
        let primCall argExpr = "once_" <> n' <> "(" <> unpackArgs inTy argExpr <> ")"
            -- Check if v is a complex expression that shouldn't be duplicated
            -- Simple expressions: variable names, single tokens
            -- Complex expressions: contain {, (, etc.
            isComplex = T.any (\c -> c == '{' || c == '(') v && needsUnpacking inTy
        in if isComplex
           then "({ OncePair _arg = " <> v <> "; " <> primCall "_arg" <> "; })"
           else primCall v
      Once.IR.StringLit s -> generateStringLit alloc s
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      Once.IR.Let x' e1 e2 ->
        let e1Code = generateIRExpr alloc pairVars retTy e1 v
            newPairVars = if yieldsPairPointer2 e1 then Set.insert x' pairVars else pairVars
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> generateIRExpr alloc newPairVars retTy e2 x' <> "; })"

    -- Check if type contains TArray/TBuffer (which need special handling due to type erasure)
    needsUnpacking :: Type -> Bool
    needsUnpacking ty = case ty of
      TArray _ -> True
      TBuffer -> True
      TProduct a b -> needsUnpacking a || needsUnpacking b
      TArrow dom _ -> needsUnpacking dom
      TEff dom _ -> needsUnpacking dom
      _ -> False

    -- Unpack product types into separate C function arguments
    -- Only for primitives containing Array/Buffer types
    unpackArgs :: Type -> Text -> Text
    unpackArgs ty val
      | needsUnpacking ty = unpackArgsImpl ty val
      | otherwise = val  -- Keep as single OncePair for scalar types

    unpackArgsImpl :: Type -> Text -> Text
    unpackArgsImpl ty val = case ty of
      -- Nested pair: .snd is stored as a pointer, need to dereference
      TProduct a b@(TProduct _ _) ->
        let sndExpr = "(*(OncePair*)(" <> val <> ".snd))"
        in unpackArgsImpl a (val <> ".fst") <> ", " <> unpackArgsImpl b sndExpr
      -- Simple pair: both elements stored directly
      TProduct a b -> unpackArgsImpl a (val <> ".fst") <> ", " <> unpackArgsImpl b (val <> ".snd")
      TArrow dom _ -> unpackArgsImpl dom val
      TEff dom _ -> unpackArgsImpl dom val
      -- Base types: cast from intptr_t to correct C type
      TInt -> "(int64_t)(" <> val <> ")"
      TFloat -> "(double)(" <> val <> ")"
      TByte -> "(uint8_t)(" <> val <> ")"
      TArray _ -> "(OnceBuffer)(" <> val <> ")"
      TBuffer -> "(OnceBuffer)(" <> val <> ")"
      TString _ -> "(OnceString)(" <> val <> ")"
      _ -> val

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
      TInt -> "int64_t"
      TFloat -> "double"
      TByte -> "uint8_t"
      TBuffer -> "OnceBuffer"
      TArray _ -> "OnceBuffer"  -- D042: Array erases to Buffer
      TString _ -> "OnceString"
      TProduct _ _ -> "OncePair"
      TSum _ _ -> "OnceSum"
      TArrow _ _ -> "void*"
      TEff _ _ -> "void*"  -- D032: Eff same as Arrow at runtime
      TApp _ _ -> "void*"
      TFix _ -> "void*"

    -- D046: Get C type for primitive array element types
    -- Returns Nothing for unsupported types (Phase 2: compound types)
    -- Also handles TVar for common type names that weren't substituted
    elementCType :: Type -> Maybe Text
    elementCType TInt = Just "int64_t"
    elementCType TFloat = Just "double"
    elementCType TByte = Just "uint8_t"
    -- Fallback for unsubstituted type variables - default to Int for Phase 1
    -- This is a workaround until we propagate instantiated types through elaboration
    elementCType (TVar _) = Just "int64_t"
    elementCType _ = Nothing  -- Unsupported in Phase 1

    -- D046: Get element size (as Text) for primitive array element types
    -- Used for length calculation: len_bytes / element_size
    elementSize :: Type -> Maybe Text
    elementSize TInt = Just "8"
    elementSize TFloat = Just "8"
    elementSize TByte = Just "1"
    -- Fallback for unsubstituted type variables - default to Int for Phase 1
    elementSize (TVar _) = Just "8"
    elementSize _ = Nothing  -- Unsupported in Phase 1

-- | Generate library header and source for multiple functions (no main required)
generateLibraryAll :: [(Text, Type, Maybe AllocStrategy, Once.IR.IR)] -> (Text, Text)
generateLibraryAll functions = (header, source)
  where
    header = T.unlines $
      [ "/* Generated by Once compiler */"
      , "#pragma once"
      , "#include <stddef.h>"
      , "#include <stdint.h>"
      , ""
      , "/* Type definitions */"
      , "#ifndef ONCE_TYPES_DEFINED"
      , "#define ONCE_TYPES_DEFINED"
      , "typedef struct { char* data; size_t len; } OnceString;"
      , "typedef struct { char* data; size_t len; } OnceBuffer;"
      , "typedef struct { intptr_t fst; intptr_t snd; } OncePair;"
      , "typedef struct { int tag; intptr_t value; } OnceSum;"
      , "#endif"
      , ""
      , "/* Function declarations */"
      ] ++ map funcDecl functions

    source = T.unlines $
      [ "/* Generated by Once compiler */"
      , "#include <stddef.h>"
      , "#include <stdint.h>"
      , ""
      , "/* Type definitions */"
      , "#ifndef ONCE_TYPES_DEFINED"
      , "#define ONCE_TYPES_DEFINED"
      , "typedef struct { char* data; size_t len; } OnceString;"
      , "typedef struct { char* data; size_t len; } OnceBuffer;"
      , "typedef struct { intptr_t fst; intptr_t snd; } OncePair;"
      , "typedef struct { int tag; intptr_t value; } OnceSum;"
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
    funcDef globalAlloc (name, ty, localAlloc, ir) =
      -- D039: If function body is a Curry, use its variable name for the parameter
      let (paramName, body) = case ir of
            Once.IR.Curry varName bodyIR -> (varName, bodyIR)
            _ -> ("x", ir)
          alloc = localAlloc <|> globalAlloc
      in case ty of
        TArrow inTy outTy ->
          libCTypeName outTy <> " once_" <> name <> "(" <> libCTypeName inTy <> " " <> paramName <> ") {\n" <>
          "    return " <> libGenerateIRExpr alloc Set.empty body paramName <> ";\n" <>
          "}"
        TEff inTy outTy ->
          libCTypeName outTy <> " once_" <> name <> "(" <> libCTypeName inTy <> " " <> paramName <> ") {\n" <>
          "    return " <> libGenerateIRExpr alloc Set.empty body paramName <> ";\n" <>
          "}"
        _ -> "/* " <> name <> " has non-function type */"

    libCTypeName :: Type -> Text
    libCTypeName t = case t of
      TVar _ -> "void*"
      TUnit -> "void*"
      TVoid -> "void"
      TInt -> "int64_t"
      TFloat -> "double"
      TByte -> "uint8_t"
      TBuffer -> "OnceBuffer"
      TArray _ -> "OnceBuffer"  -- D042: Array erases to Buffer
      TString _ -> "OnceString"
      TProduct _ _ -> "OncePair"
      TSum _ _ -> "OnceSum"
      TArrow _ _ -> "void*"
      TEff _ _ -> "void*"
      TApp _ _ -> "void*"
      TFix _ -> "void*"

    -- Check if an IR expression might produce an aggregate (OncePair)
    -- This is conservative: if we're unsure, return True to avoid invalid casts.
    -- Can't cast OncePair struct to intptr_t, so we must not cast these.
    -- Used for Case expressions where casting an aggregate would be an error.
    libIsPairIR :: Once.IR.IR -> Bool
    libIsPairIR (Once.IR.Pair _ _) = True  -- Definitely a pair
    libIsPairIR (Once.IR.Let _ _ e2) = libIsPairIR e2  -- Let returns e2
    libIsPairIR (Once.IR.Curry _ body) = libIsPairIR body  -- Curry evaluates body
    libIsPairIR (Once.IR.Case l r) = libIsPairIR l || libIsPairIR r  -- Either branch might be pair
    libIsPairIR (Once.IR.Compose g _) = libIsPairIR g  -- Compose returns g's result
    libIsPairIR (Once.IR.Var _) = True  -- Function calls might return pairs - be conservative
    libIsPairIR (Once.IR.LocalVar _) = True  -- Variables might hold pairs - be conservative
    libIsPairIR _ = False

    -- Check if an IR expression DEFINITELY produces a new pair value that needs heap allocation.
    -- This is structural: only returns True for Pair constructors, not for Var/LocalVar
    -- which might already hold heap-allocated pair pointers.
    libConstructsPair :: Once.IR.IR -> Bool
    libConstructsPair (Once.IR.Pair _ _) = True  -- Definitely constructs a pair
    libConstructsPair (Once.IR.Let _ _ e2) = libConstructsPair e2  -- Let returns e2
    libConstructsPair (Once.IR.Curry _ body) = libConstructsPair body  -- Curry evaluates body
    libConstructsPair (Once.IR.Case l r) = libConstructsPair l || libConstructsPair r  -- Either branch might construct pair
    libConstructsPair (Once.IR.Compose g _) = libConstructsPair g  -- Compose returns g's result
    libConstructsPair _ = False  -- Var/LocalVar don't construct new pairs, they reference existing values

    -- Wrap expressions for OncePair fields
    -- Nested pairs need to be heap-allocated since OncePair.snd is intptr_t
    -- OnceBuffer/OnceString values need to be cast to intptr_t
    libWrapForPair :: Once.IR.IR -> Text -> Text
    libWrapForPair ir expr
      | libConstructsPair ir = "({ OncePair* _tmp = malloc(sizeof(OncePair)); *_tmp = " <> expr <> "; (intptr_t)_tmp; })"
      | libYieldsPointerType ir = "(intptr_t)(" <> expr <> ")"
      | otherwise = expr

    -- Check if an IR expression might yield a pointer type (OnceBuffer, OnceString)
    libYieldsPointerType :: Once.IR.IR -> Bool
    libYieldsPointerType ir = case ir of
      Once.IR.Prim _ _ outTy -> libIsPointerType outTy
      Once.IR.Var _ -> True  -- Function calls might return pointers
      Once.IR.LocalVar _ -> True  -- Variables might hold pointers
      Once.IR.Compose g _ -> libYieldsPointerType g  -- Check the final result
      _ -> False

    libIsPointerType :: Type -> Bool
    libIsPointerType TBuffer = True
    libIsPointerType (TString _) = True
    libIsPointerType (TArray _) = True
    libIsPointerType _ = False

    -- Check if an expression looks like nested pair access or is a known pair variable
    libIsPairAccess :: Set Text -> Text -> Bool
    libIsPairAccess pairVars expr =
      ".snd" `T.isSuffixOf` expr ||
      ".fst" `T.isSuffixOf` expr ||
      expr `Set.member` pairVars

    -- Check if an expression might yield a POINTER to a pair (for dereferencing)
    libYieldsPairPointer :: Once.IR.IR -> Bool
    libYieldsPairPointer (Once.IR.Snd _ _) = True
    libYieldsPairPointer (Once.IR.Fst _ _) = True
    libYieldsPairPointer (Once.IR.Compose g _) = libYieldsPairPointer g
    libYieldsPairPointer _ = False

    libGenerateIRExpr :: Maybe AllocStrategy -> Set Text -> Once.IR.IR -> Text -> Text
    libGenerateIRExpr alloc pairVars ir v = case ir of
      Once.IR.Id _ -> v
      Once.IR.Fst _ _ ->
        if libIsPairAccess pairVars v
        then "(*(OncePair*)(" <> v <> ")).fst"
        else v <> ".fst"
      Once.IR.Snd _ _ ->
        if libIsPairAccess pairVars v
        then "(*(OncePair*)(" <> v <> ")).snd"
        else v <> ".snd"
      Once.IR.Pair f g ->
        let fExpr = libGenerateIRExpr alloc pairVars f v
            gExpr = libGenerateIRExpr alloc pairVars g v
        in "(OncePair){ .fst = " <> libWrapForPair f fExpr <> ", .snd = " <> libWrapForPair g gExpr <> " }"
      Once.IR.Compose g f -> libGenerateIRExpr alloc pairVars g (libGenerateIRExpr alloc pairVars f v)
      Once.IR.Terminal _ -> "((void*)0)"
      Once.IR.Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> v <> " }"
      Once.IR.Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> v <> " }"
      -- For Case expressions: if either branch produces an aggregate (OncePair),
      -- don't cast. Otherwise cast both to intptr_t for pointer type compatibility.
      Once.IR.Case l r ->
        let lExpr = libGenerateIRExpr alloc pairVars l (v <> ".value")
            rExpr = libGenerateIRExpr alloc pairVars r (v <> ".value")
        in if libIsPairIR l || libIsPairIR r
           then "(" <> v <> ".tag == 0 ? " <> lExpr <> " : " <> rExpr <> ")"
           else "(" <> v <> ".tag == 0 ? (intptr_t)(" <> lExpr <> ") : (intptr_t)(" <> rExpr <> "))"
      Once.IR.Initial _ -> v
      -- D039: Curry inside expression (e.g., case branches) needs to bind the variable
      Once.IR.Curry varName body ->
        "({ typeof(" <> v <> ") " <> varName <> " = " <> v <> "; " <> libGenerateIRExpr alloc pairVars body varName <> "; })"
      Once.IR.Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"
      Once.IR.Var n' -> "once_" <> n' <> "(" <> v <> ")"
      Once.IR.LocalVar n' -> n'  -- Local variable (let binding or lambda param)
      Once.IR.FunRef n' -> "(void*)once_" <> n'
      -- Integer literals: __int_N -> just the number
      Once.IR.Prim n' _ TInt | "__int_" `T.isPrefixOf` n' ->
        let numStr = T.drop 6 n'  -- drop "__int_" prefix
        in "((int64_t)" <> numStr <> ")"
      -- Generic array read: read : Array A * Int -> A
      Once.IR.Prim "read" (TArrow (TProduct (TArray elemTy) TInt) _) _ ->
        case libElementCType elemTy of
          Just cType ->
            "({ OncePair _arg = " <> v <> "; " <>
            "((" <> cType <> "*)((OnceBuffer)_arg.fst)->data)[(int64_t)_arg.snd]; })"
          Nothing -> error $ "Unsupported array element type for read: " ++ show elemTy
      -- Generic array write: write : Array A * (Int * A) -> Array A
      Once.IR.Prim "write" (TArrow (TProduct (TArray elemTy) (TProduct TInt _)) _) _ ->
        case libElementCType elemTy of
          Just cType ->
            "({ OncePair _arg = " <> v <> "; " <>
            "OncePair* _iv = (OncePair*)_arg.snd; " <>
            "((" <> cType <> "*)((OnceBuffer)_arg.fst)->data)[(int64_t)_iv->fst] = (" <> cType <> ")_iv->snd; " <>
            "(OnceBuffer)_arg.fst; })"
          Nothing -> error $ "Unsupported array element type for write: " ++ show elemTy
      -- Generic array length: length : Array A -> Int
      Once.IR.Prim "length" (TArrow (TArray elemTy) TInt) _ ->
        case libElementSize elemTy of
          Just size ->
            "(int64_t)(((OnceBuffer)" <> v <> ")->len / " <> size <> ")"
          Nothing -> error $ "Unsupported array element type for length: " ++ show elemTy
      -- Primitives: unpack product types into separate C function arguments
      -- When dealing with complex argument expressions (inline pairs with malloc),
      -- bind to a temporary variable first to avoid duplicating the expression
      Once.IR.Prim n' inTy _ ->
        let primCall argExpr = "once_" <> n' <> "(" <> libUnpackArgs inTy argExpr <> ")"
            isComplex = T.any (\c -> c == '{' || c == '(') v && libNeedsUnpacking inTy
        in if isComplex
           then "({ OncePair _arg = " <> v <> "; " <> primCall "_arg" <> "; })"
           else primCall v
      Once.IR.StringLit s -> libGenerateStringLit alloc s
      Once.IR.Fold _ -> v
      Once.IR.Unfold _ -> v
      Once.IR.Let x' e1 e2 ->
        let e1Code = libGenerateIRExpr alloc pairVars e1 v
            newPairVars = if libYieldsPairPointer e1 then Set.insert x' pairVars else pairVars
        in "({ typeof(" <> e1Code <> ") " <> x' <> " = " <> e1Code <> "; " <> libGenerateIRExpr alloc newPairVars e2 x' <> "; })"

    -- Check if type contains TArray/TBuffer (which need special handling due to type erasure)
    libNeedsUnpacking :: Type -> Bool
    libNeedsUnpacking ty = case ty of
      TArray _ -> True
      TBuffer -> True
      TProduct a b -> libNeedsUnpacking a || libNeedsUnpacking b
      TArrow dom _ -> libNeedsUnpacking dom
      TEff dom _ -> libNeedsUnpacking dom
      _ -> False

    -- Unpack product types into separate C function arguments
    -- Only for primitives containing Array/Buffer types
    libUnpackArgs :: Type -> Text -> Text
    libUnpackArgs ty val
      | libNeedsUnpacking ty = libUnpackArgsImpl ty val
      | otherwise = val  -- Keep as single OncePair for scalar types

    libUnpackArgsImpl :: Type -> Text -> Text
    libUnpackArgsImpl ty val = case ty of
      -- Nested pair: .snd is stored as a pointer, need to dereference
      TProduct a b@(TProduct _ _) ->
        let sndExpr = "(*(OncePair*)(" <> val <> ".snd))"
        in libUnpackArgsImpl a (val <> ".fst") <> ", " <> libUnpackArgsImpl b sndExpr
      -- Simple pair: both elements stored directly
      TProduct a b -> libUnpackArgsImpl a (val <> ".fst") <> ", " <> libUnpackArgsImpl b (val <> ".snd")
      TArrow dom _ -> libUnpackArgsImpl dom val
      TEff dom _ -> libUnpackArgsImpl dom val
      -- Base types: cast from intptr_t to correct C type
      TInt -> "(int64_t)(" <> val <> ")"
      TFloat -> "(double)(" <> val <> ")"
      TByte -> "(uint8_t)(" <> val <> ")"
      TArray _ -> "(OnceBuffer)(" <> val <> ")"
      TBuffer -> "(OnceBuffer)(" <> val <> ")"
      TString _ -> "(OnceString)(" <> val <> ")"
      _ -> val

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

    -- D046: Get C type for primitive array element types (library mode)
    libElementCType :: Type -> Maybe Text
    libElementCType TInt = Just "int64_t"
    libElementCType TFloat = Just "double"
    libElementCType TByte = Just "uint8_t"
    libElementCType (TVar _) = Just "int64_t"  -- Fallback for unsubstituted type vars
    libElementCType _ = Nothing

    -- D046: Get element size for primitive array element types (library mode)
    libElementSize :: Type -> Maybe Text
    libElementSize TInt = Just "8"
    libElementSize TFloat = Just "8"
    libElementSize TByte = Just "1"
    libElementSize (TVar _) = Just "8"  -- Fallback for unsubstituted type vars
    libElementSize _ = Nothing
