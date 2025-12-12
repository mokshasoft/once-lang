module Once.CLI
  ( run
  , Command (..)
  , BuildOptions (..)
  , CheckOptions (..)
  , OutputMode (..)
  , AllocStrategy (..)
  ) where

import Control.Applicative ((<|>))
import Data.List (isSuffixOf)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (listDirectory)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeBaseName, (</>))

import Once.Backend.C (generateC, CModule (..))
import Once.Elaborate (elaborate)
import qualified Once.IR (IR (..))
import Once.Optimize (optimize)
import Once.Parser (parseModule)
import Once.Syntax (Module (..), Decl (..), Expr, AllocStrategy (..))
import Once.Type (Type (..))
import Once.TypeCheck (checkModule, convertType)

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

-- | Options for the build command
data BuildOptions = BuildOptions
  { buildInput  :: FilePath
  , buildOutput :: Maybe FilePath       -- ^ Output base name (without extension)
  , buildMode   :: OutputMode           -- ^ Library or executable
  , buildInterp :: Maybe FilePath       -- ^ Path to interpretation directory
  , buildAlloc  :: Maybe AllocStrategy  -- ^ Default allocation strategy (Nothing = use per-function annotations)
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

-- | Run the build command: parse -> typecheck -> elaborate -> optimize -> codegen
runBuild :: BuildOptions -> IO ()
runBuild opts = do
  let inputPath = buildInput opts
      outputBase = case buildOutput opts of
        Just base -> base
        Nothing -> takeBaseName inputPath
      mode = buildMode opts

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
          -- Extract primitives and all function definitions
          let primitives = extractPrimitives m
              allFunctions = extractFunctions m

          -- Find main function
          case filter (\(n, _, _, _) -> n == "main") allFunctions of
            [] -> do
              TIO.putStrLn "Error: No main function found"
              exitFailure
            ((mainName, mainTy, mainAlloc, mainExpr):_) -> do
              -- Elaborate all functions to IR
              let otherFunctions = filter (\(n, _, _, _) -> n /= "main") allFunctions
              case elaborateAll ((mainName, mainTy, mainAlloc, mainExpr) : otherFunctions) of
                Left err -> do
                  TIO.putStrLn $ "Elaboration error: " <> T.pack (show err)
                  exitFailure
                Right irFunctions -> do
                  -- Optimize all IRs
                  let optimizedFunctions = [(n, t, a, optimize ir) | (n, t, a, ir) <- irFunctions]
                      (_, _, _, mainIR) = head optimizedFunctions

                  -- Generate C based on mode
                  case mode of
                    Library -> do
                      let CModule header source' = generateC mainName mainTy mainIR
                          headerPath = outputBase ++ ".h"
                          sourcePath = outputBase ++ ".c"
                      TIO.writeFile headerPath header
                      TIO.writeFile sourcePath source'
                      TIO.putStrLn $ "Generated: " <> T.pack headerPath <> ", " <> T.pack sourcePath

                    Executable -> do
                      -- For executable, generate C with main() wrapper
                      -- Load all interpretation C code if provided
                      interpCode <- case buildInterp opts of
                        Nothing -> pure ""
                        Just interpPath -> loadInterpretationCode interpPath

                      let sourcePath = outputBase ++ ".c"
                          alloc = mainAlloc <|> buildAlloc opts
                          source' = generateExecutableAll optimizedFunctions alloc primitives interpCode
                      TIO.writeFile sourcePath source'
                      TIO.putStrLn $ "Generated: " <> T.pack sourcePath

                  exitSuccess

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
      TApp _ _ -> "void*"
      TFix _ -> "void*"
