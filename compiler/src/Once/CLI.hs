module Once.CLI
  ( run
  , Command (..)
  , BuildOptions (..)
  , CheckOptions (..)
  , OutputMode (..)
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeBaseName)

import Once.Backend.C (generateC, CModule (..))
import Once.Elaborate (elaborate)
import qualified Once.IR (IR (..))
import Once.Optimize (optimize)
import Once.Parser (parseModule)
import Once.Syntax (Module (..), Decl (..), Expr)
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
  , buildOutput :: Maybe FilePath  -- ^ Output base name (without extension)
  , buildMode   :: OutputMode      -- ^ Library or executable
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
          -- Extract primitives and function definition
          let primitives = extractPrimitives m
          case extractFunction m of
            Nothing -> do
              TIO.putStrLn "Error: No function definition found"
              exitFailure
            Just (name, ty, expr) -> do
              -- Elaborate to IR
              case elaborate expr of
                Left err -> do
                  TIO.putStrLn $ "Elaboration error: " <> T.pack (show err)
                  exitFailure
                Right ir -> do
                  -- Optimize
                  let optimizedIR = optimize ir

                  -- Generate C based on mode
                  case mode of
                    Library -> do
                      let CModule header source' = generateC name ty optimizedIR
                          headerPath = outputBase ++ ".h"
                          sourcePath = outputBase ++ ".c"
                      TIO.writeFile headerPath header
                      TIO.writeFile sourcePath source'
                      TIO.putStrLn $ "Generated: " <> T.pack headerPath <> ", " <> T.pack sourcePath

                    Executable -> do
                      -- For executable, generate C with main() wrapper
                      let sourcePath = outputBase ++ ".c"
                          source' = generateExecutable name ty optimizedIR primitives
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

-- | Extract all primitives from a module
-- Returns list of (name, type)
extractPrimitives :: Module -> [(Text, Type)]
extractPrimitives (Module decls) =
  [ (name, convertType sty) | Primitive name sty <- decls ]

-- | Extract the first function definition from a module
-- Returns (name, type, expression)
extractFunction :: Module -> Maybe (Text, Type, Expr)
extractFunction (Module decls) = go decls Nothing
  where
    go [] _ = Nothing
    go (TypeSig name sty : FunDef name' expr : rest) _
      | name == name' = Just (name, convertType sty, expr)
      | otherwise = go rest Nothing
    go (TypeSig name sty : rest) _ = go rest (Just (name, sty))
    go (_ : rest) ctx = go rest ctx

-- | Generate C code for an executable (with main function)
generateExecutable :: Text -> Type -> Once.IR.IR -> [(Text, Type)] -> Text
generateExecutable name ty ir primitives = T.unlines
  [ "/* Generated by Once compiler */"
  , "#include <stdlib.h>"
  , ""
  , "/* Primitive declarations */"
  , primDecls
  , ""
  , "/* Once function */"
  , onceFuncCode name ty ir
  , ""
  , "/* Main entry point */"
  , "int main(void) {"
  , "    once_" <> name <> "(((void*)0));"
  , "    return 0;"
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
      Once.IR.Var n' -> n' <> "(" <> v <> ")"
      Once.IR.Prim n' _ _ -> n' <> "(" <> v <> ")"

    -- Generate primitive declarations/implementations
    primDecls = T.unlines $ map primDecl primitives

    primDecl :: (Text, Type) -> Text
    primDecl (pname, pty) = case pty of
      TArrow inTy outTy ->
        -- Generate implementation for known primitives
        if pname == "exit0"
          then T.unlines
            [ cTypeName outTy <> " " <> pname <> "(" <> cTypeName inTy <> " x) {"
            , "    (void)x;"
            , "    exit(0);"
            , "    return ((void*)0);"
            , "}"
            ]
          else
            -- Unknown primitive - just declare it as extern
            "extern " <> cTypeName outTy <> " " <> pname <> "(" <> cTypeName inTy <> " x);"
      _ -> "/* primitive " <> pname <> " has non-function type */"

    cTypeName :: Type -> Text
    cTypeName t = case t of
      TVar _ -> "void*"
      TUnit -> "void*"
      TVoid -> "void"
      TInt -> "int"
      TProduct _ _ -> "OncePair"
      TSum _ _ -> "OnceSum"
      TArrow _ _ -> "void*"
