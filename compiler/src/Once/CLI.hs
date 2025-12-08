module Once.CLI
  ( run
  , Command (..)
  , BuildOptions (..)
  , CheckOptions (..)
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (exitFailure, exitSuccess)
import System.FilePath (takeBaseName)

import Once.Backend.C (generateC, CModule (..))
import Once.Elaborate (elaborate)
import Once.Optimize (optimize)
import Once.Parser (parseModule)
import Once.Syntax (Module (..), Decl (..), Expr)
import Once.Type (Type)
import Once.TypeCheck (checkModule, convertType)

-- | CLI commands
data Command
  = Build BuildOptions
  | Check CheckOptions
  deriving (Eq, Show)

-- | Options for the build command
data BuildOptions = BuildOptions
  { buildInput  :: FilePath
  , buildOutput :: Maybe FilePath  -- ^ Output base name (without extension)
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
          -- Find the function definition and its type
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

                  -- Generate C
                  let CModule header source' = generateC name ty optimizedIR
                      headerPath = outputBase ++ ".h"
                      sourcePath = outputBase ++ ".c"

                  -- Write output files
                  TIO.writeFile headerPath header
                  TIO.writeFile sourcePath source'

                  TIO.putStrLn $ "Generated: " <> T.pack headerPath <> ", " <> T.pack sourcePath
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
