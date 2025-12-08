module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), OutputMode (..))

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Nothing -> usage
    Just cmd -> run cmd

-- | Parse command-line arguments
parseArgs :: [String] -> Maybe Command
parseArgs ("build" : rest) = parseBuild rest
parseArgs ("check" : rest) = parseCheck rest
parseArgs _ = Nothing

-- | Parse build command arguments
parseBuild :: [String] -> Maybe Command
parseBuild args = go args Nothing Library Nothing
  where
    -- go remaining output mode input
    go :: [String] -> Maybe String -> OutputMode -> Maybe String -> Maybe Command
    go [] _ _ Nothing = Nothing  -- no input file
    go [] output mode (Just input) = Just $ Build BuildOptions
      { buildInput = input
      , buildOutput = output
      , buildMode = mode
      }
    go ("-o" : out : rest) _ mode input = go rest (Just out) mode input
    go ("--lib" : rest) output _ input = go rest output Library input
    go ("--exe" : rest) output _ input = go rest output Executable input
    go (x : rest) output mode _input = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest output mode (Just x)  -- treat as input file

-- | Parse check command arguments
parseCheck :: [String] -> Maybe Command
parseCheck args = case args of
  [input] -> Just $ Check CheckOptions
    { checkInput = input
    }
  _ -> Nothing

-- | Print usage information
usage :: IO ()
usage = do
  TIO.putStrLn "Usage: once <command> [options]"
  TIO.putStrLn ""
  TIO.putStrLn "Commands:"
  TIO.putStrLn "  build [--lib|--exe] <file.once> [-o <output>]"
  TIO.putStrLn "        --lib    Generate C library (header + source) [default]"
  TIO.putStrLn "        --exe    Generate standalone executable"
  TIO.putStrLn "  check <file.once>                Type check only"
  exitFailure
