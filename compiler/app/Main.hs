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
parseBuild args = go args Nothing Library Nothing Nothing
  where
    -- go remaining output mode interp input
    go :: [String] -> Maybe String -> OutputMode -> Maybe String -> Maybe String -> Maybe Command
    go [] _ _ _ Nothing = Nothing  -- no input file
    go [] output mode interp (Just input) = Just $ Build BuildOptions
      { buildInput = input
      , buildOutput = output
      , buildMode = mode
      , buildInterp = interp
      }
    go ("-o" : out : rest) _ mode interp input = go rest (Just out) mode interp input
    go ("--lib" : rest) output _ interp input = go rest output Library interp input
    go ("--exe" : rest) output _ interp input = go rest output Executable interp input
    go ("--interp" : i : rest) output mode _ input = go rest output mode (Just i) input
    go (x : rest) output mode interp _input = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest output mode interp (Just x)  -- treat as input file

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
  TIO.putStrLn "  build [--lib|--exe] [--interp <path>] <file.once> [-o <output>]"
  TIO.putStrLn "        --lib          Generate C library (header + source) [default]"
  TIO.putStrLn "        --exe          Generate standalone executable"
  TIO.putStrLn "        --interp PATH  Use interpretation from PATH"
  TIO.putStrLn "  check <file.once>    Type check only"
  exitFailure
