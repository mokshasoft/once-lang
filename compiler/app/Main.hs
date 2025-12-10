module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), OutputMode (..), AllocStrategy (..))

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
parseBuild args = go args Nothing Library Nothing Nothing Nothing
  where
    -- go remaining output mode interp alloc input
    go :: [String] -> Maybe String -> OutputMode -> Maybe String -> Maybe AllocStrategy -> Maybe String -> Maybe Command
    go [] _ _ _ _ Nothing = Nothing  -- no input file
    go [] output mode interp alloc (Just input) = Just $ Build BuildOptions
      { buildInput = input
      , buildOutput = output
      , buildMode = mode
      , buildInterp = interp
      , buildAlloc = alloc
      }
    go ("-o" : out : rest) _ mode interp alloc input = go rest (Just out) mode interp alloc input
    go ("--lib" : rest) output _ interp alloc input = go rest output Library interp alloc input
    go ("--exe" : rest) output _ interp alloc input = go rest output Executable interp alloc input
    go ("--interp" : i : rest) output mode _ alloc input = go rest output mode (Just i) alloc input
    go ("--alloc" : a : rest) output mode interp _ input = case parseAllocStrategy a of
      Just alloc -> go rest output mode interp (Just alloc) input
      Nothing -> Nothing  -- invalid allocation strategy
    go (x : rest) output mode interp alloc _input = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest output mode interp alloc (Just x)  -- treat as input file

-- | Parse allocation strategy from string
parseAllocStrategy :: String -> Maybe AllocStrategy
parseAllocStrategy s = case s of
  "stack" -> Just AllocStack
  "heap"  -> Just AllocHeap
  "pool"  -> Just AllocPool
  "arena" -> Just AllocArena
  "const" -> Just AllocConst
  _       -> Nothing

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
  TIO.putStrLn "  build [--lib|--exe] [--interp <path>] [--alloc <strategy>] <file.once> [-o <output>]"
  TIO.putStrLn "        --lib             Generate C library (header + source) [default]"
  TIO.putStrLn "        --exe             Generate standalone executable"
  TIO.putStrLn "        --interp PATH     Use interpretation from PATH"
  TIO.putStrLn "        --alloc STRATEGY  Default allocation strategy (stack|heap|pool|arena|const)"
  TIO.putStrLn "                          const: read-only data section (works for all pure Once programs)"
  TIO.putStrLn "  check <file.once>       Type check only"
  exitFailure
