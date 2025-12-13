module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), OutputMode (..), AllocStrategy (..), Target (..), parseTarget)

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
parseBuild args = go args Nothing Library Nothing Nothing Nothing TargetC Nothing
  where
    -- go remaining output mode interp alloc strata target input
    go :: [String] -> Maybe String -> OutputMode -> Maybe String -> Maybe AllocStrategy -> Maybe String -> Target -> Maybe String -> Maybe Command
    go [] _ _ _ _ _ _ Nothing = Nothing  -- no input file
    go [] output mode interp alloc strata target (Just input) = Just $ Build BuildOptions
      { buildInput = input
      , buildOutput = output
      , buildMode = mode
      , buildInterp = interp
      , buildAlloc = alloc
      , buildStrata = strata
      , buildTarget = target
      }
    go ("-o" : out : rest) _ mode interp alloc strata target input = go rest (Just out) mode interp alloc strata target input
    go ("--lib" : rest) output _ interp alloc strata target input = go rest output Library interp alloc strata target input
    go ("--exe" : rest) output _ interp alloc strata target input = go rest output Executable interp alloc strata target input
    go ("--interp" : i : rest) output mode _ alloc strata target input = go rest output mode (Just i) alloc strata target input
    go ("--strata" : s : rest) output mode interp alloc _ target input = go rest output mode interp alloc (Just s) target input
    go ("--target" : t : rest) output mode interp alloc strata _ input = case parseTarget t of
      Just target -> go rest output mode interp alloc strata target input
      Nothing -> Nothing  -- invalid target
    go ("--alloc" : a : rest) output mode interp _ strata target input = case parseAllocStrategy a of
      Just alloc -> go rest output mode interp (Just alloc) strata target input
      Nothing -> Nothing  -- invalid allocation strategy
    go (x : rest) output mode interp alloc strata target _input = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest output mode interp alloc strata target (Just x)  -- treat as input file

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
  TIO.putStrLn "  build [--lib|--exe] [--target <arch>] [--strata <path>] [--alloc <strategy>] <file.once> [-o <output>]"
  TIO.putStrLn "        --lib             Generate C library (header + source) [default]"
  TIO.putStrLn "        --exe             Generate standalone executable"
  TIO.putStrLn "        --target ARCH     Target architecture (c|x86_64|arm64|riscv64) [default: c]"
  TIO.putStrLn "        --strata PATH     Path to Strata directory for imports (default: auto-detect)"
  TIO.putStrLn "        --alloc STRATEGY  Default allocation strategy (stack|heap|pool|arena|const)"
  TIO.putStrLn "                          const: read-only data section (works for all pure Once programs)"
  TIO.putStrLn "        --interp PATH     (deprecated) Use interpretation from PATH"
  TIO.putStrLn "  check <file.once>       Type check only"
  TIO.putStrLn ""
  TIO.putStrLn "Import abbreviations:"
  TIO.putStrLn "  I. -> Interpretations.  (e.g., import I.Linux.Syscalls)"
  TIO.putStrLn "  D. -> Derived.          (e.g., import D.Canonical)"
  TIO.putStrLn ""
  TIO.putStrLn "Target architectures:"
  TIO.putStrLn "  c       - C backend (implemented)"
  TIO.putStrLn "  x86_64  - x86-64 assembly (future)"
  TIO.putStrLn "  arm64   - ARM64 assembly (future)"
  TIO.putStrLn "  riscv64 - RISC-V 64-bit (future)"
  exitFailure
