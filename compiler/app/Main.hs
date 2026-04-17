module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Data.List (isPrefixOf, stripPrefix)
import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), ParseOptions (..), OutputMode (..), Target (..), AllocStrategy (..), InterpType (..), parseTarget, parseInterpType)

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
parseArgs ("parse" : rest) = parseParse rest
parseArgs _ = Nothing

-- | Parse parse command arguments
parseParse :: [String] -> Maybe Command
parseParse [file] = Just $ Parse ParseOptions { parseInput = file }
parseParse _ = Nothing

-- | Parse check command arguments
parseCheck :: [String] -> Maybe Command
parseCheck [file] = Just $ Check CheckOptions { checkInput = file }
parseCheck _ = Nothing

-- | Build configuration state for parsing
data BuildConfig = BuildConfig
  { bcOutput    :: Maybe String
  , bcMode      :: OutputMode
  , bcTarget    :: Target
  , bcSaveTemps :: Bool
  , bcOptimize  :: Bool
  , bcStrata    :: Maybe String
  , bcAlloc     :: Maybe AllocStrategy
  , bcInterp    :: Maybe String
  , bcExplicit  :: [(InterpType, String)]
  , bcInput     :: Maybe String
  }

defaultBuildConfig :: BuildConfig
defaultBuildConfig = BuildConfig
  { bcOutput    = Nothing
  , bcMode      = Library
  , bcTarget    = TargetC
  , bcSaveTemps = False
  , bcOptimize  = True
  , bcStrata    = Nothing
  , bcAlloc     = Nothing
  , bcInterp    = Nothing
  , bcExplicit  = []
  , bcInput     = Nothing
  }

-- | Parse allocation strategy from string
parseAllocStrategy :: String -> Maybe AllocStrategy
parseAllocStrategy "stack" = Just AllocStack
parseAllocStrategy "heap"  = Just AllocHeap
parseAllocStrategy "pool"  = Just AllocPool
parseAllocStrategy "arena" = Just AllocArena
parseAllocStrategy "const" = Just AllocConst
parseAllocStrategy _       = Nothing

-- | Parse build command arguments
parseBuild :: [String] -> Maybe Command
parseBuild args = go args defaultBuildConfig
  where
    go :: [String] -> BuildConfig -> Maybe Command
    go [] cfg = case bcInput cfg of
      Nothing -> Nothing  -- no input file
      Just input -> Just $ Build BuildOptions
        { buildInput     = input
        , buildOutput    = bcOutput cfg
        , buildMode      = bcMode cfg
        , buildTarget    = bcTarget cfg
        , buildSaveTemps = bcSaveTemps cfg
        , buildOptimize  = bcOptimize cfg
        , buildStrata    = bcStrata cfg
        , buildAlloc     = bcAlloc cfg
        , buildInterp    = bcInterp cfg
        , buildExplicitInterps = bcExplicit cfg
        }
    go ("-o" : out : rest) cfg = go rest cfg { bcOutput = Just out }
    go ("--lib" : rest) cfg = go rest cfg { bcMode = Library }
    go ("--exe" : rest) cfg = go rest cfg { bcMode = Executable }
    go ("--target" : t : rest) cfg = case parseTarget t of
      Just target -> go rest cfg { bcTarget = target }
      Nothing -> Nothing  -- invalid target
    go ("--save-temps" : rest) cfg = go rest cfg { bcSaveTemps = True }
    go ("--no-optimize" : rest) cfg = go rest cfg { bcOptimize = False }
    go ("--strata" : s : rest) cfg = go rest cfg { bcStrata = Just s }
    go ("--alloc" : a : rest) cfg = case parseAllocStrategy a of
      Just alloc -> go rest cfg { bcAlloc = Just alloc }
      Nothing -> Nothing  -- invalid allocation strategy
    go ("--interp" : i : rest) cfg = go rest cfg { bcInterp = Just i }
    -- Parse -I:TYPE MODULE (explicit interpretation with type)
    go (x : modPath : rest) cfg
      | "-I:" `isPrefixOf` x =
          case stripPrefix "-I:" x >>= parseInterpType of
            Just itype -> go rest cfg { bcExplicit = bcExplicit cfg ++ [(itype, modPath)] }
            Nothing -> Nothing  -- invalid interpretation type
    go (x : rest) cfg = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest cfg { bcInput = Just x }  -- treat as input file

-- | Print usage information
usage :: IO ()
usage = do
  TIO.putStrLn "Usage: once <command> [options]"
  TIO.putStrLn ""
  TIO.putStrLn "Commands:"
  TIO.putStrLn "  parse <file.once>             Parse only (show function signatures)"
  TIO.putStrLn "  check <file.once>             Parse and type check"
  TIO.putStrLn "  build [options] <file.once>   Full compile (parse, check, codegen)"
  TIO.putStrLn ""
  TIO.putStrLn "Build options:"
  TIO.putStrLn "  -o OUTPUT           Output base name (default: input file name)"
  TIO.putStrLn "  --lib               Generate library [default]"
  TIO.putStrLn "  --exe               Generate standalone executable"
  TIO.putStrLn "  --target ARCH       Target architecture (c|x86_64|arm64|riscv64) [default: c]"
  TIO.putStrLn "  --save-temps        Keep intermediate files (.s, .o)"
  TIO.putStrLn "  --no-optimize       Skip optimizer"
  TIO.putStrLn "  --strata PATH       Path to Strata directory for imports"
  TIO.putStrLn "  --alloc STRATEGY    Default allocation strategy (stack|heap|pool|arena|const)"
  TIO.putStrLn "  --interp PATH       Interpretation path (deprecated)"
  TIO.putStrLn "  -I:TYPE MODULE      Link interpretation (e.g., -I:C I.Linux.Syscalls)"
  TIO.putStrLn ""
  TIO.putStrLn "Target architectures:"
  TIO.putStrLn "  c       - C backend (not yet implemented)"
  TIO.putStrLn "  x86_64  - x86-64 native (verified via MAlonzo)"
  TIO.putStrLn "  arm64   - ARM64 native (not yet implemented)"
  TIO.putStrLn "  riscv64 - RISC-V 64-bit (not yet implemented)"
  exitFailure
