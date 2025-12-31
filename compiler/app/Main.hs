module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Data.List (isPrefixOf, stripPrefix)
import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), OutputMode (..), AllocStrategy (..), Target (..), InterpType (..), parseTarget, parseInterpType)
import Once.Optimize (OptimizerBackend (..))

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

-- | Build configuration state for parsing
data BuildConfig = BuildConfig
  { bcOutput     :: Maybe String
  , bcMode       :: OutputMode
  , bcInterp     :: Maybe String
  , bcAlloc      :: Maybe AllocStrategy
  , bcStrata     :: Maybe String
  , bcTarget     :: Target
  , bcOptimizer  :: OptimizerBackend
  , bcSaveTemps  :: Bool
  , bcExplicit   :: [(InterpType, String)]  -- -I:TYPE MODULE
  , bcAutoRes    :: Maybe [InterpType]      -- -A:PRIORITY
  , bcArith      :: Bool                    -- --arith flag
  , bcInput      :: Maybe String
  }

defaultBuildConfig :: BuildConfig
defaultBuildConfig = BuildConfig
  { bcOutput    = Nothing
  , bcMode      = Library
  , bcInterp    = Nothing
  , bcAlloc     = Nothing
  , bcStrata    = Nothing
  , bcTarget    = TargetC
  , bcOptimizer = HaskellOptimizer
  , bcSaveTemps = False
  , bcExplicit  = []
  , bcAutoRes   = Nothing
  , bcArith     = False
  , bcInput     = Nothing
  }

-- | Parse build command arguments
parseBuild :: [String] -> Maybe Command
parseBuild args = go args defaultBuildConfig
  where
    go :: [String] -> BuildConfig -> Maybe Command
    go [] cfg = case bcInput cfg of
      Nothing -> Nothing  -- no input file
      Just input -> Just $ Build BuildOptions
        { buildInput = input
        , buildOutput = bcOutput cfg
        , buildMode = bcMode cfg
        , buildInterp = bcInterp cfg
        , buildAlloc = bcAlloc cfg
        , buildStrata = bcStrata cfg
        , buildTarget = bcTarget cfg
        , buildOptimizer = bcOptimizer cfg
        , buildSaveTemps = bcSaveTemps cfg
        , buildExplicitInterps = bcExplicit cfg
        , buildAutoResolve = bcAutoRes cfg
        , buildArith = bcArith cfg
        }
    go ("-o" : out : rest) cfg = go rest cfg { bcOutput = Just out }
    go ("--lib" : rest) cfg = go rest cfg { bcMode = Library }
    go ("--exe" : rest) cfg = go rest cfg { bcMode = Executable }
    go ("--interp" : i : rest) cfg = go rest cfg { bcInterp = Just i }
    go ("--strata" : s : rest) cfg = go rest cfg { bcStrata = Just s }
    go ("--target" : t : rest) cfg = case parseTarget t of
      Just target -> go rest cfg { bcTarget = target }
      Nothing -> Nothing  -- invalid target
    go ("--alloc" : a : rest) cfg = case parseAllocStrategy a of
      Just alloc -> go rest cfg { bcAlloc = Just alloc }
      Nothing -> Nothing  -- invalid allocation strategy
    go ("--optimizer" : o : rest) cfg = case parseOptimizer o of
      Just opt -> go rest cfg { bcOptimizer = opt }
      Nothing -> Nothing  -- invalid optimizer
    go ("--save-temps" : rest) cfg = go rest cfg { bcSaveTemps = True }
    go ("--arith" : rest) cfg = go rest cfg { bcArith = True }
    -- Parse -I:TYPE MODULE
    go (x : modPath : rest) cfg
      | "-I:" `isPrefixOf` x =
          case stripPrefix "-I:" x >>= parseInterpType of
            Just itype -> go rest cfg { bcExplicit = bcExplicit cfg ++ [(itype, modPath)] }
            Nothing -> Nothing  -- invalid interpretation type
    -- Parse -A:PRIORITY (e.g., -A:C:x86_64)
    go (x : rest) cfg
      | "-A:" `isPrefixOf` x =
          case stripPrefix "-A:" x >>= parseAutoResolve of
            Just priority -> go rest cfg { bcAutoRes = Just priority }
            Nothing -> Nothing  -- invalid auto-resolve priority
    go (x : rest) cfg = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest cfg { bcInput = Just x }  -- treat as input file

-- | Parse auto-resolve priority string (e.g., "C:x86_64" -> [InterpC, InterpX86_64])
parseAutoResolve :: String -> Maybe [InterpType]
parseAutoResolve s = mapM parseInterpType (splitOn ':' s)
  where
    splitOn :: Char -> String -> [String]
    splitOn _ [] = []
    splitOn c str = case break (== c) str of
      (x, [])     -> [x]
      (x, _:rest) -> x : splitOn c rest

-- | Parse optimizer backend from string
parseOptimizer :: String -> Maybe OptimizerBackend
parseOptimizer s = case s of
  "haskell" -> Just HaskellOptimizer
  "malonzo" -> Just MAlonzoOptimizer
  "verified" -> Just MAlonzoOptimizer  -- alias
  _         -> Nothing

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
parseCheck args = go args Nothing Nothing
  where
    go :: [String] -> Maybe String -> Maybe String -> Maybe Command
    go [] _ Nothing = Nothing  -- no input file
    go [] strataPath (Just input) = Just $ Check CheckOptions
      { checkInput = input
      , checkStrata = strataPath
      }
    go ("--strata" : s : rest) _ inputPath = go rest (Just s) inputPath
    go (x : rest) strataPath inputPath = case x of
      ('-':_) -> Nothing  -- unknown flag
      _ -> go rest strataPath (Just x)  -- treat as input file

-- | Print usage information
usage :: IO ()
usage = do
  TIO.putStrLn "Usage: once <command> [options]"
  TIO.putStrLn ""
  TIO.putStrLn "Commands:"
  TIO.putStrLn "  build [options] <file.once> [-o <output>]"
  TIO.putStrLn ""
  TIO.putStrLn "Build options:"
  TIO.putStrLn "  --lib               Generate C library (header + source) [default]"
  TIO.putStrLn "  --exe               Generate standalone executable"
  TIO.putStrLn "  --target ARCH       Target architecture (c|x86_64|arm64|riscv64) [default: c]"
  TIO.putStrLn "  --save-temps        Keep intermediate files (.c, .s, .o)"
  TIO.putStrLn "  --strata PATH       Path to Strata directory for imports (default: auto-detect)"
  TIO.putStrLn "  --alloc STRATEGY    Default allocation strategy (stack|heap|pool|arena|const)"
  TIO.putStrLn "  --optimizer BACKEND Optimizer to use (haskell|malonzo) [default: haskell]"
  TIO.putStrLn "  --arith             Enable arithmetic compiler for pure numeric expressions"
  TIO.putStrLn ""
  TIO.putStrLn "Interpretation resolution:"
  TIO.putStrLn "  -I:TYPE MODULE      Link interpretation (e.g., -I:C I.Linux.Syscalls)"
  TIO.putStrLn "                      TYPE: C, x86_64, arm64, riscv64"
  TIO.putStrLn "                      Extension added automatically based on TYPE"
  TIO.putStrLn "  -A:PRIORITY         Auto-resolve with priority (e.g., -A:C:x86_64)"
  TIO.putStrLn "                      Example: -A:x86_64:C means prefer native, fall back to C"
  TIO.putStrLn ""
  TIO.putStrLn "Legacy options:"
  TIO.putStrLn "  --interp PATH       (deprecated) Use interpretation from PATH"
  TIO.putStrLn ""
  TIO.putStrLn "Other commands:"
  TIO.putStrLn "  check [--strata PATH] <file.once>   Type check only"
  TIO.putStrLn ""
  TIO.putStrLn "Check options:"
  TIO.putStrLn "  --strata PATH       Path to Strata directory for imports (default: auto-detect)"
  TIO.putStrLn ""
  TIO.putStrLn "Import abbreviations:"
  TIO.putStrLn "  I. -> Interpretations.  (e.g., import I.Linux.Syscalls)"
  TIO.putStrLn "  D. -> Derived.          (e.g., import D.Canonical)"
  TIO.putStrLn ""
  TIO.putStrLn "Target architectures:"
  TIO.putStrLn "  c       - C backend (default, full language support)"
  TIO.putStrLn "  x86_64  - x86-64 native"
  TIO.putStrLn "  arm64   - ARM64 native"
  TIO.putStrLn "  riscv64 - RISC-V 64-bit native"
  exitFailure
