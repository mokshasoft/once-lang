module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Data.List (isPrefixOf, stripPrefix)
import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), ParseOptions (..), StageOptions (..), OutputMode (..), Target (..), AllocStrategy (..), InterpType (..), parseTarget, parseInterpType)

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Nothing -> usage
    Just cmd -> run cmd

-- | Parse command-line arguments
parseArgs :: [String] -> Maybe Command
parseArgs ("build"      : rest) = parseBuild rest
parseArgs ("check"      : rest) = parseStageArgs rest >>= \(i, o) ->
                                   Just $ Check CheckOptions { checkInput = i, checkOutput = o }
parseArgs ("parse"      : rest) = parseStageArgs rest >>= \(i, o) ->
                                   Just $ Parse ParseOptions { parseInput = i, parseOutput = o }
parseArgs ("preprocess" : rest) = Preprocess <$> parseStageOpts rest
parseArgs ("elaborate"  : rest) = Elaborate  <$> parseStageOpts rest
parseArgs ("optimize"   : rest) = Optimize   <$> parseStageOpts rest
parseArgs ("escape"     : rest) = Escape     <$> parseStageOpts rest
parseArgs ("codegen"    : rest) = CodeGen    <$> parseStageOpts rest
parseArgs _                     = Nothing

-- | Parse [-o FILE] FILE argument combination for inspection stages.
-- Accepts -o FILE either before or after the input path, but not both.
-- Returns (input, output) where output is Nothing = stdout.
parseStageArgs :: [String] -> Maybe (String, Maybe String)
parseStageArgs = go Nothing Nothing
  where
    go Nothing    _     []                    = Nothing           -- no input
    go (Just i)   o     []                    = Just (i, o)
    go _          _     ("-o" : [])           = Nothing           -- trailing -o
    go i          Nothing ("-o" : arg : rest) = go i (Just arg) rest
    go _          _     ("-o" : _ : _)        = Nothing           -- duplicate -o
    go Nothing    o     (arg : rest)
      | take 1 arg == "-"                     = Nothing           -- unknown flag
      | otherwise                             = go (Just arg) o rest
    go (Just _)   _     (_ : _)               = Nothing           -- second positional

parseStageOpts :: [String] -> Maybe StageOptions
parseStageOpts args = do
  (i, o) <- parseStageArgs args
  pure StageOptions { stageInput = i, stageOutput = o }

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
  TIO.putStrLn "Pipeline inspection (each stage takes [-o FILE] <file.once>):"
  TIO.putStrLn "  preprocess <file.once>        Dump source after `import` resolution (TODO: Agda-level resolver)"
  TIO.putStrLn "  parse <file.once>             Parse only (show function signatures)"
  TIO.putStrLn "  check <file.once>             Parse and type check"
  TIO.putStrLn "  elaborate <file.once>         Surface IR after Surface → IR elaboration (TODO: Agda show)"
  TIO.putStrLn "  optimize <file.once>          IR after categorical-law optimizer (TODO: Agda show)"
  TIO.putStrLn "  escape <file.once>            IR after escape analysis (TODO: Agda show)"
  TIO.putStrLn "  codegen <file.once>           CCC machine program, pre-asm (TODO: Agda show)"
  TIO.putStrLn ""
  TIO.putStrLn "Full compile:"
  TIO.putStrLn "  build [options] <file.once>   Full compile → assembly, optionally to executable"
  TIO.putStrLn ""
  TIO.putStrLn "Build options:"
  TIO.putStrLn "  -o OUTPUT           Output base name (default: input file name)"
  TIO.putStrLn "  --lib               Generate library [default]"
  TIO.putStrLn "  --exe               Generate standalone executable"
  TIO.putStrLn "  --target ARCH       Target architecture (c|x86_64|x86_32|arm64|riscv64) [default: c]"
  TIO.putStrLn "  --save-temps        Keep intermediate files (.s, .o)"
  TIO.putStrLn "  --no-optimize       Skip optimizer"
  TIO.putStrLn "  --strata PATH       Path to Strata directory for imports"
  TIO.putStrLn "  --alloc STRATEGY    Default allocation strategy (stack|heap|pool|arena|const)"
  TIO.putStrLn "  --interp PATH       Interpretation path (deprecated)"
  TIO.putStrLn "  -I:TYPE MODULE      Link interpretation (e.g., -I:C I.Linux.Syscalls)"
  TIO.putStrLn ""
  TIO.putStrLn "Target architectures:"
  TIO.putStrLn "  c       - C backend (not yet implemented)"
  TIO.putStrLn "  x86_64  - x86-64 native (verified via MAlonzo, full IR coverage)"
  TIO.putStrLn "  x86_32  - x86-32 native (verified via abstract-trace, simple-IR subset)"
  TIO.putStrLn "  arm64   - ARM64 native (not yet implemented)"
  TIO.putStrLn "  riscv64 - RISC-V 64-bit (verified via abstract-trace, simple-IR subset)"
  exitFailure
