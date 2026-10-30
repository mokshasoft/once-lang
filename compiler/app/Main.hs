module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Data.List (isPrefixOf, stripPrefix)
import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..), StageOptions (..), OutputMode (..), Target (..), InterpType (..), FmtOptions (..), FmtMode (..), parseTarget, hostTarget, parseInterpType)

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Nothing -> usage
    Just cmd -> run cmd

-- | Parse command-line arguments
parseArgs :: [String] -> Maybe Command
parseArgs ("build"      : rest) = parseBuild rest
parseArgs ("check"      : rest) = parseCheck rest
parseArgs ("parse"      : rest) = Parse      <$> parseStageOpts rest
parseArgs ("elaborate"  : rest) = Elaborate  <$> parseStageOpts rest
parseArgs ("optimize"   : rest) = Optimize   <$> parseStageOpts rest
parseArgs ("fmt"        : rest) = parseFmt rest
parseArgs ("stats"      : rest) = Stats      <$> parseStageOpts rest
parseArgs _                     = Nothing

-- | `check [--target ARCH] [-o FILE] FILE`: the warnings are the target's
-- (default: the host's, as `build`).
parseCheck :: [String] -> Maybe Command
parseCheck = go hostTarget []
  where
    go _ acc ("--target" : a : rest) = parseTarget a >>= \t' -> go (Just t') acc rest
    go t acc (x : rest)              = go t (acc ++ [x]) rest
    go t acc []                      = parseStageArgs acc >>= \(i, o) ->
      Just $ Check CheckOptions { checkInput = i, checkOutput = o, checkTarget = t }

-- | `fmt [--check | --stdout] FILE...` (`--stdout` takes one file).
parseFmt :: [String] -> Maybe Command
parseFmt ("--check" : files@(_ : _))   = Just (Fmt (FmtOptions FmtCheck files))
parseFmt ("--stdout" : file : [])      = Just (Fmt (FmtOptions FmtStdout [file]))
parseFmt files@(f : _)
  | take 1 f /= "-"                     = Just (Fmt (FmtOptions FmtInPlace files))
parseFmt _                              = Nothing

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
  , bcTarget    :: Maybe Target
  , bcSaveTemps :: Bool
  , bcOptimize  :: Bool
  , bcStrata    :: Maybe String
  , bcInterp    :: Maybe String
  , bcExplicit  :: [(InterpType, String)]
  , bcHost      :: String
  , bcInput     :: Maybe String
  }

defaultBuildConfig :: BuildConfig
defaultBuildConfig = BuildConfig
  { bcOutput    = Nothing
  , bcMode      = Infer  -- program iff the module defines `main`, else library
  , bcTarget    = hostTarget
  , bcSaveTemps = False
  , bcOptimize  = True
  , bcStrata    = Nothing
  , bcInterp    = Nothing
  , bcExplicit  = []
  , bcHost      = "Linux"
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
        { buildInput     = input
        , buildOutput    = bcOutput cfg
        , buildMode      = bcMode cfg
        , buildTarget    = bcTarget cfg
        , buildSaveTemps = bcSaveTemps cfg
        , buildOptimize  = bcOptimize cfg
        , buildStrata    = bcStrata cfg
        , buildInterp    = bcInterp cfg
        , buildExplicitInterps = bcExplicit cfg
        , buildHost      = bcHost cfg
        }
    go ("-o" : out : rest) cfg = go rest cfg { bcOutput = Just out }
    go ("--lib" : rest) cfg = go rest cfg { bcMode = Library }
    go ("--exe" : rest) cfg = go rest cfg { bcMode = Executable }
    go ("--target" : t : rest) cfg = case parseTarget t of
      Just target -> go rest cfg { bcTarget = Just target }
      Nothing -> Nothing  -- invalid target
    go ("--save-temps" : rest) cfg = go rest cfg { bcSaveTemps = True }
    go ("--no-optimize" : rest) cfg = go rest cfg { bcOptimize = False }
    go ("--strata" : s : rest) cfg = go rest cfg { bcStrata = Just s }
    go ("--interp" : i : rest) cfg = go rest cfg { bcInterp = Just i }
    go ("--host" : h : rest) cfg = go rest cfg { bcHost = h }
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
  TIO.putStrLn "Inspection (each takes [-o FILE] <file.once>):"
  TIO.putStrLn "  parse <file.once>             Signatures after `import` resolution"
  TIO.putStrLn "  check <file.once>             Parse and type check ([--target ARCH] for its warnings)"
  TIO.putStrLn "  elaborate <file.once>         Each function's IR, as elaborated"
  TIO.putStrLn "  optimize <file.once>          Each function's IR, after the optimizer"
  TIO.putStrLn ""
  TIO.putStrLn "Formatting (one canonical layout, no options):"
  TIO.putStrLn "  fmt <file.once>...            Rewrite files in the canonical layout"
  TIO.putStrLn "  fmt --check <file.once>...    Fail if a file is not in the canonical layout"
  TIO.putStrLn "  fmt --stdout <file.once>      Print the formatted file"
  TIO.putStrLn ""
  TIO.putStrLn "Measuring ([-o FILE] <file.once>):"
  TIO.putStrLn "  stats <file.once>             Static costs of the program image (heap sites/cells, frames)"
  TIO.putStrLn ""
  TIO.putStrLn "Full compile:"
  TIO.putStrLn "  build [options] <file.once>   Full compile → assembly, optionally to executable"
  TIO.putStrLn ""
  TIO.putStrLn "Build options:"
  TIO.putStrLn "  -o OUTPUT           Output base name (default: input file name)"
  TIO.putStrLn "  (default)           Infer: executable if the module defines `main`, else library"
  TIO.putStrLn "  --lib               Force library output (no entry point)"
  TIO.putStrLn "  --exe               Force standalone executable (requires a `main`)"
  TIO.putStrLn "  --target ARCH       Target architecture (x86_64|x86_32|arm64|riscv64) [default: the host's]"
  TIO.putStrLn "  --save-temps        Keep intermediate files (.s, .o)"
  TIO.putStrLn "  --no-optimize       Skip optimizer"
  TIO.putStrLn "  --strata PATH       Path to Strata directory for imports"
  TIO.putStrLn "  --interp PATH       Interpretation path (deprecated)"
  TIO.putStrLn "  -I:TYPE MODULE      Link interpretation (e.g., -I:x86_64 I.Linux.Syscalls)"
  TIO.putStrLn ""
  TIO.putStrLn "Target architectures:"
  TIO.putStrLn "  x86_64  - x86-64 native (verified via MAlonzo, full IR coverage)"
  TIO.putStrLn "  x86_32  - x86-32 native (verified via abstract-trace, simple-IR subset)"
  TIO.putStrLn "  arm64   - ARM64 native (not yet implemented)"
  TIO.putStrLn "  riscv64 - RISC-V 64-bit (verified via abstract-trace, simple-IR subset)"
  exitFailure
