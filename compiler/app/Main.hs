module Main (main) where

import System.Environment (getArgs)
import System.Exit (exitFailure)
import qualified Data.Text.IO as TIO

import Once.CLI (run, Command (..), BuildOptions (..), CheckOptions (..))

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
parseBuild args = case args of
  [input] -> Just $ Build BuildOptions
    { buildInput = input
    , buildOutput = Nothing
    }
  [input, "-o", output] -> Just $ Build BuildOptions
    { buildInput = input
    , buildOutput = Just output
    }
  _ -> Nothing

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
  TIO.putStrLn "  build <file.once> [-o <output>]  Compile to C"
  TIO.putStrLn "  check <file.once>                Type check only"
  exitFailure
