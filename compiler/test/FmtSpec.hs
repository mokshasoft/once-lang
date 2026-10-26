-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | `once fmt` (plan 0.124, D341): one canonical layout. The tree is kept in
-- it (a file that parses is exactly what `fmt` writes), formatting twice is
-- formatting once, comments come out in order with their text, and `--check`
-- rejects a file that is not in the layout.
module FmtSpec (fmtTests) where

import Control.Monad (filterM, forM)
import Data.List (isPrefixOf, isSuffixOf, sort)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (hClose, hPutStr)
import System.IO.Temp (withSystemTempFile)

import Test.Tasty
import Test.Tasty.HUnit

import Backend.Common (runOnce)

fmtTests :: TestTree
fmtTests = testGroup "Fmt (one canonical layout)"
  [ testCase "every .once file of the tree that parses is in the canonical layout" $ do
      files <- concat <$> mapM onceFiles ["../tests", "../examples", "test", "../Strata"]
      bad <- fmap concat $ forM files $ \f -> do
        src <- readFile f
        (code, out, _) <- runOnce ["fmt", "--stdout", f]
        pure [f | code == ExitSuccess, out /= src]
      assertEqual "files not in the canonical layout (run `once fmt` on them)" [] bad

  , testCase "formatting is idempotent and keeps the comments in order" $ do
      out1 <- formatText sample
      out2 <- formatText out1
      assertEqual "formatting twice is formatting once" out1 out2
      assertEqual "the comments, in order" (comments sample) (comments out1)

  , testCase "--check rejects a file not in the canonical layout" $
      withSystemTempFile "unformatted.once" $ \path h -> do
        hPutStr h "f   : Int\nf = 1 +2\n"
        hClose h
        (code, _, _) <- runOnce ["fmt", "--check", path]
        assertBool "--check should fail" (code /= ExitSuccess)
  ]

-- A module with comments everywhere they can stand.
sample :: String
sample = unlines
  [ "-- header"
  , ""
  , ""
  , "-- before a declaration"
  , "f : Int -> Int"
  , "f = \\x ->"
  , "  -- inside the body"
  , "  x + 1 -- after code"
  , "g : Int"
  , "g = let a = 1"
  , "  -- before the body"
  , "  in f a"
  , "-- at the end"
  ]

formatText :: String -> IO String
formatText src = withSystemTempFile "fmt.once" $ \path h -> do
  hPutStr h src
  hClose h
  (code, out, err) <- runOnce ["fmt", "--stdout", path]
  case code of
    ExitSuccess -> pure out
    _           -> assertFailure ("fmt failed: " ++ err) >> pure ""

-- The comments of a text, in order (a `--` to the end of its line).
comments :: String -> [String]
comments = concatMap one . lines
  where
    one l = case breakOn l of
      Just c  -> [reverse (dropWhile (== ' ') (reverse c))]
      Nothing -> []
    breakOn s
      | "--" `isPrefixOf` s = Just s
      | null s              = Nothing
      | otherwise           = breakOn (tail s)

onceFiles :: FilePath -> IO [FilePath]
onceFiles dir = do
  exists <- doesDirectoryExist dir
  if not exists then pure [] else do
    entries <- sort <$> listDirectory dir
    let paths = map (dir </>) entries
    dirs <- filterM doesDirectoryExist paths
    nested <- concat <$> mapM onceFiles dirs
    pure ([p | p <- paths, ".once" `isSuffixOf` p] ++ nested)
