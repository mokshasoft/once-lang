-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | A module is well-typed iff every definition is typed ONCE, at its
-- declaration, in its prefix (plan 0.103 phase 1, D234/D235). Every
-- `Mu`/`Nu`-typed definition is a telescope entry (concreteness routes it
-- away from a direct-call symbol); such entries used to be typed only where
-- they were used, and in the use site's context.
module TelescopeSpec (telescopeTests) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode (..))
import System.IO (hClose)
import System.IO.Temp (withSystemTempFile)

import Backend.Common (runOnce, testStrataDir)

telescopeTests :: TestTree
telescopeTests = testGroup "Telescope (every definition typed once)"
  [ testCase "an unused ill-typed telescope definition is rejected" $ do
      r <- checkLib
        [ "f : Nu (K Int)"
        , "f = 5"
        ]
      assertBool "Should reject an ill-typed Nu definition even when unused" (isLeft r)

  , testCase "an unused well-typed telescope definition is accepted" $ do
      r <- checkLib
        [ "f : Int -> Nu (K Int)"
        , "f = ana (\\x -> x)"
        ]
      r @?= Right ()

  , testCase "two telescope definitions of one name are rejected" $ do
      r <- checkLib
        [ "f : Int -> Nu (K Int)"
        , "f = ana (\\x -> x)"
        , ""
        , "f : Int -> Nu (K Int)"
        , "f = ana (\\x -> x)"
        ]
      assertBool "Should reject duplicate telescope definitions" (isLeft r)
  ]

checkLib :: [T.Text] -> IO (Either String ())
checkLib sourceLines = withSystemTempFile "telescope.once" $ \path handle -> do
  TIO.hPutStr handle (T.unlines sourceLines)
  hClose handle
  withSystemTempFile "telescope-out" $ \out outH -> do
    hClose outH
    (exitCode, stdout, stderr) <-
      runOnce ["build", "--lib", "--target", "x86_64", "--strata", testStrataDir, "-o", out, path]
    case exitCode of
      ExitSuccess   -> return (Right ())
      ExitFailure _ -> return (Left (stdout ++ stderr))

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
