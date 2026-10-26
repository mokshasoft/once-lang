-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | What an import brings into scope (plan 0.122, the `DSignature` owner's
-- removal). An imported module's FFI signatures are read from the module map,
-- as the Spec's `Imported`/`SignaturesOf` read them: a module sees the
-- signatures of the modules IT imports, never those its imports import. So
-- when B imports C, A cannot name C's FFI as `f@B` (transitive re-export is
-- gone). An import contributes only its signatures (D319).
module ImportSpec (importTests) where

import Test.Tasty
import Test.Tasty.HUnit

import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)

import Backend.Common (runOnce)

importTests :: TestTree
importTests = testGroup "Imports (no transitive FFI re-export)"
  [ testCase "an import's own FFI signature is in scope" $ do
      r <- checkWith [ "import I.T.C as C", "", "go : Act Unit Unit", "go = ping@C" ]
      assertRight r

  , testCase "an import's import's FFI is not re-exported (ping@B is unbound)" $ do
      r <- checkWith [ "import Mid.B as B", "", "go : Act Unit Unit", "go = ping@B" ]
      assertBool "Should reject C's FFI named through B" (isLeft r)
  ]

------------------------------------------------------------------------
-- Helpers: a strata of two modules — `I.T.C` declares the FFI `ping`,
-- `Mid.B` imports it and defines `relay` with it — and a library build of
-- the program against it.
------------------------------------------------------------------------

checkWith :: [String] -> IO (Either String ())
checkWith program = withSystemTempDirectory "imports" $ \dir -> do
  let strata = dir </> "Strata"
  createDirectoryIfMissing True (strata </> "Interpretations" </> "T")
  createDirectoryIfMissing True (strata </> "Mid")
  writeFile (strata </> "Interpretations" </> "T" </> "C.once")
    (unlines [ "signature ping : Act Unit Unit" ])
  writeFile (strata </> "Mid" </> "B.once")
    (unlines [ "import I.T.C as C", "", "relay : Act Unit Unit", "relay = ping@C" ])
  let src = dir </> "a.once"
  writeFile src (unlines program)
  (exitCode, stdout, stderr) <-
    runOnce ["build", "--lib", "--target", "x86_64", "--strata", strata, "-o", dir </> "out", src]
  case exitCode of
    ExitSuccess   -> return (Right ())
    ExitFailure _ -> return (Left (stdout ++ stderr))

assertRight :: Either String () -> Assertion
assertRight (Right ()) = return ()
assertRight (Left err) = assertFailure ("Should accept, got: " ++ err)

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False
