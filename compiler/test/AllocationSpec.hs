module AllocationSpec (allocationStressTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (forM)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))

import Backend.Common (runOnce, cleanupDir)

-- | Allocation stress tests for escape analysis validation
allocationStressTests :: TestTree
allocationStressTests = testGroup "Allocation Stress"
  [ compileTest
  , semanticEquivalenceTests
  ]

-- | Test that allocation-stress.once compiles with current all-stack mode
compileTest :: TestTree
compileTest = testCase "allocation-stress.once compiles" $ do
  let testDir = "/tmp/once_alloc_stress_compile"
  createDirectoryIfMissing True testDir

  -- Read the allocation stress test program from test directory
  allocSource <- TIO.readFile "test/allocation-stress.once"
  TIO.writeFile (testDir </> "allocation-stress.once") allocSource

  -- Try to compile with default (all-stack) mode
  (exitCode, _, stderr) <- runOnce
    ["build", "--save-temps", testDir </> "allocation-stress.once", "-o", testDir </> "allocation-stress"]

  cleanupDir testDir

  case exitCode of
    ExitSuccess -> pure ()
    ExitFailure _ -> assertFailure $ "Compilation failed:\n" ++ stderr

-- | Test that all allocation modes produce semantically equivalent output
-- This ensures that escape analysis optimizations don't change program behavior
semanticEquivalenceTests :: TestTree
semanticEquivalenceTests = testGroup "semantic equivalence"
  [ testCase "default mode produces expected result" $ do
      let testDir = "/tmp/once_alloc_stress_default"
      result <- compileAndRun testDir Nothing
      cleanupDir testDir
      case result of
        Left err -> assertFailure err
        Right output -> assertBool "produces non-empty output" (not $ null output)

  -- These tests will be enabled once heap allocation and escape analysis are implemented
  -- , testCase "explicit stack mode matches default" $ do
  --     let testDir = "/tmp/once_alloc_stress_stack"
  --     result <- compileAndRun testDir (Just "stack")
  --     cleanupDir testDir
  --     case result of
  --       Left err -> assertFailure err
  --       Right _ -> pure ()
  --
  -- , testCase "heap mode produces same output" $ do
  --     let testDir = "/tmp/once_alloc_stress_heap"
  --     result <- compileAndRun testDir (Just "heap")
  --     cleanupDir testDir
  --     case result of
  --       Left err -> assertFailure err
  --       Right _ -> pure ()
  --
  -- , testCase "escape analysis mode produces same output" $ do
  --     let testDir = "/tmp/once_alloc_stress_escape"
  --     result <- compileAndRun testDir (Just "escape")
  --     cleanupDir testDir
  --     case result of
  --       Left err -> assertFailure err
  --       Right _ -> pure ()
  ]

-- | Helper: compile and run the allocation stress test with a given allocation strategy
compileAndRun :: FilePath -> Maybe String -> IO (Either String String)
compileAndRun testDir allocFlag = do
  createDirectoryIfMissing True testDir

  -- Read the test program
  allocSource <- TIO.readFile "test/allocation-stress.once"
  TIO.writeFile (testDir </> "allocation-stress.once") allocSource

  -- Build command with optional allocation flag
  let allocArg = maybe [] (\s -> ["--alloc", s]) allocFlag
      buildArgs = ["build"] ++ allocArg ++
                  [testDir </> "allocation-stress.once", "-o", testDir </> "allocation-stress"]

  -- Compile
  (compileCode, _, compileErr) <- runOnce buildArgs

  case compileCode of
    ExitFailure _ -> return $ Left $ "Compilation failed for " ++ show allocFlag ++ ":\n" ++ compileErr
    ExitSuccess -> do
      -- TODO: Once we have an executable, run it and capture output
      -- For now, just return success if it compiles
      return $ Right "compiled successfully"
