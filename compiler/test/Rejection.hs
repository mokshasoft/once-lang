-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | A rejecting test checks WHY it rejects (plan 0.115).
--
-- A test that asserts only "the program is rejected" passes for any error, so
-- it keeps passing after the rule it pinned has changed (D258 turned the String
-- tests into tests that passed for a different reason, and nobody noticed). A
-- rejection is evidence about the Spec only if it names the rule that rejects.
--
-- The reason is a fragment of the error text: the rendering of the
-- elaborator's structured error (`Once.TypeCheck.Error.renderError`), or the
-- message of the stage that rejected (parse, import resolution, the Spec
-- checks of the driver). Pick the fragment that names the rule, not the
-- program's own names.
module Rejection (assertRejects) where

import Data.List (isInfixOf)
import GHC.Stack (HasCallStack, callStack, getCallStack, SrcLoc (..))
import System.Environment (lookupEnv)
import Test.Tasty.HUnit

-- | The program was rejected, and the error mentions @reason@.
assertRejects :: HasCallStack => String -> String -> Either String a -> Assertion
assertRejects what reason r = case r of
  Right _  -> assertFailure ("Should reject: " ++ what)
  Left err -> do
    logRejection what err
    assertBool ("Should reject " ++ what ++ " because of " ++ show reason
                ++ ", but the error was:\n" ++ err)
               (reason `isInfixOf` err)

-- TEMPORARY (plan 0.115 step 1, the inventory): with ONCE_REJECT_LOG set, record
-- each rejection's outermost call site and its error.
logRejection :: HasCallStack => String -> String -> IO ()
logRejection what err = do
  mlog <- lookupEnv "ONCE_REJECT_LOG"
  case mlog of
    Nothing -> pure ()
    Just path -> do
      let site = case reverse (getCallStack callStack) of
            ((_, loc) : _) -> srcLocFile loc ++ ":" ++ show (srcLocStartLine loc)
            []             -> "?"
      appendFile path (site ++ "\t" ++ what ++ "\t" ++ show err ++ "\n")
