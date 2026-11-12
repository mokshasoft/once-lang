-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | A rejecting test checks WHY it rejects (D368).
--
-- A test that asserts only "the program is rejected" passes for any error, so
-- it keeps passing after the rule it pinned has changed (D258 turned the String
-- tests into tests that passed for a different reason, and nobody noticed). A
-- rejection is evidence about the Spec only if it names the rule that rejects.
--
-- The reason is a fragment of the error text: the rendering of the
-- elaborator's structured error (`Once.TypeCheck.Error.renderError`), or the
-- message of the stage that rejected (parse, import resolution, the Spec
-- checks of the driver). Pick a fragment that names the rule (and the names
-- or types it is about, where they tell two causes apart). Where the text is
-- known to be a poor diagnostic, the test pins it and says so in a comment
-- (none does since D407).
module Rejection (assertRejects) where

import Data.List (isInfixOf)
import Test.Tasty.HUnit

-- | The program was rejected, and the error mentions @reason@.
assertRejects :: HasCallStack => String -> String -> Either String a -> Assertion
assertRejects what reason r = case r of
  Right _  -> assertFailure ("Should reject: " ++ what)
  Left err ->
    assertBool ("Should reject " ++ what ++ " because of " ++ show reason
                ++ ", but the error was:\n" ++ err)
               (reason `isInfixOf` err)
