-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Golden tests pinning the Haskell symbol mangler (Once.Target.SymbolName)
-- to the verified Agda original (Once.Target.Symbol). The first group asserts
-- exactly the vectors the Agda module proves by `refl`; if the two ever drift,
-- these fail. The second group pins the symbols the build actually relies on.
module SymbolNameSpec (symbolNameTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Once.Target.SymbolName (onceSymbolPath, mangleComponent)

symbolNameTests :: TestTree
symbolNameTests = testGroup "Symbol mangling (mirrors Once.Target.Symbol)"
  [ testGroup "Agda `refl` vectors"
      [ testCase "Cars/All/foo" $
          onceSymbolPath ["Cars", "All", "foo"] @?= "once_4Cars_3All_3foo"
      , testCase "underscore in a component is not a separator" $
          onceSymbolPath ["Cars", "All_foo"] @?= "once_4Cars_7All_foo"
      , testCase "z-encodes '+'" $
          onceSymbolPath ["M", "assocL+"] @?= "once_1M_8assocLzp"
      , testCase "z-encodes '.'" $
          onceSymbolPath ["arith.add.int"] @?= "once_15arithzdaddzdint"
      , testCase "mangleComponent z-escapes 'z'" $
          mangleComponent "zp" @?= "3zzp"
      ]
  , testGroup "symbols the build aliases to"
      [ testCase "I.Test.Emit.emit" $
          onceSymbolPath ["Interpretations", "Test", "Emit", "emit"]
            @?= "once_15Interpretations_4Test_4Emit_4emit"
      , testCase "I.Linux.Syscalls.exit" $
          onceSymbolPath ["Interpretations", "Linux", "Syscalls", "exit"]
            @?= "once_15Interpretations_5Linux_8Syscalls_4exit"
      ]
  ]
