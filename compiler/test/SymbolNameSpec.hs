-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

-- | Golden tests pinning the Haskell symbol mangler (Once.Target.SymbolName)
-- to the verified Agda original (Once.Target.Symbol). The first group asserts
-- exactly the vectors the Agda module proves by `refl`; if the two ever drift,
-- these fail. The second group pins the symbols the build actually relies on.
module SymbolNameSpec (symbolNameTests, thunkSymbolTests) where

import Test.Tasty
import Test.Tasty.HUnit

import Once.Target.SymbolName (onceSymbolPath, mangleComponent)

import Backend.Common (BackendArch, archName, backendArches, buildAsmOn)
import Data.Char (isAlphaNum)
import Data.List (isPrefixOf, nub, sort)

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


------------------------------------------------------------------------
-- THUNK-SYMBOL CLOSURE (D160 / D161).
--
-- A closure body's DEFINITION symbol and every REFERENCE to it are one string,
-- resolved by the assembler. They drifted: `emit-thunk-body` rendered
-- `showNat` (`.L_thunk_10`) while the references rendered `showLabelId`
-- (`.L_thunk_once_4main_10`, carrying the CanonicalName path), on all three
-- targets. The agreement had been asserted in a comment.
--
-- The exit tests DO catch that — as a build failure, because `as` cannot
-- resolve the reference. These check the property directly on the emitted
-- assembly, so the failure names the symbol instead of surfacing as a linker
-- message, and the DUPLICATE case is covered too: `.L_thunk_…  is already
-- defined` was the 2026-08-06 regression, which D100 records as "invisible to
-- every proof, because the only layer that rejects it is the assembler".
--
-- Written against `Backend.Common.buildAsmOn` — the same build path
-- `buildAndRunOn` uses — rather than as a shell script, so it cannot drift
-- from how the suite actually compiles a test program.
------------------------------------------------------------------------

-- | `.L_thunk_<sym>` occurrences, split into definitions (label position, i.e.
-- the symbol is followed by ':') and all occurrences.
thunkSyms :: String -> ([String], [String])
thunkSyms asm = (concatMap defsOf ls, concatMap refsOf ls)
  where
    ls = lines asm
    sym r = takeWhile (\c -> isAlphaNum c || c == '_') r
    -- every occurrence anywhere on the line
    refsOf l = go l
      where go [] = []
            go r@(_:t)
              | pfx `isPrefixOf` r = let s = sym (drop 2 r) in ("L" ++ s) : go t
              | otherwise          = go t
    -- a definition: the line STARTS with the symbol and it ends in ':'
    defsOf l
      | pfx `isPrefixOf` l
      , let s = "L" ++ sym (drop 2 l)
      , (("." ++ s ++ ":") `isPrefixOf` l) = [s]
      | otherwise = []
    pfx = ".L_thunk_"

-- | Every referenced thunk symbol is defined exactly once.
thunkClosureOn :: BackendArch -> String -> IO (Either String ())
thunkClosureOn arch name = do
  r <- buildAsmOn arch name
  pure $ case r of
    Left e    -> Left e
    Right asm ->
      let (defs, refs) = thunkSyms asm
          undef = [ s | s <- nub refs, s `notElem` defs ]
          dup   = [ s | s <- nub defs, length (filter (== s) defs) > 1 ]
          tag   = "[" ++ archName arch ++ "] "
      in case (undef, dup) of
           ([], []) -> Right ()
           _        -> Left $ tag
                          ++ (if null undef then "" else "referenced but never defined: " ++ show (sort undef) ++ "; ")
                          ++ (if null dup   then "" else "defined more than once: " ++ show (sort dup))

-- | Closure-producing programs: each emits at least one `.L_thunk_` body.
thunkPrograms :: [String]
thunkPrograms =
  [ "layer4-partial-app", "layer4-keep-fst", "layer4-closure-in-sum"
  , "arith-lambda-1", "arith-lambda-2" ]

thunkSymbolTests :: TestTree
thunkSymbolTests = testGroup "Thunk symbols resolve (definition == reference)"
  [ testGroup name
      [ testCase (archName a) (thunkClosureOn a name >>= either assertFailure pure)
      | a <- backendArches ]
  | name <- thunkPrograms ]
