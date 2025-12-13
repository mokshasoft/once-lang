module ModuleSpec (moduleTests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as Map

import Once.Module
import Once.Syntax (Module (..), Decl (..), SType (..))

moduleTests :: TestTree
moduleTests = testGroup "Module System"
  [ abbreviationTests
  , pathResolutionTests
  , aliasTests
  , lookupTests
  , buildExportsTests
  ]

------------------------------------------------------------------------
-- Path Abbreviation Tests
------------------------------------------------------------------------

abbreviationTests :: TestTree
abbreviationTests = testGroup "Path abbreviations"
  [ testCase "I. expands to Interpretations" $ do
      expandAbbreviations ["I", "Linux", "Syscalls"]
        @?= Right ["Interpretations", "Linux", "Syscalls"]

  , testCase "D. expands to Derived" $ do
      expandAbbreviations ["D", "Canonical"]
        @?= Right ["Derived", "Canonical"]

  , testCase "Single I expands" $ do
      expandAbbreviations ["I"]
        @?= Right ["Interpretations"]

  , testCase "Single D expands" $ do
      expandAbbreviations ["D"]
        @?= Right ["Derived"]

  , testCase "Unknown single-letter abbreviation fails" $ do
      case expandAbbreviations ["X", "Foo"] of
        Left (AbbreviationNotFound "X") -> pure ()
        other -> assertFailure $ "Expected AbbreviationNotFound, got: " ++ show other

  , testCase "Multi-char path not treated as abbreviation" $ do
      expandAbbreviations ["Foo", "Bar"]
        @?= Right ["Foo", "Bar"]

  , testCase "Full path unchanged" $ do
      expandAbbreviations ["Interpretations", "Linux", "Syscalls"]
        @?= Right ["Interpretations", "Linux", "Syscalls"]

  , testCase "Empty path unchanged" $ do
      expandAbbreviations []
        @?= Right []
  ]

------------------------------------------------------------------------
-- File Path Resolution Tests
------------------------------------------------------------------------

pathResolutionTests :: TestTree
pathResolutionTests = testGroup "File path resolution"
  [ testCase "Module path to file path" $ do
      moduleToFilePath "Strata" ["Derived", "Canonical"]
        @?= "Strata/Derived/Canonical.once"

  , testCase "Deep module path" $ do
      moduleToFilePath "Strata" ["Interpretations", "Linux", "Syscalls"]
        @?= "Strata/Interpretations/Linux/Syscalls.once"

  , testCase "Single component path" $ do
      moduleToFilePath "Strata" ["Prelude"]
        @?= "Strata/Prelude.once"

  , testCase "Custom strata path" $ do
      moduleToFilePath "/custom/path" ["Derived", "Simple"]
        @?= "/custom/path/Derived/Simple.once"
  ]

------------------------------------------------------------------------
-- Alias Resolution Tests
------------------------------------------------------------------------

aliasTests :: TestTree
aliasTests = testGroup "Alias resolution"
  [ testCase "Single alias resolves" $ do
      let env = (emptyModuleEnv "Strata" ".c")
                  { meAliases = Map.singleton "C" ["Derived", "Canonical"] }
      resolveAlias env ["C"]
        @?= ["Derived", "Canonical"]

  , testCase "Unknown alias unchanged" $ do
      let env = emptyModuleEnv "Strata" ".c"
      resolveAlias env ["Unknown"]
        @?= ["Unknown"]

  , testCase "Multi-component path not resolved as alias" $ do
      let env = (emptyModuleEnv "Strata" ".c")
                  { meAliases = Map.singleton "C" ["Derived", "Canonical"] }
      resolveAlias env ["C", "Extra"]
        @?= ["C", "Extra"]

  , testCase "Multiple aliases in environment" $ do
      let env = (emptyModuleEnv "Strata" ".c")
                  { meAliases = Map.fromList
                      [ ("S", ["Derived", "Simple"])
                      , ("E", ["Interpretations", "Linux", "Exit"])
                      ]
                  }
      resolveAlias env ["S"] @?= ["Derived", "Simple"]
      resolveAlias env ["E"] @?= ["Interpretations", "Linux", "Exit"]
  ]

------------------------------------------------------------------------
-- Qualified Name Lookup Tests
------------------------------------------------------------------------

lookupTests :: TestTree
lookupTests = testGroup "Qualified name lookup"
  [ testCase "Lookup in empty env fails with ModuleNotFound" $ do
      let env = emptyModuleEnv "Strata" ".c"
      case lookupQualified "swap" ["Derived", "Simple"] env of
        Left (ModuleNotFound _ _) -> pure ()
        other -> assertFailure $ "Expected ModuleNotFound, got: " ++ show other

  , testCase "Alias resolved before abbreviation check" $ do
      -- When path is an alias, it should resolve without trying abbreviation expansion
      let env = (emptyModuleEnv "Strata" ".c")
                  { meAliases = Map.singleton "S" ["Derived", "Simple"] }
      -- "S" is an alias, not an abbreviation - should not fail with AbbreviationNotFound
      case lookupQualified "swap" ["S"] env of
        Left (ModuleNotFound ["Derived", "Simple"] _) -> pure ()
        Left (AbbreviationNotFound _) -> assertFailure "Should resolve alias before checking abbreviations"
        other -> assertFailure $ "Expected ModuleNotFound for resolved alias, got: " ++ show other
  ]

------------------------------------------------------------------------
-- Build Exports Tests
------------------------------------------------------------------------

buildExportsTests :: TestTree
buildExportsTests = testGroup "Build exports from module"
  [ testCase "Empty module has no exports" $ do
      let m = Module [] []
      Map.null (buildExports m) @?= True

  , testCase "Type signature exported" $ do
      let m = Module [] [TypeSig "foo" (STArrow STUnit STUnit)]
          exports = buildExports m
      Map.member "foo" exports @?= True

  , testCase "Primitive exported with type" $ do
      let m = Module [] [Primitive "exit0" (STEff STUnit STUnit)]
          exports = buildExports m
      case Map.lookup "exit0" exports of
        Just (DeclInfo (Just _) _) -> pure ()
        other -> assertFailure $ "Expected DeclInfo with type, got: " ++ show other

  , testCase "Multiple declarations exported" $ do
      let m = Module []
                [ TypeSig "swap" (STArrow (STProduct (STVar "A") (STVar "B"))
                                          (STProduct (STVar "B") (STVar "A")))
                , TypeSig "diag" (STArrow (STVar "A") (STProduct (STVar "A") (STVar "A")))
                ]
          exports = buildExports m
      Map.size exports @?= 2
      Map.member "swap" exports @?= True
      Map.member "diag" exports @?= True
  ]
