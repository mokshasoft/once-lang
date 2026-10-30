{-# LANGUAGE ScopedTypeVariables #-}
-- | Bridge module between Haskell and MAlonzo-generated Agda code: the
-- compiler and the front end the tools share.
--
-- Provides a stable Haskell API over the numeric-suffixed names that
-- MAlonzo emits. Each tool beside the compiler has its own bridge
-- (`Once.Inspect.Bridge`, `Once.Measure.Bridge`, `Once.Format.Bridge`,
-- D352); a re-extraction changes the bridge whose names moved.
--
-- Haskell drives the transitive import I/O (`parseSource`, `moduleImports`,
-- `resolveImports`); Agda resolves and compiles (`assemblyFromModule`).
module Once.Compile.Bridge
  ( -- * Types
    Arch (..)
    -- * Module AST (opaque handle + import inspection)
  , Module
  , Resolved
  , resolvedAgda
  , ImportRef (..)
    -- * AST-level pipeline
  , parseSource
  , moduleImports
  , isProgram
  , moduleWarnings
  , resolveImports
  , assemblyFromModule
  ) where

import Data.Maybe (isJust)
import Data.Text (Text)
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as MSigma
import qualified MAlonzo.Code.Data.Sum.Base as MSum
import qualified MAlonzo.Code.Once.Extract.Root as MR
import qualified MAlonzo.Code.Once.Target.Arch as MTA
import qualified MAlonzo.Code.Once.Parser.Module.Core as MMC
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax as MSS
import Once.Bridge.Agda (agdaToText, textToAgda, eitherText, runs)

------------------------------------------------------------------------
-- Haskell types (stable API)
------------------------------------------------------------------------

data Arch
  = X86_64   -- ^ x86-64 (full IR coverage via direct compile-ir)
  | X86_32   -- ^ x86-32 (abstract-trace pipeline; simple-IR subset)
  | RiscV64  -- ^ RISC-V 64 (abstract-trace pipeline; simple-IR subset)
  deriving (Eq, Show)

-- | Opaque Module handle — a wrapped Agda `Module` AST. Haskell
-- doesn't introspect the internals except through `moduleImports`.
newtype Module = Module MSS.T_Module_122

-- | Opaque resolved-module handle: the resolved module, and the signatures
-- of the modules it imports (the Agda `Resolved`).
newtype Resolved = Resolved MMC.T_Resolved_8

-- | The Agda value, for the tools' bridges.
resolvedAgda :: Resolved -> MMC.T_Resolved_8
resolvedAgda (Resolved r) = r

-- | An `import` decl seen inside a parsed module. Haskell uses this
-- to decide which files to load before calling `resolveImports`.
data ImportRef = ImportRef
  { importPath  :: [Text]       -- ^ Dotted module path (e.g. ["I","Foo","Bar"])
  , importAlias :: Maybe Text   -- ^ Alias from `as X`, or Nothing
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- MAlonzo conversion (update suffixes after regenerating)
------------------------------------------------------------------------

-- Single shared `Arch` enum (Once.Target.Arch). The compiler and the verified
-- pipeline now use the SAME type, so one converter serves both call sites
-- (formerly `toMArch` + `toMVArch` over two isomorphic Agda enums).
toMArch :: Arch -> MTA.T_Arch_6
toMArch X86_64  = MTA.C_x86'45'64_8
toMArch X86_32  = MTA.C_x86'45'32_10
toMArch RiscV64 = MTA.C_riscv64_12

------------------------------------------------------------------------
-- AST-level pipeline
------------------------------------------------------------------------

-- | Parse a single .once source into a Module AST.
-- Returns `Left err` if the source fails to parse cleanly (including
-- silent-drop cases like dotted primitive names or TVars in type
-- position — see plan 0.6 Phase A). It is `Once.Parser.parseStrict`, the
-- parser the apex's `compile` reads a source with, so these failures surface
-- rather than silently producing a module with missing decls.
parseSource :: Text -> Either Text Module
parseSource source =
  case MR.d_parse'45'source_34 runs (textToAgda source) of
    MSum.C_inj'8321'_38 err -> Left (agdaToText err)
    MSum.C_inj'8322'_42 m   -> Right (Module (unsafeCoerce m))

-- | Extract just the `import` declarations from a parsed Module.
-- Haskell uses this to decide which files to read + parse next.
-- D162: goes through `Once.Extract.Names`, which returns (path, alias) pairs,
-- so this no longer names `DImport` or its fields. Before, it destructured
-- MAlonzo constructors by serial — a second copy of the datatype's shape,
-- checked by nobody.
moduleImports :: Module -> [ImportRef]
moduleImports (Module m) =
  [ ImportRef (map agdaToText (MR.d_import'45'path_38 runs pr))
              (fmap agdaToText (MR.d_import'45'alias_40 runs pr))
  | pr <- MR.d_module'45'imports_36 runs m
  ]

-- | Is the module a program (it has a `main` the compiler compiles), or a
-- library? The compiler's `moduleToIR`, the case the apex's `compile` splits
-- on (`Adequacy.Compile.compile-mir`): `build` links an executable exactly when
-- the theorem says there are bytes to run (D354).
isProgram :: Resolved -> Bool
isProgram (Resolved r) = isJust (MR.d_main'45'ir_42 runs r)

-- | D123/D116: the rounding warnings this module has AT THIS TARGET, rendered.
--
-- `warningsFor` is a PURE QUERY of the parsed module and the arch — deliberately
-- not threaded through `compile`, so wiring it does not change the pipeline's
-- type. It is arch-relative because rounding is (D113): the same literal is
-- exact at one target's format and not at another's.
--
-- Until this existed, D116's "K3 removed the refusal; this is what replaces it"
-- was only half true — the refusal was gone and the replacement unreachable.
moduleWarnings :: Arch -> Text -> Resolved -> [Text]
moduleWarnings arch src (Resolved m) =
  map agdaToText (MR.d_warnings_46 runs (toMArch arch) (textToAgda src) (unsafeCoerce m))

-- | Resolve the user's module against the module map: its references are
-- resolved, and the signatures of the modules it imports are read from the
-- map (the Spec's `Imported`).
--
-- The caller must supply a `ModuleMap` containing every module the user's
-- module imports, as written. Haskell builds this bottom-up, resolving each
-- imported module to check it.
resolveImports
  :: [([Text], Module)]   -- ^ Map from dotted import path to the written Module
  -> Module               -- ^ User's module
  -> Either Text Resolved
resolveImports modMap (Module userMod) =
  let agdaMap = map mapEntry modMap
      agdaResult = MR.d_resolve'45'imports_44 runs (unsafeCoerce agdaMap) (unsafeCoerce userMod)
  in case agdaResult of
       MSum.C_inj'8321'_38 err -> Left (agdaToText err)
       MSum.C_inj'8322'_42 r   -> Right (Resolved (unsafeCoerce r))
  where
    mapEntry :: ([Text], Module) -> MSigma.T_Σ_14
    mapEntry (path, Module m) =
      MSigma.C__'44'__32 (unsafeCoerce (map textToAgda path :: [Text])) (unsafeCoerce m)

-- | The assembly text of a resolved module, built for `arch` with or without
-- the optimizer, or the compiler's error: the print of the file the verified
-- compiler emits (`Once.Compile.assemblyFromModule`), in allocation mode `Heap`,
-- the mode the apex covers (D352).
assemblyFromModule :: Bool -> Arch -> Resolved -> Either Text Text
assemblyFromModule doOpt arch (Resolved mod_) =
  eitherText (MR.d_assembly_48 runs doOpt (toMArch arch) (unsafeCoerce mod_))
