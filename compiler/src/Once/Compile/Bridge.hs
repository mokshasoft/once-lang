{-# LANGUAGE ScopedTypeVariables #-}
-- | Bridge module between Haskell and MAlonzo-generated Agda code.
--
-- Provides a stable Haskell API over the numeric-suffixed names that
-- MAlonzo emits. When regenerating MAlonzo, only this file needs
-- updating.
--
-- Two pipelines are exposed:
--
--   * `compile`           — one-shot source → CompileResult; used by
--                           the existing (legacy, text-level-import)
--                           path.
--   * AST-level API       — `parseSource`, `moduleImports`,
--                           `resolveImports`, `compileFromModule`.
--                           Used by the new pipeline where Haskell
--                           drives transitive import I/O and Agda
--                           does the verified AST-level substitution.
module Once.Compile.Bridge
  ( -- * Types
    Stage (..)
  , Arch (..)
  , CompileResult (..)
  , FunSig (..)
  , PolyFunSig (..)
    -- * Module AST (opaque handle + import inspection)
  , Module
  , Resolved
  , resolvedModule
  , ImportRef (..)
    -- * One-shot compilation (legacy)
  , compile
    -- * AST-level pipeline
  , parseSource
  , moduleImports
  , moduleHasMain
  , moduleWarnings
  , resolveImports
  , compileFromModule
  , dumpIRFromModule
    -- * Measuring (MERGE.md §1)
  , statsFromModule
    -- * Formatting (plan 0.124)
  , formatSource
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as MSigma
import qualified MAlonzo.Code.Data.Sum.Base as MSum
import qualified MAlonzo.Code.Once.Compile as MC
import qualified MAlonzo.Code.Once.Compile.Dump as MCD
import qualified MAlonzo.Code.Once.Measure as MMe
import qualified MAlonzo.Code.Once.IR as MCIR
import qualified MAlonzo.Code.Once.Target.Arch as MTA
import qualified MAlonzo.Code.Once.Warnings as MW
import qualified MAlonzo.Code.Once.Parser as MP
import qualified MAlonzo.Code.Once.Extract.Names as MEN
import qualified MAlonzo.Code.Once.Parser.Module.Core as MMC
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax as MSS
import qualified MAlonzo.Code.Once.Parser.Module.Resolve as MMR
import qualified MAlonzo.Code.Once.Type as MT
import qualified MAlonzo.Code.Once.Format as MF

------------------------------------------------------------------------
-- Haskell types (stable API)
------------------------------------------------------------------------

data Stage = Parse | Check | Build
  deriving (Eq, Show)

data Arch
  = X86_64   -- ^ x86-64 (full IR coverage via direct compile-ir)
  | X86_32   -- ^ x86-32 (abstract-trace pipeline; simple-IR subset)
  | RiscV64  -- ^ RISC-V 64 (abstract-trace pipeline; simple-IR subset)
  deriving (Eq, Show)

data FunSig = FunSig
  { funSigName :: Text
  , funSigType :: Text
  } deriving (Eq, Show)

-- | User-declared polymorphic definitions surface as `PolyFunSig`.
-- Their signatures are polymorphic schemas (with `TVar`s); downstream
-- compile-stage consumers currently reject non-empty poly lists
-- pending plan 0.6 Phase C.1 (schema instantiation at call sites).
data PolyFunSig = PolyFunSig
  { polyFunSigName :: Text
  , polyFunSigType :: Text
  } deriving (Eq, Show)

data CompileResult
  = Parsed [FunSig] [PolyFunSig]
  | Checked
  | Built Text
  | Error Text
  deriving (Eq, Show)

-- | Opaque Module handle — a wrapped Agda `Module` AST. Haskell
-- doesn't introspect the internals except through `moduleImports`.
newtype Module = Module MSS.T_Module_122

-- | Opaque resolved-module handle: the resolved module, and the signatures
-- of the modules it imports (the Agda `Resolved`).
newtype Resolved = Resolved MMC.T_Resolved_8

-- | The resolved module itself.
resolvedModule :: Resolved -> Module
resolvedModule (Resolved r) = Module (MMC.d_rmodule_14 r)

-- | An `import` decl seen inside a parsed module. Haskell uses this
-- to decide which files to load before calling `resolveImports`.
data ImportRef = ImportRef
  { importPath  :: [Text]       -- ^ Dotted module path (e.g. ["I","Foo","Bar"])
  , importAlias :: Maybe Text   -- ^ Alias from `as X`, or Nothing
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- MAlonzo conversion (update suffixes after regenerating)
------------------------------------------------------------------------

toMStage :: Stage -> MC.T_Stage_1504
toMStage Parse = MC.C_Parse_1506
toMStage Check = MC.C_Check_1508
toMStage Build = MC.C_Build_1510

-- Single shared `Arch` enum (Once.Target.Arch). The compiler and the verified
-- pipeline now use the SAME type, so one converter serves both call sites
-- (formerly `toMArch` + `toMVArch` over two isomorphic Agda enums).
toMArch :: Arch -> MTA.T_Arch_6
toMArch X86_64  = MTA.C_x86'45'64_8
toMArch X86_32  = MTA.C_x86'45'32_10
toMArch RiscV64 = MTA.C_riscv64_12

-- | Agda strings are Haskell `Text` at runtime (MAlonzo primitive binding).
agdaToText :: a -> Text
agdaToText = unsafeCoerce

textToAgda :: Text -> a
textToAgda = unsafeCoerce

fromMFunInfo :: MP.T_FunInfo_78 -> FunSig
fromMFunInfo fi = FunSig
  { funSigName = agdaToText (MP.d_funName_88 fi)
    -- D007: funType is now `Maybe Type` (Nothing = no explicit sig, inferred).
    -- MAlonzo's Maybe is Haskell's Maybe (Just/Nothing pattern synonyms).
  , funSigType = case MP.d_funType_90 fi of
      Just ty -> agdaToText (MT.d_showType_36 0 ty)
      Nothing -> T.pack "<inferred>"
  }

fromMPolyFunInfo :: MP.T_PolyFunInfo_98 -> PolyFunSig
fromMPolyFunInfo pfi = PolyFunSig
  { polyFunSigName = agdaToText (MP.d_pfunName_106 pfi)
  , polyFunSigType = agdaToText (MT.d_showPolyType_134 (MP.d_pfunType_108 pfi))
  }

fromMResult :: MC.T_CompileResult_1512 -> CompileResult
fromMResult (MC.C_Parsed_1514 fis pfis) =
  Parsed (map fromMFunInfo fis) (map fromMPolyFunInfo pfis)
fromMResult (MC.C_Checked_1516 _)  = Checked
fromMResult (MC.C_Built_1518 asm)  = Built (agdaToText asm)
fromMResult (MC.C_Error_1520 err)  = Error (agdaToText err)

------------------------------------------------------------------------
-- One-shot legacy pipeline
------------------------------------------------------------------------

compile :: Stage -> Bool -> Arch -> Text -> CompileResult
compile stage doOpt arch source =
  fromMResult (MC.d_compile_1568 MCIR.C_Heap_8 (toMStage stage) doOpt (toMArch arch) (textToAgda source))

------------------------------------------------------------------------
-- AST-level pipeline
------------------------------------------------------------------------

-- | Parse a single .once source into a Module AST.
-- Returns `Left err` if the source fails to parse cleanly (including
-- silent-drop cases like dotted primitive names or TVars in type
-- position — see plan 0.6 Phase A). Agda-side `parseSourceToModule`
-- now uses the strict parser, so these failures surface rather than
-- silently producing a module with missing decls.
parseSource :: Text -> Either Text Module
parseSource source =
  case MC.d_parseSourceToModule_624 (textToAgda source) of
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
  [ ImportRef (map agdaToText (MEN.d_import'45'path_50 pr))
              (fmap agdaToText (MEN.d_import'45'alias_54 pr))
  | pr <- MEN.d_module'45'imports_34 m
  ]

-- | Does the module define a top-level `main`? This — not a CLI flag — is what
-- distinguishes a PROGRAM (has `main`, whose entry `once_main` `_start` calls)
-- from a LIBRARY (no `main`). Mirrors `moduleImports`' decl inspection.
-- D162: the predicate itself lives in Agda now (`Once.Extract.Names`). The
-- Haskell version pattern-matched the `DFunDef` constructor with three fields, a stale
-- mirror of the constructor's ARITY — it broke loudly on 2026-09-08 only
-- because the field COUNT changed.
moduleHasMain :: Module -> Bool
moduleHasMain (Module m) = MEN.d_module'45'has'45'main_6 m

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
  map agdaToText (MW.d_warningsFor_378 (toMArch arch) (textToAgda src) (unsafeCoerce m))

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
      agdaResult = MMR.d_resolveImports_904 (unsafeCoerce agdaMap) (unsafeCoerce userMod)
  in case agdaResult of
       MSum.C_inj'8321'_38 err -> Left (agdaToText err)
       MSum.C_inj'8322'_42 r   -> Right (Resolved (unsafeCoerce r))
  where
    mapEntry :: ([Text], Module) -> MSigma.T_Σ_14
    mapEntry (path, Module m) =
      MSigma.C__'44'__32 (unsafeCoerce (map textToAgda path :: [Text])) (unsafeCoerce m)

-- | Compile a pre-resolved Module through the selected stage.
-- Equivalent to `compile` but skips the initial parse step — used by
-- the AST-level pipeline after `resolveImports` produces a flat Module.
--
-- Routes through `Once.Adequacy.Compile.compile-cli-asm` (Plan 0.10:
-- extracted = verified). The verified path is currently a thin
-- wrapper around `compileFromModule` for Build, with one named
-- trusted-base postulate (`string-to-bytes` — GNU `as` conformance,
-- the B2 stance). When B1 (in-Agda assembler) lands, the postulate
-- goes away and this binding stays the same.
-- | The compiler in allocation mode `Heap`, the mode the apex covers (plan 0.131 A:
-- the CLI has no `--alloc`).
compileFromModule :: Stage -> Bool -> Arch -> Resolved -> CompileResult
compileFromModule stage doOpt arch (Resolved mod_) =
  fromMResult
    (MC.d_compileFromModule_1770
       MCIR.C_Heap_8 (toMStage stage) doOpt (toMArch arch) (unsafeCoerce mod_))

-- | Each compiled function's IR as text, unoptimized (`False`) or optimized
-- (`True`), or the compiler's error (`Once.Compile.Dump.dumpIR`, plan 0.39).
dumpIRFromModule :: Bool -> Resolved -> Either Text Text
dumpIRFromModule doOpt (Resolved mod_) =
  case MCD.d_dumpIR_16 doOpt (unsafeCoerce mod_) of
    MSum.C_inj'8321'_38 err -> Left (agdaToText err)
    MSum.C_inj'8322'_42 out -> Right (agdaToText out)

-- | The static costs of the module's program image, optimized (`True`) or
-- not, or the compiler's error (`Once.Measure.statsOf`).
statsFromModule :: Bool -> Resolved -> Either Text Text
statsFromModule doOpt (Resolved mod_) =
  case MMe.d_statsOf_4 doOpt (unsafeCoerce mod_) of
    MSum.C_inj'8321'_38 err -> Left (agdaToText err)
    MSum.C_inj'8322'_42 out -> Right (agdaToText out)

-- | A source text in the canonical layout (`once fmt`, plan 0.124), or the
-- parser's error. The formatting is Agda's (`Once.Format.formatSource`).
formatSource :: Text -> Either Text Text
formatSource source =
  case MF.d_formatSource_14 (textToAgda source) of
    MSum.C_inj'8321'_38 err -> Left (agdaToText err)
    MSum.C_inj'8322'_42 out -> Right (agdaToText out)
