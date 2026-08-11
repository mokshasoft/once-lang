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
  , ImportRef (..)
    -- * One-shot compilation (legacy)
  , compile
    -- * Allocation mode (Plan 0.14 follow-up — wired from CLI --alloc)
  , AllocMode (..)
    -- * AST-level pipeline
  , parseSource
  , moduleImports
  , moduleHasMain
  , resolveImports
  , compileFromModule
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as MSigma
import qualified MAlonzo.Code.Data.Sum.Base as MSum
import qualified MAlonzo.Code.Once.Compile as MC
import qualified MAlonzo.Code.Once.IR as MCIR
import qualified MAlonzo.Code.Once.Adequacy.Compile as MVC
import qualified MAlonzo.Code.Once.Target.Arch as MTA
import qualified MAlonzo.Code.Once.Parser as MP
import qualified MAlonzo.Code.Once.Parser.Module.Core as MMC
import qualified MAlonzo.Code.Once.Parser.Module.Resolve as MMR
import qualified MAlonzo.Code.Once.Type as MT

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
newtype Module = Module MMC.T_Module_44

-- | An `import` decl seen inside a parsed module. Haskell uses this
-- to decide which files to load before calling `resolveImports`.
data ImportRef = ImportRef
  { importPath  :: [Text]       -- ^ Dotted module path (e.g. ["I","Foo","Bar"])
  , importAlias :: Maybe Text   -- ^ Alias from `as X`, or Nothing
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- MAlonzo conversion (update suffixes after regenerating)
------------------------------------------------------------------------

toMStage :: Stage -> MC.T_Stage_778
toMStage Parse = MC.C_Parse_780
toMStage Check = MC.C_Check_782
toMStage Build = MC.C_Build_784

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

fromMFunInfo :: MP.T_FunInfo_96 -> FunSig
fromMFunInfo fi = FunSig
  { funSigName = agdaToText (MP.d_funName_108 fi)
    -- D007: funType is now `Maybe Type` (Nothing = no explicit sig, inferred).
    -- MAlonzo's Maybe is Haskell's Maybe (Just/Nothing pattern synonyms).
  , funSigType = case MP.d_funType_110 fi of
      Just ty -> agdaToText (MT.d_showType_206 ty)
      Nothing -> T.pack "<inferred>"
  }

fromMPolyFunInfo :: MP.T_PolyFunInfo_120 -> PolyFunSig
fromMPolyFunInfo pfi = PolyFunSig
  { polyFunSigName = agdaToText (MP.d_pfunName_130 pfi)
  , polyFunSigType = agdaToText (MT.d_showPolyType_468 (MP.d_pfunType_132 pfi))
  }

fromMResult :: MC.T_CompileResult_786 -> CompileResult
fromMResult (MC.C_Parsed_788 fis pfis) =
  Parsed (map fromMFunInfo fis) (map fromMPolyFunInfo pfis)
fromMResult (MC.C_Checked_790 _)  = Checked
fromMResult (MC.C_Built_792 asm)  = Built (agdaToText asm)
fromMResult (MC.C_Error_794 err)  = Error (agdaToText err)

------------------------------------------------------------------------
-- One-shot legacy pipeline
------------------------------------------------------------------------

compile :: Stage -> Bool -> Arch -> Text -> CompileResult
compile stage doOpt arch source =
  fromMResult (MC.d_compile_830 (toMAllocMode AllocHeap) (toMStage stage) doOpt (toMArch arch) (textToAgda source))

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
  case MC.d_parseSourceToModule_552 (textToAgda source) of
    MSum.C_inj'8321'_38 err -> Left (agdaToText err)
    MSum.C_inj'8322'_42 m   -> Right (Module (unsafeCoerce m))

-- | Extract just the `import` declarations from a parsed Module.
-- Haskell uses this to decide which files to read + parse next.
moduleImports :: Module -> [ImportRef]
moduleImports (Module m) =
  [ ImportRef (map agdaToText (MMC.d_path_26 i))
              (fmap agdaToText (MMC.d_alias_28 i))
  | MMC.C_DImport_42 i <- MMC.d_decls_48 m
  ]

-- | Does the module define a top-level `main`? This — not a CLI flag — is what
-- distinguishes a PROGRAM (has `main`, gets an entry point via `maybeWrapMain`)
-- from a LIBRARY (no `main`). Mirrors `moduleImports`' decl inspection.
moduleHasMain :: Module -> Bool
moduleHasMain (Module m) = any isMain (MMC.d_decls_48 m)
  where
    isMain (MMC.C_DFunDef_36 name _ _) = agdaToText name == T.pack "main"
    isMain _                           = False

-- | Flatten imports: for each `DImport path (just alias)` in the
-- user's module, substitute the primitives of the imported module
-- (owner-tagged with the alias), dropping the `DImport` itself.
--
-- The caller must supply a `ModuleMap` containing every transitive
-- dependency, already fully resolved (i.e. each entry's own
-- `DImport`s have been flattened). Haskell builds this by
-- topologically sorting and resolving bottom-up.
resolveImports
  :: [([Text], Module)]   -- ^ Map from dotted import path to resolved Module
  -> Module               -- ^ User's module
  -> Either Text Module
resolveImports modMap (Module userMod) =
  let agdaMap = map mapEntry modMap
      agdaResult = MMR.d_resolveImports_690 (unsafeCoerce agdaMap) (unsafeCoerce userMod)
  in case agdaResult of
       MSum.C_inj'8321'_38 err -> Left (agdaToText err)
       MSum.C_inj'8322'_42 m   -> Right (Module (unsafeCoerce m))
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
-- | Default allocation mode for surface-level pair/inl/inr/curry/let.
-- Threaded from CLI's --alloc flag through to the elaborator. Plan 0.14
-- follow-up (2026-05-18): previously hardcoded to Heap in the
-- elaborator, silently dropping the user's CLI choice.
data AllocMode = AllocStack | AllocHeap
  deriving (Eq, Show)

toMAllocMode :: AllocMode -> MCIR.T_AllocMode_4
toMAllocMode AllocStack = MCIR.C_Stack_6
toMAllocMode AllocHeap  = MCIR.C_Heap_8

compileFromModule :: AllocMode -> Stage -> Bool -> Arch -> Module -> CompileResult
compileFromModule m stage doOpt arch (Module mod_) =
  fromMResult
    (MVC.d_compile'45'cli'45'asm_26
       (toMAllocMode m) (toMStage stage) doOpt (toMArch arch) (unsafeCoerce mod_))
