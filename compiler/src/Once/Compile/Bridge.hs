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
    -- * Module AST (opaque handle + import inspection)
  , Module
  , ImportRef (..)
    -- * One-shot compilation (legacy)
  , compile
    -- * AST-level pipeline
  , parseSource
  , moduleImports
  , resolveImports
  , compileFromModule
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Unsafe.Coerce (unsafeCoerce)

import qualified MAlonzo.Code.Agda.Builtin.Sigma as MSigma
import qualified MAlonzo.Code.Data.Sum.Base as MSum
import qualified MAlonzo.Code.Once.Compile as MC
import qualified MAlonzo.Code.Once.Parser as MP
import qualified MAlonzo.Code.Once.Parser.Module.Core as MMC
import qualified MAlonzo.Code.Once.Parser.Module.Resolve as MMR
import qualified MAlonzo.Code.Once.Type as MT

------------------------------------------------------------------------
-- Haskell types (stable API)
------------------------------------------------------------------------

data Stage = Parse | Check | Build
  deriving (Eq, Show)

data Arch = X86_64
  deriving (Eq, Show)

data FunSig = FunSig
  { funSigName :: Text
  , funSigType :: Text
  } deriving (Eq, Show)

data CompileResult
  = Parsed [FunSig]
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
  { importPath  :: [Text]       -- ^ Dotted module path (e.g. ["I","Linux","Syscalls"])
  , importAlias :: Maybe Text   -- ^ Alias from `as X`, or Nothing
  } deriving (Eq, Show)

------------------------------------------------------------------------
-- MAlonzo conversion (update suffixes after regenerating)
------------------------------------------------------------------------

toMStage :: Stage -> MC.T_Stage_294
toMStage Parse = MC.C_Parse_296
toMStage Check = MC.C_Check_298
toMStage Build = MC.C_Build_300

toMArch :: Arch -> MC.T_Arch_274
toMArch X86_64 = MC.C_x86'45'64_276

-- | Agda strings are Haskell `Text` at runtime (MAlonzo primitive binding).
agdaToText :: a -> Text
agdaToText = unsafeCoerce

textToAgda :: Text -> a
textToAgda = unsafeCoerce

fromMFunInfo :: MP.T_FunInfo_38 -> FunSig
fromMFunInfo fi = FunSig
  { funSigName = agdaToText (MP.d_funName_48 fi)
  , funSigType = agdaToText (MT.d_showType_132 (MP.d_funType_50 fi))
  }

fromMResult :: MC.T_CompileResult_302 -> CompileResult
fromMResult (MC.C_Parsed_304 fis) = Parsed (map fromMFunInfo fis)
fromMResult (MC.C_Checked_306 _)  = Checked
fromMResult (MC.C_Built_308 asm)  = Built (agdaToText asm)
fromMResult (MC.C_Error_310 err)  = Error (agdaToText err)

------------------------------------------------------------------------
-- One-shot legacy pipeline
------------------------------------------------------------------------

compile :: Stage -> Bool -> Arch -> Text -> CompileResult
compile stage doOpt arch source =
  fromMResult (MC.d_compile_324 (toMStage stage) doOpt (toMArch arch) (textToAgda source))

------------------------------------------------------------------------
-- AST-level pipeline
------------------------------------------------------------------------

-- | Parse a single .once source into a Module AST.
-- Returns Nothing on parse failure.
parseSource :: Text -> Maybe Module
parseSource source = fmap (Module . unsafeCoerce)
                          (MC.d_parseSourceToModule_240 (textToAgda source))

-- | Extract just the `import` declarations from a parsed Module.
-- Haskell uses this to decide which files to read + parse next.
moduleImports :: Module -> [ImportRef]
moduleImports (Module m) =
  [ ImportRef (map agdaToText (MMC.d_path_26 i))
              (fmap agdaToText (MMC.d_alias_28 i))
  | MMC.C_DImport_42 i <- MMC.d_decls_48 m
  ]

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
      agdaResult = MMR.d_resolveImports_172 (unsafeCoerce agdaMap) (unsafeCoerce userMod)
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
compileFromModule :: Stage -> Bool -> Arch -> Module -> CompileResult
compileFromModule stage doOpt arch (Module m) =
  fromMResult
    (MC.d_compileFromModule_376 (toMStage stage) doOpt (toMArch arch) (unsafeCoerce m))
