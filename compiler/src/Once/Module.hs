{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Module resolution for Once's import system.
--
-- Handles:
-- - Path abbreviations: I. -> Interpretations., D. -> Derived.
-- - Module loading from Strata directory
-- - Cycle detection
module Once.Module
  ( -- * Types
    Name
  , ModuleName
  , Import (..)
  , AllocStrategy (..)
    -- * Module Environment
  , ModuleEnv (..)
  , LoadedModule (..)
  , emptyModuleEnv
    -- * Path Resolution
  , expandAbbreviations
  , moduleToFilePath
    -- * Module Loading
  , loadModuleFile
  , resolveImports
  , extractImports
  , buildImportsForTypeChecker
    -- * Errors
  , ModuleError (..)
  , formatModuleError
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist)
import System.FilePath ((</>), (<.>))

import qualified MAlonzo.Code.Once.Parser as MP
import qualified MAlonzo.Code.Once.Parser.Module as MPM
import qualified MAlonzo.Code.Once.Type as MT

-- | Variable and type names
type Name = Text

-- | Module names (dot-separated path)
type ModuleName = [Text]

-- | Import declaration
data Import = Import
  { importModule :: ModuleName   -- ^ Module path: ["Canonical", "Product"]
  , importAlias  :: Maybe Name   -- ^ Optional alias: `import Foo as F`
  } deriving (Eq, Show)

-- | Allocation strategy for buffer outputs
data AllocStrategy
  = AllocStack    -- ^ Stack-allocated, automatic lifetime
  | AllocHeap     -- ^ Heap-allocated via malloc/free
  | AllocPool     -- ^ Fixed-size block pool
  | AllocArena    -- ^ Bump allocation, bulk free
  | AllocConst    -- ^ Read-only constant section (string literals)
  deriving (Eq, Show)

-- | Hardcoded path abbreviations
-- "I" -> ["Interpretations"]
-- "D" -> ["Derived"]
abbreviations :: Map Text [Text]
abbreviations = Map.fromList
  [ ("I", ["Interpretations"])
  , ("D", ["Derived"])
  ]

-- | Module errors
data ModuleError
  = ModuleNotFound ModuleName FilePath
  | ModuleParseError ModuleName Text
  | CyclicImport [ModuleName]
  | AbbreviationNotFound Text
  deriving (Eq, Show)

-- | Format a module error for display
formatModuleError :: ModuleError -> Text
formatModuleError = \case
  ModuleNotFound modPath path ->
    "Module not found: " <> formatModPath modPath <> "\n  Looked in: " <> T.pack path
  ModuleParseError modPath err ->
    "Parse error in module " <> formatModPath modPath <> ":\n" <> err
  CyclicImport cycle ->
    "Cyclic import detected: " <> T.intercalate " -> " (map formatModPath cycle)
  AbbreviationNotFound abbrev ->
    "Unknown path abbreviation: " <> abbrev <> ". (Valid: I for Interpretations, D for Derived)"
  where
    formatModPath = T.intercalate "."

-- | A loaded module
data LoadedModule = LoadedModule
  { lmPath       :: FilePath            -- ^ Source file path
  , lmTargetPath :: Maybe FilePath      -- ^ Target-specific implementation file (.c, .x86_64, etc.)
  , lmPrimitives :: [(Text, MT.T_Type_32)]  -- ^ Primitives exported by this module (name, type)
  }

instance Show LoadedModule where
  show lm = "LoadedModule { lmPath = " ++ show (lmPath lm) ++
            ", lmTargetPath = " ++ show (lmTargetPath lm) ++
            ", lmPrimitives = <" ++ show (length (lmPrimitives lm)) ++ " primitives> }"

-- | Module environment: tracks all loaded modules and aliases
data ModuleEnv = ModuleEnv
  { meModules    :: Map ModuleName LoadedModule  -- ^ Loaded modules by canonical path
  , meAliases    :: Map Name ModuleName          -- ^ Alias -> canonical module path
  , meStrataPath :: FilePath                     -- ^ Base path for Strata directory
  , meTargetExt  :: String                       -- ^ Target file extension (e.g., ".c", ".x86_64")
  } deriving (Show)

-- | Create an empty module environment
emptyModuleEnv :: FilePath -> String -> ModuleEnv
emptyModuleEnv strataPath targetExt = ModuleEnv
  { meModules = Map.empty
  , meAliases = Map.empty
  , meStrataPath = strataPath
  , meTargetExt = targetExt
  }

-- | Expand path abbreviations
-- "I.Linux.Syscalls" -> ["Interpretations", "Linux", "Syscalls"]
-- "D.Canonical" -> ["Derived", "Canonical"]
expandAbbreviations :: ModuleName -> Either ModuleError ModuleName
expandAbbreviations [] = Right []
expandAbbreviations (prefix : rest)
  | T.length prefix == 1 = case Map.lookup prefix abbreviations of
      Just expanded -> Right (expanded ++ rest)
      Nothing
        -- Single uppercase letter that's not a known abbreviation is an error
        | T.all (\c -> c >= 'A' && c <= 'Z') prefix ->
            Left (AbbreviationNotFound prefix)
        -- Otherwise, it's not an abbreviation
        | otherwise -> Right (prefix : rest)
  | otherwise = Right (prefix : rest)  -- Multi-char, not an abbreviation

-- | Convert module path to file path
-- ["Derived", "Canonical"] -> "Strata/Derived/Canonical.once"
moduleToFilePath :: FilePath -> ModuleName -> FilePath
moduleToFilePath strataPath modPath =
  strataPath </> foldr1 (</>) (map T.unpack modPath) <.> "once"

-- | Get target-specific implementation file path
targetFilePath :: FilePath -> String -> ModuleName -> FilePath
targetFilePath strataPath ext modPath =
  strataPath </> foldr1 (</>) (map T.unpack modPath) ++ ext

-- | Extract imports from an Agda-parsed module
extractImports :: MPM.T_Module_42 -> [Import]
extractImports (MPM.C_mkModule_48 decls) = go decls
  where
    go [] = []
    go (MPM.C_DImport_40 imp : rest) = fromAgdaImport imp : go rest
    go (_ : rest) = go rest

-- | Convert Agda Import to Haskell Import
fromAgdaImport :: MPM.T_Import_18 -> Import
fromAgdaImport (MPM.C_mkImport_28 path alias) = Import path alias

-- | Extract primitives from an Agda-parsed module
extractPrimitives :: MPM.T_Module_42 -> [(Text, MT.T_Type_32)]
extractPrimitives (MPM.C_mkModule_48 decls) = go decls
  where
    go [] = []
    go (MPM.C_DPrimitive_36 name ty : rest) = (name, ty) : go rest
    go (_ : rest) = go rest

-- | Load a single module file (returns loaded module and its imports for recursive resolution)
loadModuleFile :: FilePath -> String -> ModuleName -> IO (Either ModuleError (LoadedModule, [Import]))
loadModuleFile strataPath targetExt modPath = do
  let oncePath = moduleToFilePath strataPath modPath
  exists <- doesFileExist oncePath
  if not exists
    then return $ Left (ModuleNotFound modPath oncePath)
    else do
      content <- TIO.readFile oncePath
      case MP.d_parse_4 content of
        Nothing -> return $ Left (ModuleParseError modPath "parse failed")
        Just agdaModule -> do
          let tgtPath = targetFilePath strataPath targetExt modPath
          hasTarget <- doesFileExist tgtPath
          let imports = extractImports agdaModule
              prims = extractPrimitives agdaModule
          return $ Right
            ( LoadedModule
                { lmPath = oncePath
                , lmTargetPath = if hasTarget then Just tgtPath else Nothing
                , lmPrimitives = prims
                }
            , imports
            )

-- | Resolve all imports for a module, loading dependencies recursively
-- Detects cycles and returns error if found
resolveImports :: ModuleEnv -> [Import] -> IO (Either ModuleError ModuleEnv)
resolveImports env imports = do
  -- First, expand all abbreviations
  case traverse expandImportPath imports of
    Left err -> return $ Left err
    Right expandedImports -> do
      -- Load all modules with cycle detection
      result <- loadModulesWithCycleCheck env Set.empty (map importModule expandedImports)
      case result of
        Left err -> return $ Left err
        Right env' -> do
          -- Build alias map from imports
          let aliases = buildAliasMap expandedImports
          return $ Right env' { meAliases = Map.union aliases (meAliases env') }
  where
    expandImportPath :: Import -> Either ModuleError Import
    expandImportPath imp = do
      expanded <- expandAbbreviations (importModule imp)
      return imp { importModule = expanded }

-- | Build alias map from imports
buildAliasMap :: [Import] -> Map Name ModuleName
buildAliasMap imports = Map.fromList
  [ (alias, importModule imp)
  | imp <- imports
  , let alias = case importAlias imp of
          Just a -> a                        -- Explicit alias: import ... as A
          Nothing -> last (importModule imp) -- Implicit alias: last component
  ]

-- | Load modules with cycle detection
loadModulesWithCycleCheck ::
  ModuleEnv -> Set ModuleName -> [ModuleName] -> IO (Either ModuleError ModuleEnv)
loadModulesWithCycleCheck env _loading [] = return $ Right env
loadModulesWithCycleCheck env loading (modPath : rest) = do
  -- Check if already loaded
  if Map.member modPath (meModules env)
    then loadModulesWithCycleCheck env loading rest
    else if Set.member modPath loading
      -- Cycle detected!
      then return $ Left (CyclicImport (Set.toList loading ++ [modPath]))
      else do
        -- Mark as loading
        let loading' = Set.insert modPath loading
        -- Load the module (using target extension from environment)
        result <- loadModuleFile (meStrataPath env) (meTargetExt env) modPath
        case result of
          Left err -> return $ Left err
          Right (lm, subImports) -> do
            -- Add to environment
            let env' = env { meModules = Map.insert modPath lm (meModules env) }
            -- Recursively load this module's imports
            case traverse (\imp -> expandAbbreviations (importModule imp)) subImports of
              Left err -> return $ Left err
              Right expandedPaths -> do
                result' <- loadModulesWithCycleCheck env' loading' expandedPaths
                case result' of
                  Left err -> return $ Left err
                  Right env'' -> loadModulesWithCycleCheck env'' loading rest

-- | Build the imports list for the type checker from the module environment.
-- Returns list of (qualified_name, type) where qualified_name is "alias.name".
buildImportsForTypeChecker :: ModuleEnv -> [(Text, MT.T_Type_32)]
buildImportsForTypeChecker env =
  [ (alias <> "." <> name, ty)
  | (alias, modPath) <- Map.toList (meAliases env)
  , Just lm <- [Map.lookup modPath (meModules env)]
  , (name, ty) <- lmPrimitives lm
  ]
