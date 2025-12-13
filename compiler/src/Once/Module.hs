{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}

-- | Module resolution for Once's import system.
--
-- Handles:
-- - Path abbreviations: I. -> Interpretations., D. -> Derived.
-- - Module loading from Strata directory
-- - Cycle detection
-- - Qualified name lookup
module Once.Module
  ( -- * Module Environment
    ModuleEnv (..)
  , LoadedModule (..)
  , DeclInfo (..)
  , emptyModuleEnv
    -- * Path Resolution
  , expandAbbreviations
  , moduleToFilePath
    -- * Module Loading
  , loadModuleFile
  , resolveImports
  , buildExports
    -- * Lookup
  , lookupQualified
  , resolveAlias
    -- * Errors
  , ModuleError (..)
  , formatModuleError
  ) where

import Control.Monad (foldM)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist)
import System.FilePath ((</>), (<.>))

import Once.Syntax (Module (..), Decl (..), Import (..), ModuleName, Name, SType)
import Once.Parser (parseModule)

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
  | UnresolvedQualified Name ModuleName
  | UnknownAlias Name
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
  UnresolvedQualified name modPath ->
    "Name '" <> name <> "' not found in module " <> formatModPath modPath
  UnknownAlias alias ->
    "Unknown module alias: " <> alias
  AbbreviationNotFound abbrev ->
    "Unknown path abbreviation: " <> abbrev <> ". (Valid: I for Interpretations, D for Derived)"
  where
    formatModPath = T.intercalate "."

-- | A loaded module with its exports
data LoadedModule = LoadedModule
  { lmModule  :: Module              -- ^ The parsed module
  , lmPath    :: FilePath            -- ^ Source file path
  , lmExports :: Map Name DeclInfo   -- ^ Exported names with their declarations
  , lmCPath   :: Maybe FilePath      -- ^ Companion .c file (for interpretations)
  } deriving (Show)

-- | Information about an exported declaration
data DeclInfo = DeclInfo
  { diType :: Maybe SType   -- ^ Type signature (if any)
  , diDecl :: Decl          -- ^ The declaration itself
  } deriving (Show)

-- | Module environment: tracks all loaded modules and aliases
data ModuleEnv = ModuleEnv
  { meModules    :: Map ModuleName LoadedModule  -- ^ Loaded modules by canonical path
  , meAliases    :: Map Name ModuleName          -- ^ Alias -> canonical module path
  , meStrataPath :: FilePath                     -- ^ Base path for Strata directory
  } deriving (Show)

-- | Create an empty module environment
emptyModuleEnv :: FilePath -> ModuleEnv
emptyModuleEnv strataPath = ModuleEnv
  { meModules = Map.empty
  , meAliases = Map.empty
  , meStrataPath = strataPath
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
        -- Otherwise, it's not an abbreviation (shouldn't happen with uppercase)
        | otherwise -> Right (prefix : rest)
  | otherwise = Right (prefix : rest)  -- Multi-char, not an abbreviation

-- | Convert module path to file path
-- ["Derived", "Canonical"] -> "Strata/Derived/Canonical.once"
moduleToFilePath :: FilePath -> ModuleName -> FilePath
moduleToFilePath strataPath modPath =
  strataPath </> foldr1 (</>) (map T.unpack modPath) <.> "once"

-- | Get companion C file path (for interpretation modules)
-- ["Interpretations", "Linux", "Syscalls"] -> "Strata/Interpretations/Linux/Syscalls.c"
companionCPath :: FilePath -> ModuleName -> FilePath
companionCPath strataPath modPath =
  strataPath </> foldr1 (</>) (map T.unpack modPath) <.> "c"

-- | Build exports map from a module's declarations
-- Associates each name with its type signature and definition
buildExports :: Module -> Map Name DeclInfo
buildExports m = foldr addDecl Map.empty (moduleDecls m)
  where
    addDecl :: Decl -> Map Name DeclInfo -> Map Name DeclInfo
    addDecl decl acc = case decl of
      TypeSig name sty ->
        -- Add or update type signature
        Map.alter (addType sty) name acc
      FunDef name alloc expr ->
        -- Add function definition
        Map.alter (addDef (FunDef name alloc expr)) name acc
      Primitive name sty ->
        -- Primitive has both type and "definition"
        Map.insert name (DeclInfo (Just sty) (Primitive name sty)) acc
      TypeAlias name params sty ->
        -- Type aliases are exported as-is
        Map.insert name (DeclInfo Nothing (TypeAlias name params sty)) acc

    addType sty Nothing = Just (DeclInfo (Just sty) (TypeSig "" sty))  -- placeholder decl
    addType sty (Just info) = Just info { diType = Just sty }

    addDef decl Nothing = Just (DeclInfo Nothing decl)
    addDef decl (Just info) = Just info { diDecl = decl }

-- | Load a single module file
loadModuleFile :: FilePath -> ModuleName -> IO (Either ModuleError LoadedModule)
loadModuleFile strataPath modPath = do
  let oncePath = moduleToFilePath strataPath modPath
  exists <- doesFileExist oncePath
  if not exists
    then return $ Left (ModuleNotFound modPath oncePath)
    else do
      content <- TIO.readFile oncePath
      case parseModule content of
        Left err -> return $ Left (ModuleParseError modPath (T.pack $ show err))
        Right m -> do
          -- Check for companion .c file
          let cPath = companionCPath strataPath modPath
          hasC <- doesFileExist cPath
          return $ Right LoadedModule
            { lmModule = m
            , lmPath = oncePath
            , lmExports = buildExports m
            , lmCPath = if hasC then Just cPath else Nothing
            }

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
-- import D.Canonical as C -> "C" -> ["Derived", "Canonical"]
buildAliasMap :: [Import] -> Map Name ModuleName
buildAliasMap imports = Map.fromList
  [ (alias, importModule imp)
  | imp <- imports
  , Just alias <- [importAlias imp]
  ]

-- | Load modules with cycle detection
-- Uses a "loading" set to detect cycles
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
        -- Load the module
        result <- loadModuleFile (meStrataPath env) modPath
        case result of
          Left err -> return $ Left err
          Right lm -> do
            -- Add to environment
            let env' = env { meModules = Map.insert modPath lm (meModules env) }
            -- Recursively load this module's imports
            let subImports = moduleImports (lmModule lm)
            case traverse (\imp -> expandAbbreviations (importModule imp)) subImports of
              Left err -> return $ Left err
              Right expandedPaths -> do
                result' <- loadModulesWithCycleCheck env' loading' expandedPaths
                case result' of
                  Left err -> return $ Left err
                  Right env'' -> loadModulesWithCycleCheck env'' loading rest

-- | Resolve an alias to a canonical module path
-- If the path is a single component matching an alias, return the target
-- Otherwise return the path unchanged
resolveAlias :: ModuleEnv -> ModuleName -> ModuleName
resolveAlias env [single] = Map.findWithDefault [single] single (meAliases env)
resolveAlias _env path = path

-- | Look up a qualified name in the module environment
-- swap@C -> look up "swap" in module "C" (resolving aliases first, then abbreviations)
lookupQualified :: Name -> ModuleName -> ModuleEnv -> Either ModuleError DeclInfo
lookupQualified name modPath env = do
  -- First, try to resolve as an alias (single-component paths like "S" from "import ... as S")
  let aliasResolved = resolveAlias env modPath
  -- If alias resolution changed the path, use that; otherwise expand abbreviations
  canonicalPath <- if aliasResolved /= modPath
    then Right aliasResolved  -- It was an alias, already resolved
    else expandAbbreviations modPath  -- Not an alias, try abbreviation expansion
  -- Look up the module
  case Map.lookup canonicalPath (meModules env) of
    Nothing -> Left (ModuleNotFound canonicalPath (moduleToFilePath (meStrataPath env) canonicalPath))
    Just lm ->
      -- Look up the name in the module's exports
      case Map.lookup name (lmExports lm) of
        Nothing -> Left (UnresolvedQualified name canonicalPath)
        Just info -> Right info
