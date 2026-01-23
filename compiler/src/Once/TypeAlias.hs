-- | Type alias expansion
--
-- Pure textual operations for expanding type aliases before passing
-- types to the Agda-verified type checker. This is the only type-level
-- logic that remains in Haskell — all actual type checking is done by Agda.
module Once.TypeAlias
  ( TypeAliasEnv
  , emptyAliasEnv
  , extendAliasEnv
  , convertType
  , convertTypeWithAliases
  , substSType
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Once.Syntax (SType (..), Name)
import Once.Type (Type (..), Encoding (..))

-- | Type alias environment: maps alias names to (params, body)
type TypeAliasEnv = Map Name ([Name], SType)

-- | Empty type alias environment
emptyAliasEnv :: TypeAliasEnv
emptyAliasEnv = Map.empty

-- | Add a type alias to the environment
extendAliasEnv :: Name -> [Name] -> SType -> TypeAliasEnv -> TypeAliasEnv
extendAliasEnv name params body = Map.insert name (params, body)

-- | Convert surface type to internal type
convertType :: SType -> Type
convertType = convertTypeWithAliases emptyAliasEnv

-- | Convert surface type to internal type, expanding type aliases
convertTypeWithAliases :: TypeAliasEnv -> SType -> Type
convertTypeWithAliases aliases sty = case sty of
  STVar name ->
    -- Check if this is a 0-ary type alias
    case Map.lookup name aliases of
      Just ([], body) -> conv body  -- 0-ary alias: expand it
      Just (_, _) -> TVar name      -- Alias needs arguments: keep as variable
      Nothing -> TVar name          -- Not an alias: keep as variable
  STUnit -> TUnit
  STVoid -> TVoid
  STInt -> TInt
  STFloat -> TFloat
  STBuffer -> TBuffer
  STString enc -> TString enc
  STProduct a b -> TProduct (conv a) (conv b)
  STSum a b -> TSum (conv a) (conv b)
  STArrow a b -> TArrow (conv a) (conv b)
  STEff a b -> TEff (conv a) (conv b)
  STQuant _ t -> conv t  -- quantity tracked separately in context
  STApp name args ->
    -- Check if this is a type alias application
    case Map.lookup name aliases of
      Just (params, body) ->
        -- Expand the alias: substitute params with args in body
        let argSubst = Map.fromList (zip params args)
            expanded = substSType argSubst body
        in conv expanded
      Nothing ->
        -- Not an alias, keep as type application
        TApp name (map conv args)
  STFix t -> TFix (conv t)
  where
    conv = convertTypeWithAliases aliases

-- | Substitute type variables in a surface type
substSType :: Map Name SType -> SType -> SType
substSType subst sty = case sty of
  STVar name -> Map.findWithDefault (STVar name) name subst
  STUnit -> STUnit
  STVoid -> STVoid
  STInt -> STInt
  STFloat -> STFloat
  STBuffer -> STBuffer
  STString enc -> STString enc
  STProduct a b -> STProduct (substSType subst a) (substSType subst b)
  STSum a b -> STSum (substSType subst a) (substSType subst b)
  STArrow a b -> STArrow (substSType subst a) (substSType subst b)
  STEff a b -> STEff (substSType subst a) (substSType subst b)
  STQuant q t -> STQuant q (substSType subst t)
  STApp name args -> STApp name (map (substSType subst) args)
  STFix t -> STFix (substSType subst t)
