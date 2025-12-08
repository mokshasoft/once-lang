module Once.Backend.C
  ( generateC
  , generateHeader
  , generateSource
  , CModule (..)
  ) where

import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T

import Once.IR (IR (..))
import Once.Type (Type (..), Name)

-- | Generated C module (header + source)
data CModule = CModule
  { cHeader :: Text   -- ^ .h file contents
  , cSource :: Text   -- ^ .c file contents
  } deriving (Eq, Show)

-- | Generate C code for a named function
generateC :: Name -> Type -> IR -> CModule
generateC name ty ir = CModule
  { cHeader = generateHeader name ty
  , cSource = generateSource name ty ir
  }

-- | Generate C header file
generateHeader :: Name -> Type -> Text
generateHeader name ty = T.unlines
  [ "#ifndef ONCE_" <> T.toUpper name <> "_H"
  , "#define ONCE_" <> T.toUpper name <> "_H"
  , ""
  , "/* Type definitions */"
  , typeDefinitions ty
  , ""
  , "/* Function declaration */"
  , functionDecl name ty <> ";"
  , ""
  , "#endif"
  ]

-- | Generate C source file
generateSource :: Name -> Type -> IR -> Text
generateSource name ty ir = T.unlines
  [ "#include \"once_" <> name <> ".h\""
  , ""
  , functionDecl name ty <> " {"
  , "    return " <> generateExpr ir "x" <> ";"
  , "}"
  ]

-- | Generate type definitions needed for a type
typeDefinitions :: Type -> Text
typeDefinitions ty = T.unlines $ catMaybes
  [ if needsPair ty then Just "typedef struct { void* fst; void* snd; } OncePair;" else Nothing
  , if needsSum ty then Just "typedef struct { int tag; void* value; } OnceSum;" else Nothing
  ]
  where
    needsPair :: Type -> Bool
    needsPair t = case t of
      TProduct _ _ -> True
      TSum a b -> needsPair a || needsPair b
      TArrow a b -> needsPair a || needsPair b
      _ -> False

    needsSum :: Type -> Bool
    needsSum t = case t of
      TSum _ _ -> True
      TProduct a b -> needsSum a || needsSum b
      TArrow a b -> needsSum a || needsSum b
      _ -> False

-- | Generate C type name
cTypeName :: Type -> Text
cTypeName ty = case ty of
  TVar _ -> "void*"
  TUnit -> "void*"  -- Unit represented as NULL
  TVoid -> "void"
  TInt -> "int"
  TProduct _ _ -> "OncePair"
  TSum _ _ -> "OnceSum"
  TArrow _ _ -> "void*"  -- Function pointers (not used for swap)

-- | Generate function declaration
functionDecl :: Name -> Type -> Text
functionDecl name ty = case ty of
  TArrow inTy outTy ->
    cTypeName outTy <> " once_" <> name <> "(" <> cTypeName inTy <> " x)"
  _ -> "void* once_" <> name <> "(void)"

-- | Generate C expression from IR
-- The 'var' parameter is the name of the input variable
generateExpr :: IR -> Text -> Text
generateExpr ir var = case ir of
  Id _ -> var

  Fst _ _ -> var <> ".fst"

  Snd _ _ -> var <> ".snd"

  Pair f g ->
    "(OncePair){ .fst = " <> generateExpr f var <>
    ", .snd = " <> generateExpr g var <> " }"

  Compose g f ->
    let inner = generateExpr f var
    in generateExpr g inner

  Terminal _ -> "((void*)0)"  -- NULL for Unit

  Inl _ _ -> "(OnceSum){ .tag = 0, .value = " <> var <> " }"

  Inr _ _ -> "(OnceSum){ .tag = 1, .value = " <> var <> " }"

  Case l r ->
    "(" <> var <> ".tag == 0 ? " <>
    generateExpr l (var <> ".value") <> " : " <>
    generateExpr r (var <> ".value") <> ")"

  Initial _ -> var  -- Void -> A (unreachable)

  Curry _ -> "/* curry not yet implemented */ ((void*)0)"

  Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"

  Var n -> n <> "(" <> var <> ")"  -- treat as function call

  Prim n _ _ -> n <> "(" <> var <> ")"
