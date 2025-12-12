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
generateHeader name ty = T.unlines $
  [ "#ifndef ONCE_" <> T.toUpper name <> "_H"
  , "#define ONCE_" <> T.toUpper name <> "_H"
  , ""
  ] ++
  (if needsStddef ty then ["#include <stddef.h>", ""] else []) ++
  [ "/* Type definitions */"
  , typeDefinitions ty
  , ""
  , "/* Function declaration */"
  , functionDecl name ty <> ";"
  , ""
  , "#endif"
  ]
  where
    -- Need stddef.h for size_t (used by Buffer/String)
    needsStddef :: Type -> Bool
    needsStddef t = case t of
      TBuffer -> True
      TString _ -> True
      TProduct a b -> needsStddef a || needsStddef b
      TSum a b -> needsStddef a || needsStddef b
      TArrow a b -> needsStddef a || needsStddef b
      _ -> False

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
  , if needsBuffer ty then Just "typedef struct { const char* data; size_t len; } OnceBuffer;" else Nothing
  , if needsString ty then Just "typedef OnceBuffer OnceString;  /* Encoding erased at runtime */" else Nothing
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

    needsBuffer :: Type -> Bool
    needsBuffer t = case t of
      TBuffer -> True
      TString _ -> True  -- String needs Buffer typedef first
      TProduct a b -> needsBuffer a || needsBuffer b
      TSum a b -> needsBuffer a || needsBuffer b
      TArrow a b -> needsBuffer a || needsBuffer b
      _ -> False

    needsString :: Type -> Bool
    needsString t = case t of
      TString _ -> True
      TProduct a b -> needsString a || needsString b
      TSum a b -> needsString a || needsString b
      TArrow a b -> needsString a || needsString b
      _ -> False

-- | Generate C type name
cTypeName :: Type -> Text
cTypeName ty = case ty of
  TVar _ -> "void*"
  TUnit -> "void*"  -- Unit represented as NULL
  TVoid -> "void"
  TInt -> "int"
  TBuffer -> "OnceBuffer"
  TString _ -> "OnceString"  -- Encoding erased at runtime
  TProduct _ _ -> "OncePair"
  TSum _ _ -> "OnceSum"
  TArrow _ _ -> "void*"  -- Function pointers (not used for swap)
  TApp _ _ -> "void*"    -- Type applications (polymorphic, boxed)
  TFix _ -> "void*"      -- Fixed-point types (recursive, boxed)

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

  Var n -> "once_" <> n <> "(" <> var <> ")"  -- treat as function call

  LocalVar n -> n  -- Local variable: just use the name

  Prim n _ _ -> "once_" <> n <> "(" <> var <> ")"

  StringLit s ->
    -- String literals are constant morphisms: Unit -> String Utf8
    -- They ignore their input and return the string
    -- Since we're in expression context, generate inline struct
    "(OnceString){ .data = " <> cStringLiteral s <> ", .len = " <> tshow (T.length s) <> " }"

  -- Recursive type operations
  -- At runtime, Fix F and F (Fix F) have the same representation (boxed pointer)
  Fold _ -> var    -- fold is identity at runtime (wraps into Fix)
  Unfold _ -> var  -- unfold is identity at runtime (unwraps from Fix)

  -- Let binding: use GCC statement expression ({ ... })
  -- let x = e1 in e2 => ({ typeof(e1) x = e1; e2; })
  -- Using GCC typeof extension to infer the type automatically
  Let x e1 e2 ->
    let e1Code = generateExpr e1 var
    in "({ typeof(" <> e1Code <> ") " <> x <> " = " <> e1Code <> "; " <> generateExpr e2 x <> "; })"

-- | Convert Text to C string literal (with escaping)
cStringLiteral :: Text -> Text
cStringLiteral s = "\"" <> T.concatMap escapeChar s <> "\""
  where
    escapeChar :: Char -> Text
    escapeChar c = case c of
      '\n' -> "\\n"
      '\t' -> "\\t"
      '\r' -> "\\r"
      '\\' -> "\\\\"
      '"'  -> "\\\""
      _    -> T.singleton c

-- | Show for Text
tshow :: Show a => a -> Text
tshow = T.pack . show
