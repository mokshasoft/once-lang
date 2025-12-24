module Once.Backend.C
  ( generateC
  , generateHeader
  , generateSource
  , CModule (..)
  ) where

import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import Debug.Trace (trace)

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
      TEff a b -> needsStddef a || needsStddef b  -- D032: Eff same as Arrow at runtime
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
-- These definitions match the interpretation files exactly to avoid conflicts
typeDefinitions :: Type -> Text
typeDefinitions ty =
  let typeDefs = catMaybes
        [ if needsString ty || needsBuffer ty then Just "typedef struct { const char* data; size_t len; } OnceString;" else Nothing
        , if needsBuffer ty then Just "typedef struct { void* data; size_t len; } OnceBuffer;" else Nothing
        , if needsPair ty then Just "typedef struct { void* fst; void* snd; } OncePair;" else Nothing
        , if needsSum ty then Just "typedef struct { int tag; void* value; } OnceSum;" else Nothing
        ]
  in if null typeDefs
     then ""
     else T.unlines $
       [ "#include <stddef.h>"
       , ""
       , "#ifndef ONCE_TYPES_DEFINED"
       , "#define ONCE_TYPES_DEFINED"
       ] ++ typeDefs ++
       [ "#endif"
       ]
  where
    needsPair :: Type -> Bool
    needsPair t = case t of
      TProduct _ _ -> True
      TSum a b -> needsPair a || needsPair b
      TArrow a b -> needsPair a || needsPair b
      TEff a b -> needsPair a || needsPair b  -- D032
      _ -> False

    needsSum :: Type -> Bool
    needsSum t = case t of
      TSum _ _ -> True
      TProduct a b -> needsSum a || needsSum b
      TArrow a b -> needsSum a || needsSum b
      TEff a b -> needsSum a || needsSum b  -- D032
      _ -> False

    needsBuffer :: Type -> Bool
    needsBuffer t = case t of
      TBuffer -> True
      TString _ -> True  -- String needs Buffer typedef first
      TProduct a b -> needsBuffer a || needsBuffer b
      TSum a b -> needsBuffer a || needsBuffer b
      TArrow a b -> needsBuffer a || needsBuffer b
      TEff a b -> needsBuffer a || needsBuffer b  -- D032
      _ -> False

    needsString :: Type -> Bool
    needsString t = case t of
      TString _ -> True
      TProduct a b -> needsString a || needsString b
      TSum a b -> needsString a || needsString b
      TArrow a b -> needsString a || needsString b
      TEff a b -> needsString a || needsString b  -- D032
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
  TEff _ _ -> "void*"    -- D032: Effectful morphisms same as functions at runtime
  TApp _ _ -> "void*"    -- Type applications (polymorphic, boxed)
  TFix _ -> "void*"      -- Fixed-point types (recursive, boxed)

-- | Generate function declaration
functionDecl :: Name -> Type -> Text
functionDecl name ty = case ty of
  TArrow inTy outTy ->
    cTypeName outTy <> " once_" <> name <> "(" <> cTypeName inTy <> " x)"
  TEff inTy outTy ->  -- D032: Eff same as Arrow at runtime
    cTypeName outTy <> " once_" <> name <> "(" <> cTypeName inTy <> " x)"
  _ -> "void* once_" <> name <> "(void)"

-- | Check if a variable expression needs to be cast to OncePair* before accessing .fst/.snd
-- This happens when the expression is the result of a previous pair access:
-- - ".fst" or ".snd" suffix (first level access like _tuple.fst)
-- - ")->fst" or ")->snd" suffix (deeper level access like ((OncePair*)x)->fst)
needsPairCast :: Text -> Bool
needsPairCast var =
  ".fst" `T.isSuffixOf` var || ".snd" `T.isSuffixOf` var ||
  ")->fst" `T.isSuffixOf` var || ")->snd" `T.isSuffixOf` var

-- | Generate C expression from IR
-- The 'var' parameter is the name of the input variable
generateExpr :: IR -> Text -> Text
generateExpr ir var = trace ("generateExpr: " ++ take 50 (show ir) ++ " var=" ++ T.unpack var) $ case ir of
  Id _ -> var

  -- When accessing nested pairs, the intermediate .fst/.snd returns void*
  -- which needs to be cast to OncePair* before accessing its members.
  -- Check for both ".fst"/".snd" (first level) and ")->fst"/")->snd" (deeper levels)
  Fst _ _ ->
    trace ("  Fst case hit, var=" ++ T.unpack var ++ " needsCast=" ++ show (needsPairCast var)) $
    if needsPairCast var
      then "((OncePair*)" <> var <> ")->fst"
      else var <> ".fst"

  Snd _ _ ->
    trace ("  Snd case hit, var=" ++ T.unpack var ++ " needsCast=" ++ show (needsPairCast var)) $
    if needsPairCast var
      then "((OncePair*)" <> var <> ")->snd"
      else var <> ".snd"

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

  -- Curry x body: bind input to x and evaluate body
  -- From lambda elaboration: \x -> e becomes Curry x e'
  -- The body contains LocalVar x references to the parameter
  Curry paramName body ->
    "({ typeof(" <> var <> ") " <> paramName <> " = " <> var <> "; " <>
    generateExpr body paramName <> "; })"

  Apply _ _ -> "/* apply not yet implemented */ ((void*)0)"

  Var n -> "once_" <> n <> "(" <> var <> ")"  -- treat as function call

  LocalVar n -> n  -- Local variable: just use the name

  FunRef n -> "(void*)once_" <> n  -- Function reference (pointer, not call)

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
