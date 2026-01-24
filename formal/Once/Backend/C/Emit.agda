------------------------------------------------------------------------
-- Once.Backend.C.Emit
--
-- String helpers and C type emission for the C backend.
-- Converts Once types to C type names and provides utilities for
-- generating well-formed C expressions.
------------------------------------------------------------------------

module Once.Backend.C.Emit where

open import Data.String using (String; _++_; toList; fromList)
open import Data.List using (List; []; _∷_; reverse)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Char using (Char; _≟_)
open import Relation.Nullary using (yes; no)
open import Once.Type using (Type; Unit; Void; Int; Float; Str; Buffer;
                             _*_; _+_; _⇒[_]_; Eff; Fix; TVar)

------------------------------------------------------------------------
-- String helpers
------------------------------------------------------------------------

-- | Join strings with newlines
unlines : List String → String
unlines [] = ""
unlines (x ∷ []) = x
unlines (x ∷ xs) = x ++ "\n" ++ unlines xs

-- | Check if a list ends with a given suffix (by comparing reversed lists)
isSuffixOf : List Char → List Char → Bool
isSuffixOf suffix str = go (reverse suffix) (reverse str)
  where
    go : List Char → List Char → Bool
    go [] _ = true
    go (_ ∷ _) [] = false
    go (s ∷ ss) (c ∷ cs) with s ≟ c
    ... | yes _ = go ss cs
    ... | no  _ = false

-- | Check if a string ends with a given suffix string
endsWith : String → String → Bool
endsWith str suffix = isSuffixOf (toList suffix) (toList str)

------------------------------------------------------------------------
-- C type names
------------------------------------------------------------------------

-- | Map Once types to C type names
cTypeName : Type → String
cTypeName Unit          = "void*"
cTypeName Void          = "void"
cTypeName Int           = "int"
cTypeName Float         = "double"
cTypeName Str           = "OnceString"
cTypeName Buffer        = "OnceBuffer"
cTypeName (_ * _)       = "OncePair"
cTypeName (_ + _)       = "OnceSum"
cTypeName (_ ⇒[ _ ] _) = "void*"
cTypeName (Eff _ _)     = "void*"
cTypeName (Fix _)       = "void*"
cTypeName (TVar _)      = "void*"

------------------------------------------------------------------------
-- Pair access (needsPairCast logic)
------------------------------------------------------------------------

-- | Check if a variable expression needs casting to OncePair* before
-- accessing .fst/.snd. This happens when the expression is already
-- a pair member access (returning void*).
needsPairCast : String → Bool
needsPairCast var =
  endsWith var ".fst" ∨
  endsWith var ".snd" ∨
  endsWith var ")->fst" ∨
  endsWith var ")->snd"

-- | Generate pair field access with appropriate casting
pairAccess : String → String → String
pairAccess var member =
  if needsPairCast var
    then "((OncePair*)" ++ var ++ ")->" ++ member
    else var ++ "." ++ member

------------------------------------------------------------------------
-- C string escaping
------------------------------------------------------------------------

-- | Escape a single character for C string literal
escapeChar : Char → String
escapeChar '\n' = "\\n"
escapeChar '\t' = "\\t"
escapeChar '\r' = "\\r"
escapeChar '\\' = "\\\\"
escapeChar '"'  = "\\\""
escapeChar c    = fromList (c ∷ [])

-- | Escape a string for use in C string literal
escapeString : String → String
escapeString s = go (toList s)
  where
    go : List Char → String
    go [] = ""
    go (c ∷ cs) = escapeChar c ++ go cs

------------------------------------------------------------------------
-- Function declaration generation
------------------------------------------------------------------------

-- | Generate C function declaration from declared type and name
-- Arrow/Eff types produce: retType once_name(argType x)
-- Other types produce: void* once_name(void)
functionDecl : Type → String → String
functionDecl (a ⇒[ _ ] b) name =
  cTypeName b ++ " once_" ++ name ++ "(" ++ cTypeName a ++ " x)"
functionDecl (Eff a b) name =
  cTypeName b ++ " once_" ++ name ++ "(" ++ cTypeName a ++ " x)"
functionDecl _ name =
  "void* once_" ++ name ++ "(void)"
