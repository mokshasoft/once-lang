------------------------------------------------------------------------
-- Once.Backend.C.CodeGen
--
-- C code generation from categorical IR.
-- Converts typed IR morphisms to C expression text.
--
-- This is extracted via MAlonzo to provide verified C code generation.
------------------------------------------------------------------------

module Once.Backend.C.CodeGen where

open import Data.String using (String; _++_)
open import Once.IR
open import Once.Type
open import Once.Backend.C.Emit

------------------------------------------------------------------------
-- Core expression code generation
------------------------------------------------------------------------

-- | Generate a C expression from an IR morphism and input variable name.
--
-- Each IR constructor maps to a C expression that transforms the input:
--   id        → var (identity)
--   g ∘ f     → g(f(var)) (composition)
--   fst/snd   → pair access with casting
--   ⟨f, g⟩    → compound literal pair
--   terminal  → NULL
--   inl/inr   → tagged sum
--   [f, g]    → ternary on tag
--   curry f   → GCC statement expression binding input
--   apply     → not implemented (requires closures)
--   fold/unfold/arr → identity at runtime
--   Prim name → function call
--
compile-c-expr : ∀ {A B} → IR A B → String → String
compile-c-expr id var = var

compile-c-expr (g ∘ f) var =
  compile-c-expr g (compile-c-expr f var)

compile-c-expr fst var = pairAccess var "fst"

compile-c-expr snd var = pairAccess var "snd"

compile-c-expr (⟨ f , g ⟩ _) var =
  "(OncePair){ .fst = " ++ compile-c-expr f var ++
  ", .snd = " ++ compile-c-expr g var ++ " }"

compile-c-expr terminal var = "((void*)0)"

compile-c-expr (inl _) var =
  "(OnceSum){ .tag = 0, .value = " ++ var ++ " }"

compile-c-expr (inr _) var =
  "(OnceSum){ .tag = 1, .value = " ++ var ++ " }"

compile-c-expr [ l , r ] var =
  "(" ++ var ++ ".tag == 0 ? " ++
  compile-c-expr l (var ++ ".value") ++ " : " ++
  compile-c-expr r (var ++ ".value") ++ ")"

compile-c-expr initial var = var

compile-c-expr (curry f _) var =
  "({ typeof(" ++ var ++ ") _ = " ++ var ++ "; " ++
  compile-c-expr f "_" ++ "; })"

compile-c-expr apply var =
  "/* apply not yet implemented */ ((void*)0)"

compile-c-expr fold var = var
compile-c-expr unfold var = var
compile-c-expr arr var = var

compile-c-expr (Prim name) var =
  "once_" ++ name ++ "(" ++ var ++ ")"

------------------------------------------------------------------------
-- Function-level code generation
------------------------------------------------------------------------

-- | Generate a complete C function definition.
-- Takes the declared function type, function name, and IR body.
-- Produces: retType once_name(argType x) { return expr; }
compile-c-function : Type → String → ∀ {A B} → IR A B → String
compile-c-function ty name ir =
  functionDecl ty name ++ " {\n    return " ++
  compile-c-expr ir "x" ++ ";\n}"
