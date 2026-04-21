-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Compile
--
-- General compilation pipeline: source → IR
-- Target-independent stages that are shared across all backends.
--
-- Pipeline:
--   1. Parse source text to Module
--   2. Extract functions with type signatures
--   3. For each function:
--      a. Validate (main must be Eff Unit A)
--      b. Type check and elaborate (RawExpr → SurfaceExpr)
--      c. Elaborate to IR (SurfaceExpr → IR)
--      d. Optimize (categorical laws)
--   4. Return IR for target-specific code generation
--
-- See D035: Two-Stage IR and MAlonzo Compilation
------------------------------------------------------------------------

module Once.Compile where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_; _==_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)

-- Re-export types
open import Once.Type public

-- Re-export Core IR
open import Once.CCC.IR public

-- Re-export Surface IR
open import Once.Surface.IR public
  using (SurfaceIR; Let; Prim)
  renaming
    ( id to S-id
    ; _∘_ to _S-∘_
    ; fst to S-fst
    ; snd to S-snd
    ; ⟨_,_⟩ to S-⟨_,_⟩
    ; inl to S-inl
    ; inr to S-inr
    ; [_,_] to S-[_,_]
    ; terminal to S-terminal
    ; initial to S-initial
    ; curry to S-curry
    ; apply to S-apply
    -- OCP-0003: fold/unfold removed in favor of structured recursion
    ; arr to S-arr
    )

-- Re-export desugar transformation
open import Once.Surface.Desugar public
  using (desugar)

-- Re-export optimizer (includes categorical laws + fusion rules)
open import Once.Optimize public
  using (optimize; optimize-once; optimize-n)

-- Re-export escape analysis (stack allocation optimization)
open import Once.Escape public
  using (escape; escape-once; escape-n)

-- Re-export Arith types and IR (OCP-0001: Orthogonal Arithmetic Compiler)
open import Once.Arith.Type public
open import Once.Arith.IR public
  hiding (_⊕_)  -- Avoid clash with Once.Type._⊕_ (Functor sum)

-- Re-export Parser (for module loading)
open import Once.Parser public
open import Once.Parser.Module public
open FunInfo
open PolyFunInfo

-- Type checking / elaboration
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndSelf; ctxWithImportsAndSelfAndPolys; PolyCtx; emptyPolyCtx; checkElab)
open import Once.TypeCheck.Elaborate as TE using (CheckElabResult)

-- Surface → IR elaboration
open import Once.Surface.Elaborate using (elaborate)

------------------------------------------------------------------------
-- Main function validation
------------------------------------------------------------------------

-- | Validate that main has type Eff Unit Unit (i.e. `IO Unit`).
--
-- The entry point is an effectful action that returns no meaningful
-- value; exit codes come from explicit `exit@<alias>` calls in the
-- body, not from `main`'s return. Admitting `Eff Unit A` for arbitrary
-- A would silently discard any non-Unit return and invites confusion
-- between "exit code" and "value to compose with".
validateMain : Type → String ⊎ ⊤
validateMain (Eff Unit Unit) = inj₂ tt
validateMain ty = inj₁ ("main must have type IO Unit (= Eff Unit Unit), but got: " ++ showType ty)

------------------------------------------------------------------------
-- Function compilation: RawExpr → IR
------------------------------------------------------------------------

-- | Type context for inter-function calls
-- Maps function names to their types (used as imports for type checking)
FunCtx : Set
FunCtx = List (String × Type)

-- | Empty function context
emptyFunCtx : FunCtx
emptyFunCtx = []

-- | Extend context with a new function
extendFunCtx : FunCtx → String → Type → FunCtx
extendFunCtx ctx name ty = (name , ty) ∷ ctx

-- | Compile a function body to IR with context of previous functions
-- Pipeline: typecheck → elaborate → (optionally) optimize
-- Returns IR or error message
compileFunBody : Bool → FunCtx → PolyCtx → (name : String) (ty : Type) → RawExpr → String ⊎ IR Unit ty
compileFunBody doOpt ctx polys name ty expr with checkElab (ctxWithImportsAndSelfAndPolys ctx polys name ty) expr ty
... | TE.failure err = inj₁ ("Type error in " ++ name ++ ": " ++ TE.renderError err)
... | TE.success _ surfaceExpr _ _ =
  let ir = elaborate surfaceExpr
  in inj₂ (if doOpt then optimize ir else ir)

-- | Compile a function with main validation
-- For main: validates type is Eff Unit A before compiling
-- For other functions: compiles directly
compileFun : Bool → FunCtx → PolyCtx → (name : String) (ty : Type) → RawExpr → String ⊎ IR Unit ty
compileFun doOpt ctx polys name ty expr with name == "main"
... | true with validateMain ty
...   | inj₁ err = inj₁ err
...   | inj₂ _   = compileFunBody doOpt ctx polys name ty expr
compileFun doOpt ctx polys name ty expr | false = compileFunBody doOpt ctx polys name ty expr

------------------------------------------------------------------------
-- Module compilation: source → List (name, IR)
------------------------------------------------------------------------

-- | Result of compiling a module
-- Contains function name, type, and compiled IR
record CompiledFun : Set where
  constructor mkCompiledFun
  field
    cfName : String
    cfType : Type
    cfIR   : IR Unit cfType

open CompiledFun

-- | Build context from list of FunInfo (for previously processed functions)
buildFunCtx : List FunInfo → FunCtx
buildFunCtx [] = emptyFunCtx
buildFunCtx (fi ∷ rest) = extendFunCtx (buildFunCtx rest) (funName fi) (funType fi)

-- | Build a `PolyCtx` from the list of `PolyFunInfo`s extracted
-- from a module. Plan 0.6.2.
buildPolyCtx : List PolyFunInfo → PolyCtx
buildPolyCtx [] = emptyPolyCtx
buildPolyCtx (pfi ∷ rest) =
  (pfunName pfi , pfunType pfi , pfunBody pfi) ∷ buildPolyCtx rest

-- | Compile all functions from parsed module, accumulating context
-- Each function is compiled with access to all previously defined
-- functions (ground, via FunCtx) and all polymorphic user defs
-- (via PolyCtx, plan 0.6.2).
compileAllFuns : Bool → List FunInfo → PolyCtx → String ⊎ List CompiledFun
compileAllFuns doOpt funs polys = go funs emptyFunCtx
  where
    go : List FunInfo → FunCtx → String ⊎ List CompiledFun
    go [] _ = inj₂ []
    go (fi ∷ rest) ctx with compileFun doOpt ctx polys (funName fi) (funType fi) (funBody fi)
    ... | inj₁ err = inj₁ err
    ... | inj₂ ir with go rest (extendFunCtx ctx (funName fi) (funType fi))
    ...   | inj₁ err = inj₁ err
    ...   | inj₂ compiled = inj₂ (mkCompiledFun (funName fi) (funType fi) ir ∷ compiled)

-- | Inline fuel budget: bound on the recursion depth of the
-- `inlineReferences` walk. User-polymorphic bodies are typically a
-- handful of NT combinators deep (e.g. `pair snd fst`), so 1024 is
-- far beyond any plausible usage. Kept conservatively large for
-- future deeper libraries; the cost is at most O(fuel) per call site.
inlineFuel : ℕ
inlineFuel = 1024

-- | Compile source text to list of compiled functions
-- Returns: Left error | Right list of (name, type, IR)
--
-- Plan 0.6 Phase C.1: ground function bodies are pre-inlined with
-- both ground and polymorphic user-defined sources. Polymorphic names
-- at call sites expand to their NT-combinator body before typechecking,
-- at which point the existing bidirectional machinery specializes each
-- constituent builtin against the call-site expected type.
compileModule : Bool → String → String ⊎ List CompiledFun
compileModule doOpt source with parse source
... | nothing = inj₁ "Parse error: failed to parse module"
... | just mod =
      let aliases = extractAliases mod
      in case extractFunctions aliases mod of λ where
           (inj₁ err)             → inj₁ err
           (inj₂ (funs , polys))  →
             compileAllFuns doOpt funs (buildPolyCtx polys)

-- | Parse source text to a Module AST. Haskell uses this to read
-- both the user's file and each transitive import before calling
-- `resolveImports` with the populated ModuleMap.
--
-- Strict: returns `inj₁ err` if any tokens are left unconsumed after
-- the parsed decls, or if the module failed to parse at all. This
-- surfaces silent-drop failures (dotted primitive names, TVar-in-
-- type-position, etc.) as real errors at the Haskell boundary
-- instead of zero-decl "Parse OK" that cost a session's worth of
-- debugging earlier. Plan 0.6 Phase A.
parseSourceToModule : String → String ⊎ Module
parseSourceToModule = parseStrict

-- | Compile a pre-parsed, pre-resolved Module. Same as `compileModule`
-- but starting from an AST rather than source text. Used by the
-- import-aware pipeline: Haskell parses each file separately, calls
-- `resolveImports` to flatten imports into owner-tagged primitives,
-- then hands the flat Module to this entry point.
compileResolvedModule : Bool → Module → String ⊎ List CompiledFun
compileResolvedModule doOpt mod =
  let aliases = extractAliases mod
  in case extractFunctions aliases mod of λ where
       (inj₁ err)             → inj₁ err
       (inj₂ (funs , polys))  →
         compileAllFuns doOpt funs (buildPolyCtx polys)

------------------------------------------------------------------------
-- Pipeline composition (SurfaceIR → IR)
------------------------------------------------------------------------

-- | IR pipeline: desugar → optimize → escape
--
-- Transforms SurfaceIR to optimized Core IR.
-- Pipeline stages:
--   1. desugar  - Convert SurfaceIR to Core IR (let-binding elimination)
--   2. optimize - Apply categorical laws + fusion (beta/eta, fold/unfold, map fusion)
--   3. escape   - Rewrite Heap → Stack where allocations don't escape
--
pipeline : ∀ {A B} → SurfaceIR A B → IR A B
pipeline ir = escape (optimize (desugar ir))

-- | Pipeline without escape analysis (for comparison/debugging)
pipeline-no-escape : ∀ {A B} → SurfaceIR A B → IR A B
pipeline-no-escape ir = optimize (desugar ir)

-- | Pipeline without optimization (for debugging)
pipeline-no-opt : ∀ {A B} → SurfaceIR A B → IR A B
pipeline-no-opt = desugar

------------------------------------------------------------------------
-- Target selection and compilation
------------------------------------------------------------------------

open import Once.Target as T using (Target)
open T.Target

-- Import all targets (qualified to avoid name clashes)
import Once.Target.X86-64 as X86-64-Target

-- | Supported architectures
data Arch : Set where
  x86-64 : Arch

-- | Get target implementation for an architecture
archTarget : Arch → Target
archTarget x86-64 = X86-64-Target.x86-64

-- | Compile a single function's IR to assembly using a target
compileFunWithTarget : Target → CompiledFun → String
compileFunWithTarget target cf =
  functionPrologue target (cfName cf) ++
  irToAsm target (cfIR cf) ++
  functionEpilogue target

-- | Compile all functions to assembly using a target
compileAllWithTarget : Target → List CompiledFun → String
compileAllWithTarget target = foldr (λ cf acc → compileFunWithTarget target cf ++ acc) ""

------------------------------------------------------------------------
-- Unified compilation entry point
------------------------------------------------------------------------

-- | Compilation stage
data Stage : Set where
  Parse : Stage   -- Just parse, return function signatures
  Check : Stage   -- Parse + typecheck, no codegen
  Build : Stage   -- Full pipeline including codegen

-- | Compilation result (varies by stage)
data CompileResult : Set where
  Parsed  : List FunInfo → List PolyFunInfo → CompileResult  -- Parse succeeded (ground + poly)
  Checked : List CompiledFun → CompileResult                 -- Typecheck succeeded
  Built   : String → CompileResult                           -- Codegen succeeded (assembly)
  Error   : String → CompileResult                           -- Any stage failed

-- | Show a FunInfo as "name : type"
showFunInfo : FunInfo → String
showFunInfo fi = funName fi ++ " : " ++ showType (funType fi)

-- | Show a PolyFunInfo as "name : polytype"
showPolyFunInfo : PolyFunInfo → String
showPolyFunInfo pfi = pfunName pfi ++ " : " ++ showPolyType (pfunType pfi)

-- | Show all function signatures
showFunInfos : List FunInfo → String
showFunInfos [] = ""
showFunInfos (fi ∷ []) = showFunInfo fi
showFunInfos (fi ∷ rest) = showFunInfo fi ++ "\n" ++ showFunInfos rest

showPolyFunInfos : List PolyFunInfo → String
showPolyFunInfos [] = ""
showPolyFunInfos (pfi ∷ []) = showPolyFunInfo pfi
showPolyFunInfos (pfi ∷ rest) = showPolyFunInfo pfi ++ "\n" ++ showPolyFunInfos rest

-- | Unified compile function - single entry point for all stages
-- stage: how far to compile (ParseOnly, CheckOnly, FullBuild)
-- doOpt: whether to run optimizer (only relevant for CheckOnly/FullBuild)
-- arch: target architecture (only relevant for FullBuild)
-- source: source code text
compile : Stage → Bool → Arch → String → CompileResult
compile stage doOpt arch source with parseStrict source
... | inj₁ err = Error err
... | inj₂ mod =
  let aliases = extractAliases mod
  in case extractFunctions aliases mod of λ where
       (inj₁ err)             → Error err
       (inj₂ (funs , polys))  →
         let pctx = buildPolyCtx polys
         in case stage of λ where
           Parse → Parsed funs polys
           Check → case compileAllFuns doOpt funs pctx of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) → Checked compiled
           Build → case compileAllFuns doOpt funs pctx of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) →
               let target = archTarget arch
               in Built (asmHeader target ++ compileAllWithTarget target compiled)

-- | Same as `compile` but starting from a pre-resolved `Module`.
-- Haskell uses this after driving transitive-import I/O and calling
-- `resolveImports` to flatten `DImport` decls into owner-tagged
-- `DPrimitive` decls. Skips the `parse source` step of `compile`.
compileFromModule : Stage → Bool → Arch → Module → CompileResult
compileFromModule stage doOpt arch mod =
  let aliases = extractAliases mod
  in case extractFunctions aliases mod of λ where
       (inj₁ err)             → Error err
       (inj₂ (funs , polys))  →
         let pctx = buildPolyCtx polys
         in case stage of λ where
           Parse → Parsed funs polys
           Check → case compileAllFuns doOpt funs pctx of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) → Checked compiled
           Build → case compileAllFuns doOpt funs pctx of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) →
               let target = archTarget arch
               in Built (asmHeader target ++ compileAllWithTarget target compiled)