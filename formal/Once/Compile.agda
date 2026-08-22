-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.List using (List; []; _∷_; foldr; foldl)
import Data.List as DL
open import Data.Nat using (ℕ; _⊔_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.String using (String; _++_; _==_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)

-- Re-export types
open import Once.Type public

-- Re-export Core IR
open import Once.IR public
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Target.Symbol using (once-symbol-path)

-- Re-export Surface IR
open import Once.Surface.IR public
  using (SurfaceIR; Let; SigOp)
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
  using (desugar; desugar-default)

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

-- Plan 0.20 Phase G: import the IR rewrite pass that lifts maximal
-- arith subtrees to opaque `arith.block.<digest>` SigOps. Codegen
-- emits `call once_arith.block.<digest>` for those, and the
-- accumulated `ArithBlock`s are passed to the target's
-- `emitArithBlocks` after the main program text.
open import Once.Arith.Machine.IR using (ArithBlock)
open import Once.Arith.Machine.Rewrite using (rewrite-ir)

-- D100: the emitted LOCAL labels (`moduleLabels`, below) — the `.L…` sibling of
-- `moduleSyms`. `labels-def` reads them off the abstract trace; the trace walk
-- itself is telescoped per definition (`IRT.ir-to-trace-from o l ir`).
open import Once.CCC.Label using (Label)
open import Once.CCC.Codegen.EmittedWF using (labels-def)
import Once.CCC.Codegen.IRToTrace as IRT

-- Re-export Parser (for module loading)
open import Once.Parser public
open import Once.Parser.Module public
open FunInfo
open PolyFunInfo

-- Type checking / elaboration
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate using (ctxWithImportsAndSelf; ctxWithImportsAndSelfAndPolys; PolyCtx; emptyPolyCtx; checkElab)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Elaborate as TE using (CheckElabResult)
import Once.Surface.Syntax as Srf
open import Relation.Binary.PropositionalEquality using (subst; cong)
-- D007 inference: the self-less context for inferring a sig-less def's type.
open import Once.TypeCheck.Classify using (ctxWithImportsAndPolys; SigEffectCtx; emptySigEffects; lookupSigEffect; NamedCtx)
-- D072: the untrusted principal-type oracle (validated by checkElab).
import Once.TypeCheck.Principal as Principal
open import Once.SigEffect using (SigEffect)

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
validateMain (Unit ⇒[ mk-kind Many eff ] Unit) = inj₂ tt
validateMain ty = inj₁ ("main must have type IO Unit (= Eff Unit Unit), but got: " ++ showType ty)

-- | Plan 0.2.4.5 D1: target-independent entry-point IR construction.
-- main : IR Unit (Eff Unit Unit) produces a closure value. To run it,
-- we need to apply that closure to (). Express this in CCC IR:
--
--   wrapMainAsEntry main = apply ∘ ⟨ main , terminal ⟩ : IR Unit Unit
--
-- This shifts the responsibility for the closure-call ABI from a
-- hand-written `_start` template (which previously drifted out of sync
-- with the verified apply-setup-trace) onto the verified `apply` IR
-- itself. `_start` then only needs to do kernel-runtime setup
-- (heap-pool init, stack reservation) and call the wrapped entry.
wrapMainAsEntry : IR ⌊ Unit ⌋ ⌊ Unit ⇒[ mk-kind Many eff ] Unit ⌋ → IR ⌊ Unit ⌋ ⌊ Unit ⌋
-- Plan 0.53: the entry/call apply-pairs must be `Heap`, not `Stack`.
-- These wrappers can produce ESCAPING closures (a curried direct-call
-- function `g 4` returns a closure capturing `4`); with a `Stack` pair the
-- capture would point into a transient stack cell that is reused after the
-- frame is popped (the x86-32 `arith-lambda-2` dangling read — x86-64/riscv64
-- only survived it by luck). AllocMode is semantically transparent, so this
-- does not affect the evaluation proof; it only moves the allocation to the
-- heap, where an escaping closure's environment must live. We are heap-only.
wrapMainAsEntry mainIR = apply ∘ ⟨ mainIR , terminal ⟩ Heap

-- | Apply the entry wrap conditionally for the function named "main".
-- Returns the (possibly-rewritten) type and IR. Non-main functions and
-- main with a non-validated type pass through unchanged.
maybeWrapMain : (name : String) (ty : Type) → IR ⌊ Unit ⌋ ⌊ ty ⌋
              → ∃[ ty' ] IR ⌊ Unit ⌋ ⌊ ty' ⌋
maybeWrapMain "main" (Unit ⇒[ mk-kind Many eff ] Unit) ir = Unit , wrapMainAsEntry ir
maybeWrapMain _ ty ir = ty , ir

-- | Plan 0.50 Stage 2 (D064): emit a top-level definition as a DIRECT-CALL
-- MORPHISM. References now elaborate to `lift-morphism (SigOp once_f)` and
-- compile to a direct `call once_f` (`compile-sigOp`), so `once_f` must be the
-- arrow `f : A → B` (`once_f(a) : B`), NOT a closure-returner `once_f() : Bᴬ`.
-- An arrow function's `cfIR : IR Unit (A ⇒ B)` (the curried closure) is
-- uncurried to `apply ∘ ⟨ cfIR ∘ terminal , id ⟩ : IR A B` — the verified
-- `apply` consumes the closure with the incoming argument `id`, mirroring
-- `wrapMainAsEntry`. `main` is already `cfType ≡ Unit` (entry-wrapped by
-- `maybeWrapMain`), so it is non-arrow and passes through untouched.
directCallIR : (ty : Type) → IR ⌊ Unit ⌋ ⌊ ty ⌋ → ∃[ D ] ∃[ C ] IR ⌊ D ⌋ ⌊ C ⌋
-- Plan 0.53: `Heap`, not `Stack` — see wrapMainAsEntry. A curried direct-call
-- function's first application returns a closure that captures the first arg
-- and escapes, so its apply-pair must be heap-allocated.
directCallIR (A ⇒[ k ] B) ir = A , B , apply ∘ ⟨ ir ∘ terminal , id ⟩ Heap
directCallIR ty           ir = Unit , ty , ir

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
-- Pipeline: typecheck (Phase 1) → resolve polys (Phase 2) → elaborate → (optionally) optimize
-- Phase 1 emits `poly x T` placeholders at user-polymorphic references;
-- Phase 2's `resolveExpr` tree-walk substitutes them with the specialized
-- body elaborations before the surface-to-IR pass.
-- Returns IR or error message
-- Plan 0.14 follow-up: take the default AllocMode from the caller
-- (threaded from CLI --alloc).
-- `compileFunBody-aux` takes the elaboration RESULT explicitly (instead of a
-- `with` on `checkElab`), so proofs can case on a bound variable and the
-- original `compileFunBody` is `aux ∘ checkElab` by `refl` (Plan 0.48: needed
-- to prove `doOpt`-independence of success without the `with`-bite). Generic
-- over the elaboration context `Δ` so the dependent index need not be spelled.
compileFunBody-aux : ∀ {n} {Δ : Srf.Ctx n}
  → AllocMode → Bool → FunCtx → PolyCtx → (name : String) (ty : Type)
  → Srf.⟦ Δ ⟧ᶜ ≡ Unit
  → CheckElabResult Δ ty → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFunBody-aux m doOpt ctx polys name ty δ-unit (TE.failure err) =
  inj₁ ("Type error in " ++ name ++ ": " ++ TE.renderError err)
compileFunBody-aux m doOpt ctx polys name ty δ-unit (TE.success _ surfaceExpr _ _) =
  -- Plan 0.19: pass the user-fn list (= `ctx + self`) twice: once as
  -- `imps` (preserves the resolver's existing typecheck-context use for
  -- poly bodies) and once as `userFns` (drives sigOp→closure rewrite
  -- for user-defined top-level fn references). External syscalls are
  -- handled via the qualified-name path and never reach this resolver.
  let userList = (name , ty) ∷ ctx
      resolved = resolveExpr polys userList userList 0 surfaceExpr
      ir = elaborate m resolved
  in inj₂ (subst (λ X → IR X ⌊ ty ⌋) (cong ⌊_⌋ δ-unit) (if doOpt then optimize ir else ir))

compileFunBody : AllocMode → Bool → FunCtx → PolyCtx → SigEffectCtx → (name : String) (ty : Type) → RawExpr → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFunBody m doOpt ctx polys sigEffs name ty expr =
  compileFunBody-aux m doOpt ctx polys name ty refl
    (checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs name ty) expr ty)

-- | Compile a function with main validation
-- For main: validates type is Eff Unit A before compiling
-- For other functions: compiles directly
--
-- Explicit-argument aux form (Plan 0.48): `compileFun-aux` dispatches on the
-- `name == "main"` Bool, `compileFun-main-aux` on the `validateMain` result —
-- both `doOpt`-free guards, so success rides on `compileFunBody` alone.
compileFun-main-aux : AllocMode → Bool → FunCtx → PolyCtx → SigEffectCtx → (name : String) (ty : Type) → RawExpr → String ⊎ ⊤ → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFun-main-aux m doOpt ctx polys sigEffs name ty expr (inj₁ err) = inj₁ err
compileFun-main-aux m doOpt ctx polys sigEffs name ty expr (inj₂ _)   = compileFunBody m doOpt ctx polys sigEffs name ty expr

compileFun-aux : AllocMode → Bool → FunCtx → PolyCtx → SigEffectCtx → (name : String) (ty : Type) → RawExpr → Bool → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFun-aux m doOpt ctx polys sigEffs name ty expr true  = compileFun-main-aux m doOpt ctx polys sigEffs name ty expr (validateMain ty)
compileFun-aux m doOpt ctx polys sigEffs name ty expr false = compileFunBody m doOpt ctx polys sigEffs name ty expr

compileFun : AllocMode → Bool → FunCtx → PolyCtx → SigEffectCtx → (name : String) (ty : Type) → RawExpr → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFun m doOpt ctx polys sigEffs name ty expr = compileFun-aux m doOpt ctx polys sigEffs name ty expr (name == "main")

------------------------------------------------------------------------
-- Module compilation: source → List (name, IR)
------------------------------------------------------------------------

-- | Result of compiling a module
-- Contains function name, type, and compiled IR
record CompiledFun : Set where
  constructor mkCompiledFun
  field
    cfName : CanonicalName
    cfType : Type
    cfIR   : IR ⌊ Unit ⌋ ⌊ cfType ⌋
    -- | Plan 0.11: `true` for primitives (signatures whose
    -- implementation is provided externally via
    -- `Strata/Interpretations/<…>.<arch>` files). Their function
    -- body is NOT emitted at codegen time.
    cfIsPrimitive : Bool

open CompiledFun

-- | Build context from list of FunInfo (for previously processed functions)
buildFunCtx : List FunInfo → FunCtx
buildFunCtx [] = emptyFunCtx
buildFunCtx (fi ∷ rest) with funType fi
... | just ty = extendFunCtx (buildFunCtx rest) (funName fi) ty
... | nothing = buildFunCtx rest

-- | Build a `PolyCtx` from the list of `PolyFunInfo`s extracted
-- from a module. Plan 0.6.2.
buildPolyCtx : List PolyFunInfo → PolyCtx
buildPolyCtx [] = emptyPolyCtx
buildPolyCtx (pfi ∷ rest) =
  (pfunName pfi , pfunType pfi , pfunBody pfi) ∷ buildPolyCtx rest

-- | D007 type inference: a definition without an explicit signature has its
-- type fully determined by the composition of its body (no specialization,
-- no ambiguity — D007). Inferred in a SELF-LESS context (Once has no
-- recursion). `inferElab`'s `success` carries the inferred type `A`.
-- | D072: validate an untrusted oracle answer with the verified
-- `checkElab` before adopting it (check-after-infer is the trust
-- boundary — a wrong oracle answer is a rejected program, never an
-- unsound one). Top-level aux (not a `with`) so proofs can match the
-- `Maybe Type` scrutinee directly.
inferType-validate : NamedCtx → RawExpr → String → Maybe Type → String ⊎ Type
inferType-validate nctx body err nothing = inj₁ err
inferType-validate nctx body err (just T) with checkElab nctx body T
... | TE.success _ _ _ _ = inj₂ T
... | TE.failure _       = inj₁ err

inferType : FunCtx → PolyCtx → RawExpr → String ⊎ Type
inferType ctx polys body with TE.inferElab (ctxWithImportsAndPolys ctx polys) body
... | TE.success A _ _ _ _ = inj₂ A
-- D072: bidirectional synthesis failed — ask the principal-type oracle
-- (ground answers only here; schema answers route via the telescope, M3).
... | TE.failure err       =
      inferType-validate (ctxWithImportsAndPolys ctx polys) body
        ("Cannot infer type: " ++ TE.renderError err)
        (Principal.principalGround (ctxWithImportsAndPolys ctx polys) body)

-- | The explicit signature if given, otherwise the inferred type (D007).
resolveFunType : FunCtx → PolyCtx → Maybe Type → RawExpr → String ⊎ Type
resolveFunType ctx polys (just ty) body = inj₂ ty
resolveFunType ctx polys nothing   body = inferType ctx polys body

-- | Compile all functions from parsed module, accumulating context
-- Each function is compiled with access to all previously defined
-- functions (ground, via FunCtx) and all polymorphic user defs
-- (via PolyCtx, plan 0.6.2).
-- `go` lifted to TOP LEVEL (was a `where`-local of `compileAllFuns`) so the
-- verified frontend can induct on it (a compiled `main` traces back to its
-- `FunInfo`). The `ctx` accumulator is now
-- an explicit parameter; `compileAllFuns` seeds it with `emptyFunCtx`.
-- Explicit-argument aux form (Plan 0.48): the three nested scrutinees
-- (`resolveFunType` → `compileFun` → the recursion) each become an aux that
-- matches a bound `⊎` variable, so proofs can case without the `with`-bite.
-- `caf-go-cf-aux` calls `compileAllFuns-go` (mutual); the self-recursion is on
-- the structurally-smaller `rest`.
caf-go-wrap : (fi : FunInfo) (ty : Type) → IR ⌊ Unit ⌋ ⌊ ty ⌋ → String ⊎ List CompiledFun → String ⊎ List CompiledFun
caf-go-cf-aux : AllocMode → Bool → PolyCtx → SigEffectCtx → (fi : FunInfo) → List FunInfo → FunCtx → (ty : Type) → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋ → String ⊎ List CompiledFun
caf-go-rf-aux : AllocMode → Bool → PolyCtx → SigEffectCtx → (fi : FunInfo) → List FunInfo → FunCtx → String ⊎ Type → String ⊎ List CompiledFun
compileAllFuns-go : AllocMode → Bool → PolyCtx → SigEffectCtx → List FunInfo → FunCtx → String ⊎ List CompiledFun

caf-go-wrap fi ty ir (inj₁ err)       = inj₁ err
caf-go-wrap fi ty ir (inj₂ compiled)  =
  -- Plan 0.2.4.5 D1: for main, wrap as `apply ∘ ⟨ main , terminal ⟩`
  -- so codegen produces a Unit→Unit entry point that does the
  -- closure invocation via the verified apply IR. _start no longer
  -- needs hand-written closure-call ABI (which drifted at Stage C).
  let wrapped = maybeWrapMain (funName fi) ty ir
      ty'     = proj₁ wrapped
      ir'     = proj₂ wrapped
  in inj₂ (mkCompiledFun (bare (funName fi)) ty' ir' (funIsPrimitive fi) ∷ compiled)

caf-go-cf-aux m doOpt polys sigEffs fi rest ctx ty (inj₁ err) = inj₁ err
caf-go-cf-aux m doOpt polys sigEffs fi rest ctx ty (inj₂ ir) =
  caf-go-wrap fi ty ir (compileAllFuns-go m doOpt polys sigEffs rest (extendFunCtx ctx (funName fi) ty))

caf-go-rf-aux m doOpt polys sigEffs fi rest ctx (inj₁ err) = inj₁ err
caf-go-rf-aux m doOpt polys sigEffs fi rest ctx (inj₂ ty) =
  caf-go-cf-aux m doOpt polys sigEffs fi rest ctx ty (compileFun m doOpt ctx polys sigEffs (funName fi) ty (funBody fi))

compileAllFuns-go m doOpt polys sigEffs [] _ = inj₂ []
-- D007: resolve the function's type FIRST (explicit sig, or inferred from
-- the body), then compile / extend the context / wrap-main with it.
compileAllFuns-go m doOpt polys sigEffs (fi ∷ rest) ctx =
  caf-go-rf-aux m doOpt polys sigEffs fi rest ctx (resolveFunType ctx polys (funType fi) (funBody fi))

compileAllFuns : AllocMode → Bool → List FunInfo → PolyCtx → SigEffectCtx → String ⊎ List CompiledFun
compileAllFuns m doOpt funs polys sigEffs = compileAllFuns-go m doOpt polys sigEffs funs emptyFunCtx

-- | Collect the declared `! <shape>` effect map from a module's
-- declarations (Plan 0.38 M0.2). Keyed by the SAME qualified name as
-- `extractFunctions`' `FunInfo`s / the elaborator's import lookups
-- (`owner.name`, or bare `name` when unowned). Signatures with no
-- annotation contribute nothing. This is the ONLY channel by which the
-- compiler learns an external arrow's effect.
collectSigEffects : List Decl → SigEffectCtx
collectSigEffects [] = []
collectSigEffects (DSignature name (just owner) _ (just se) ∷ rest) =
  (owner ++ "." ++ name , se) ∷ collectSigEffects rest
collectSigEffects (DSignature name nothing _ (just se) ∷ rest) =
  (name , se) ∷ collectSigEffects rest
collectSigEffects (_ ∷ rest) = collectSigEffects rest

-- | Compile source text to list of compiled functions
-- Returns: Left error | Right list of (name, type, IR)
--
-- Plan 0.6 Phase C.1: ground function bodies are pre-inlined with
-- both ground and polymorphic user-defined sources. Polymorphic names
-- at call sites expand to their NT-combinator body before typechecking,
-- at which point the existing bidirectional machinery specializes each
-- constituent builtin against the call-site expected type.
compileModule : AllocMode → Bool → String → String ⊎ List CompiledFun
compileModule m doOpt source with parse source
... | nothing = inj₁ "Parse error: failed to parse module"
... | just mod =
      let aliases = extractAliases mod
      in case extractFunctions aliases mod of λ where
           (inj₁ err)             → inj₁ err
           (inj₂ (funs , polys))  →
             compileAllFuns m doOpt funs (buildPolyCtx polys) (collectSigEffects (Module.decls mod))

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
-- Explicit-argument aux form (Plan 0.48): dispatch on the `extractFunctions`
-- result so the proof relating this to `compileFromModule` (which shares the
-- same call) can match a bound `⊎` variable.
compileResolvedModule-aux : AllocMode → Bool → Module → String ⊎ (List FunInfo × List PolyFunInfo) → String ⊎ List CompiledFun
compileResolvedModule-aux m doOpt mod (inj₁ err)            = inj₁ err
compileResolvedModule-aux m doOpt mod (inj₂ (funs , polys)) =
  compileAllFuns m doOpt funs (buildPolyCtx polys) (collectSigEffects (Module.decls mod))

compileResolvedModule : AllocMode → Bool → Module → String ⊎ List CompiledFun
compileResolvedModule m doOpt mod =
  compileResolvedModule-aux m doOpt mod (extractFunctions (extractAliases mod) mod)

-- Plan 0.50 — the symbols THIS codegen actually emits as `.globl` labels, defined
-- on the SAME `CompiledFun` list `compileFromModule` renders (`compileResolvedModule`).
-- `compileFunWithTarget` skips primitives and emits `functionPrologue (cfName cf)` =
-- `once-symbol-path (cfName cf)` for the rest, so `emittedSyms` mirrors that exactly.
-- Clash-freedom (`program-no-clash`) is proven over THIS list, so it cannot drift
-- from what the backend emits (the earlier `extractFunctions`-re-derivation could).
emittedSyms-cons : Bool → CompiledFun → List String → List String
emittedSyms-cons true  cf rest = rest                                   -- primitive: no label
emittedSyms-cons false cf rest = once-symbol-path (cfName cf) ∷ rest

emittedSyms : List CompiledFun → List String
emittedSyms []         = []
emittedSyms (cf ∷ cfs) = emittedSyms-cons (cfIsPrimitive cf) cf (emittedSyms cfs)

moduleSyms-aux : String ⊎ List CompiledFun → List String
moduleSyms-aux (inj₁ _)   = []
moduleSyms-aux (inj₂ cfs) = emittedSyms cfs

moduleSyms : AllocMode → Bool → Module → List String
moduleSyms m doOpt mod = moduleSyms-aux (compileResolvedModule m doOpt mod)

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
-- Plan 0.14 follow-up (2026-05-18): desugar is now parameterized on
-- the default AllocMode. Callers thread the user's --alloc choice from
-- the CLI; backwards-compatible aliases (-default suffix) preserve Heap
-- as the previous hardcoded behavior.
pipeline : ∀ {A B} → AllocMode → SurfaceIR A B → IR ⌊ A ⌋ ⌊ B ⌋
pipeline m ir = escape (optimize (desugar m ir))

pipeline-default : ∀ {A B} → SurfaceIR A B → IR ⌊ A ⌋ ⌊ B ⌋
pipeline-default = pipeline Heap

-- | Pipeline without escape analysis (for comparison/debugging)
pipeline-no-escape : ∀ {A B} → AllocMode → SurfaceIR A B → IR ⌊ A ⌋ ⌊ B ⌋
pipeline-no-escape m ir = optimize (desugar m ir)

-- | Pipeline without optimization (for debugging)
pipeline-no-opt : ∀ {A B} → AllocMode → SurfaceIR A B → IR ⌊ A ⌋ ⌊ B ⌋
pipeline-no-opt = desugar

------------------------------------------------------------------------
-- Target selection and compilation
------------------------------------------------------------------------

open import Once.Target as T using (Target)
open T.Target

-- Import all targets (qualified to avoid name clashes)
import Once.Target.X86-64 as X86-64-Target
import Once.Target.X86-32 as X86-32-Target
import Once.Target.RiscV64 as RiscV64-Target

-- | Supported architectures — the single shared enum (re-exported so
-- existing `C.Arch` references downstream are unchanged).
open import Once.Target.Arch public
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?; firstBadLit)
open import Data.Nat.Show renaming (show to showNat)
open import Data.Integer using (ℤ)
open import Data.Nat using (_∸_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Integer.Show renaming (show to showℤ)

-- | Get target implementation for an architecture
archTarget : Arch → Target
archTarget x86-64  = X86-64-Target.x86-64
archTarget x86-32  = X86-32-Target.x86-32
archTarget riscv64 = RiscV64-Target.riscv64

-- | Compile a single function's IR to assembly using a target.
-- Plan 0.11: primitives (signatures) emit nothing — their bodies
-- live in `Strata/Interpretations/<…>.<arch>` files and are
-- statically linked at build time by the driver. Emitting a body
-- here would produce a recursive `once_<name>: ...; call once_<name>;
-- ret` stub.
--
-- Plan 0.2.4.2 Phase B: closure-body labels (`.L_thunk_<n>:`) are
-- emitted via `irToBodies` AFTER the parent's `ret` (epilogue). The
-- parent's fall-through stops at `ret`; bodies are reachable only
-- via `lea label(%rip)` from the parent's curry trace.
--
-- Plan 0.12 Layer 1: takes a starting thunk-label counter `l` and
-- returns the next-available counter alongside the assembly text,
-- so that thunks emitted by separate top-level functions don't
-- collide. Both `irToAsm` and `irToBodies` are called with the same
-- `l` and produce the same `l'` — the calls re-traverse the IR but
-- agree on the label counter advancement (`ir-to-trace'` is
-- deterministic in `l`).
compileFunWithTarget : Target → ℕ → CompiledFun → ℕ × String × List ArithBlock
compileFunWithTarget target l cf with cfIsPrimitive cf
... | true  = l , "" , []  -- primitive: external symbol, no body
... | false =
  let -- Plan 0.50 Stage 2: emit the function as a direct-call morphism (D064).
      (_ , _ , dcIR) = directCallIR (cfType cf) (cfIR cf)
      -- Plan 0.20 Phase G: arith-block recognition pass before codegen.
      (ir' , blks)  = rewrite-ir dcIR
      -- Plan 0.63 (D089): the definition's own identity keys its labels.
      (l₁ , asm)    = irToAsm    target (cfName cf) l ir'
      (l₂ , bodies) = irToBodies target (cfName cf) l ir'
  in (l₁ ⊔ l₂) , (functionPrologue target (cfName cf) ++
           asm ++
           functionEpilogue target ++
           bodies) , blks
  where
    -- Plan 0.29: irToAsm and irToBodies share the thunk-label phase
    -- (l→l', deterministic, so thunk labels agree between call sites
    -- and bodies). But the CASE-label phase diverges: irToAsm's l₁
    -- counts case-on-tags in the MAIN trace, while irToBodies' l₂
    -- counts case-on-tags inside the thunk BODIES. A cata's algebra
    -- case-on-tags live in the closure body (l₂ > l₁), so threading
    -- l₁ alone leaks body case labels into the next function. Thread
    -- `l₁ ⊔ l₂` so the next function starts past BOTH ranges.
    -- (Invariant preserved: per function, main cases ⊆ [l', l₁) and
    -- body cases ⊆ [l', l₂); these overlap only if a function has
    -- case-on-tag in both main trace and a body — not produced by any
    -- current IR, since closure-valued IRs put all dispatch in bodies.)

-- | Compile all functions to assembly using a target.
-- Plan 0.12 Layer 1: left-fold threading the thunk-label counter so
-- thunks remain globally unique across the module.
-- Plan 0.20 Phase G: collect ArithBlocks from every function and
-- append `emitArithBlocks` output after the program text, so each
-- `arith.block.<digest>` SigOp call site resolves at link time.
compileAllWithTarget : Target → List CompiledFun → String
compileAllWithTarget target cfs =
  let (_ , asm , blks) = foldl step (0 , "" , []) cfs
  in asm ++ emitArithBlocks target blks
  where
    step : ℕ × String × List ArithBlock → CompiledFun → ℕ × String × List ArithBlock
    step p cf =
      let l       = proj₁ p
          acc     = proj₁ (proj₂ p)
          accBlks = proj₂ (proj₂ p)
          (l' , fn-asm , blks) = compileFunWithTarget target l cf
      in l' , (acc ++ fn-asm) , (accBlks DL.++ blks)

------------------------------------------------------------------------
-- D100 — THE LOCAL LABELS THIS CODEGEN EMITS.
--
-- The exact mirror of `moduleSyms` one level down: that list is the `.globl`
-- function symbols, this one is the `.L…` labels the trace invents. `as`
-- rejects a file that defines either twice, and the 2026-08-06 regression
-- (`symbol .L_thunk_once_4main_10 is already defined`) was a duplicate in THIS
-- list — invisible to every proof, because the only layer that rejects it is
-- the assembler, i.e. the `<arch>-loader-faithful` axiom.
--
-- Defined over the SAME `CompiledFun` list `compileFromModule` renders and
-- threading the SAME counter `compileAllWithTarget`'s fold threads (`l₁ ⊔ l₂`,
-- both targets' walks) — so it cannot drift from what the backend emits. The
-- counter is the one place the arch shows through: `irToAsm` allocates further
-- labels of its own inside `compile-trace-cnt`, and the NEXT function starts
-- past them. The labels themselves are read off the ABSTRACT TRACE
-- (`labels-def`), which is arch-independent, so the invariant is one statement
-- for all three targets.
--
-- SCOPE, honestly: the arch labels `compile-trace-cnt` allocates are inside the
-- range but not in this list. That walk is LINEAR (it never splices a
-- sub-trace twice), so its freshness is a per-arch `LabelRange` one-liner; the
-- non-linear walk (`ir-to-trace'`, whose `Cata` clause splices its algebra
-- twice) is the one this list sees.
------------------------------------------------------------------------

funLabels-cons : Bool → Target → ℕ → CompiledFun → ℕ × List Label
funLabels-cons true  target l cf = l , []              -- primitive: no body, no labels
funLabels-cons false target l cf =
  let (_ , _ , dcIR) = directCallIR (cfType cf) (cfIR cf)
      (ir' , _)      = rewrite-ir dcIR
      (l₁ , _)       = irToAsm    target (cfName cf) l ir'
      (l₂ , _)       = irToBodies target (cfName cf) l ir'
      (_  , at)      = IRT.ir-to-trace-from (cfName cf) l ir'
  in (l₁ ⊔ l₂) , labels-def at

funLabels : Target → ℕ → CompiledFun → ℕ × List Label
funLabels target l cf = funLabels-cons (cfIsPrimitive cf) target l cf

emittedLabels : Target → ℕ → List CompiledFun → List Label
emittedLabels target l []         = []
emittedLabels target l (cf ∷ cfs) =
  proj₂ (funLabels target l cf) DL.++ emittedLabels target (proj₁ (funLabels target l cf)) cfs

moduleLabels-aux : Target → String ⊎ List CompiledFun → List Label
moduleLabels-aux target (inj₁ _)   = []
moduleLabels-aux target (inj₂ cfs) = emittedLabels target 0 cfs

moduleLabels : Arch → AllocMode → Bool → Module → List Label
moduleLabels arch m doOpt mod =
  moduleLabels-aux (archTarget arch) (compileResolvedModule m doOpt mod)

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
showFunInfo fi with funType fi
... | just ty = funName fi ++ " : " ++ showType ty
... | nothing = funName fi ++ " : <inferred>"

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
compile : AllocMode → Stage → Bool → Arch → String → CompileResult
compile m stage doOpt arch source with parseStrict source
... | inj₁ err = Error err
... | inj₂ mod =
  let aliases = extractAliases mod
  in case extractFunctions aliases mod of λ where
       (inj₁ err)             → Error err
       (inj₂ (funs , polys))  →
         let pctx = buildPolyCtx polys
         in case stage of λ where
           Parse → Parsed funs polys
           Check → case compileAllFuns m doOpt funs pctx (collectSigEffects (Module.decls mod)) of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) → Checked compiled
           Build → case compileAllFuns m doOpt funs pctx (collectSigEffects (Module.decls mod)) of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) →
               let target = archTarget arch
               in Built (asmHeader target ++ compileAllWithTarget target compiled)

-- | Same as `compile` but starting from a pre-resolved `Module`.
-- Haskell uses this after driving transitive-import I/O and calling
-- `resolveImports` to flatten `DImport` decls into owner-tagged
-- `DSignature` decls. Skips the `parse source` step of `compile`.
-- Plan 0.14 follow-up: takes AllocMode from CLI --alloc flag.
-- Explicit-argument aux form (Plan 0.48): `cfm-ef-aux` dispatches on
-- `extractFunctions`, `cfm-stage-aux` on the stage, and the Check/Build emit
-- helpers on the `compileAllFuns` result — the SAME `compileAllFuns` call as
-- `compileResolvedModule-aux`, which is what lets `main⇒built` relate them.
cfm-build-emit : Arch → String ⊎ List CompiledFun → CompileResult
cfm-build-emit arch (inj₁ err)       = Error err
cfm-build-emit arch (inj₂ compiled)  =
  let target = archTarget arch in Built (asmHeader target ++ compileAllWithTarget target compiled)

cfm-check-emit : String ⊎ List CompiledFun → CompileResult
cfm-check-emit (inj₁ err)       = Error err
cfm-check-emit (inj₂ compiled)  = Checked compiled

-- | THE LITERAL-RANGE GATE (plan 0.74 J3, D115).
--
-- An `Int` literal that does not fit this target's signed range is a compile
-- error. It is raised HERE, at lowering, and not as a type error: the
-- constraint is target-specific and the type system is target-generic, which
-- is the whole reason the frontend does not know the width.
--
-- It gates BUILD only. `once check` still succeeds — typechecking genuinely
-- did — and `once build --target x86_32` is where a literal too wide for
-- x86-32 is refused. That is the error being target-specific, visible.
--
-- The DECISION is `admissibleM?`, the spec's own — one procedure, two callers.
-- The alternative, a second range test written here, is how `ArithSimX86-32`
-- came to model a 32-bit target at 64 bits with nothing to catch it.
--
-- Arithmetic is NOT gated: it wraps, and D054 says that is defined semantics.
-- Float literals are not gated either: they always lower, rounding when the
-- target cannot hold them exactly (D116).
litRangeError : Arch → Module → String
litRangeError arch mod = badLit (firstBadLit arch mod)
  where
    bits = arch-int-bits arch
    badLit : Maybe ℤ → String
    badLit (just z) =
      "Int literal " ++ showℤ z ++ " does not fit " ++ archName arch
        ++ "'s signed " ++ showNat bits ++ "-bit range (-2^"
        ++ showNat (bits ∸ 1) ++ " .. 2^" ++ showNat (bits ∸ 1) ++ "-1). "
        ++ "Once's Int is the TARGET's word (D054), so this literal is "
        ++ "expressible on a wider target and not on this one. Arithmetic "
        ++ "wraps; a literal does not."
    badLit nothing = "Int literal out of range for " ++ archName arch

-- Explicit-argument aux (no `with`), matching this file's convention, so the
-- decision stays a subterm downstream proofs can rewrite by.
cfm-build-gated : AllocMode → Bool → (arch : Arch) → (mod : Module)
                → List FunInfo → List PolyFunInfo
                → Dec (AdmissibleM arch mod) → CompileResult
cfm-build-gated m doOpt arch mod funs polys (no  _) = Error (litRangeError arch mod)
cfm-build-gated m doOpt arch mod funs polys (yes _) =
  cfm-build-emit arch (compileAllFuns m doOpt funs (buildPolyCtx polys) (collectSigEffects (Module.decls mod)))

cfm-stage-aux : AllocMode → Stage → Bool → Arch → Module → List FunInfo → List PolyFunInfo → CompileResult
cfm-stage-aux m Parse doOpt arch mod funs polys = Parsed funs polys
cfm-stage-aux m Check doOpt arch mod funs polys =
  cfm-check-emit (compileAllFuns m doOpt funs (buildPolyCtx polys) (collectSigEffects (Module.decls mod)))
cfm-stage-aux m Build doOpt arch mod funs polys =
  cfm-build-gated m doOpt arch mod funs polys (admissibleM? arch mod)

cfm-ef-aux : AllocMode → Stage → Bool → Arch → Module → String ⊎ (List FunInfo × List PolyFunInfo) → CompileResult
cfm-ef-aux m stage doOpt arch mod (inj₁ err)            = Error err
cfm-ef-aux m stage doOpt arch mod (inj₂ (funs , polys)) = cfm-stage-aux m stage doOpt arch mod funs polys

compileFromModule : AllocMode → Stage → Bool → Arch → Module → CompileResult
compileFromModule m stage doOpt arch mod =
  cfm-ef-aux m stage doOpt arch mod (extractFunctions (extractAliases mod) mod)