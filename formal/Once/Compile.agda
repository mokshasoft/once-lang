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
open import Data.List using (List; []; _∷_)
import Data.List as DL
import Data.Bool.ListAction as BLA
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.String using (String; _++_; _==_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)

-- Re-export types
open import Once.Type

-- Re-export Core IR
open import Once.IR
open import Once.IRTy using (Unit; ⌊_⌋)
open import Once.CanonicalName using (CanonicalName; bare)
open import Once.Target.Symbol using (once-symbol-path; once-symbol-own)
open import Once.CCC.Codegen.NodesOK using (leaf-syms)
open import Data.List.Membership.DecPropositional Data.String._≟_ using () renaming (_∈?_ to _∈ˢ?_; _∈_ to _∈ˢ_)
open import Relation.Nullary.Decidable.Core using (¬?)
open import Relation.Nullary.Negation.Core using (¬_)

-- Re-export Surface IR

-- Re-export desugar transformation

-- Re-export optimizer (includes categorical laws + fusion rules)
open import Once.Optimize
  using (optimize)

-- Re-export Arith types and IR (OCP-0001: Orthogonal Arithmetic Compiler)

-- Plan 0.20 Phase G: import the IR rewrite pass that lifts maximal
-- arith subtrees to opaque `arith.block.<digest>` SigOps. Codegen
-- emits `call once_arith.block.<digest>` for those, and the
-- accumulated `ArithBlock`s are passed to the target's
-- `emitArithBlocks` after the main program text.
open import Once.Arith.Machine.IR using (ArithBlock)
open Once.Arith.Machine.IR.ArithBlock using (block-body)
open import Once.Arith.SigOp.Block using (block-name)
open import Once.Arith.Machine.Rewrite using (rewrite-ir)

import Once.CCC.Codegen.IRToTrace as IRT
import Once.CCC.Target.X86-64.File as X64F
import Once.CCC.Target.X86-32.File as X32F
import Once.CCC.Target.RiscV64.File as RVF
import Once.CCC.Target.X86-64.Syntax as X64S
import Once.CCC.Target.X86-32.Syntax as X32S
import Once.CCC.Target.RiscV64.Syntax as RVS
import Once.CCC.Target.X86-64.AbstractToX86 as X64L
import Once.CCC.Target.X86-32.AbstractToX86-32 as X32L
import Once.CCC.Target.RiscV64.AbstractToRiscV as RVL
import Once.Arith.Backend.X86-64.Emit as X64A
import Once.Arith.Backend.X86-32.Emit as X32A
import Once.Arith.Backend.RiscV64.Emit as RVA
import Once.CCC.Label as Label
open import Once.CCC.Machine.SMCore using (AbstractTrace)
open import Once.CCC.Codegen.ProgramImage using (program-image; fns-image)
open import Once.Denotation.Program using (IRFun; irFun; IRProgram; irProgram)
open Once.Denotation.Program.IRProgram using (main; table)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Once.CanonicalName using () renaming (_≟ᶜ_ to _≟cn_)

-- Re-export Parser (for module loading)
open import Once.Parser
open import Once.Parser.Module
open import Once.Parser.Module.Core using (Module)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.Type using (Type)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (no; yes)
open FunInfo
open PolyFunInfo

-- Type checking / elaboration
open import Once.TypeCheck.Elaborate using (checkElab)
import Once.TypeCheck.Error as Error
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Elaborate as TE using ()
import Once.Surface.Syntax as Srf
open import Relation.Binary.PropositionalEquality using (subst; cong)
-- D007 inference: the self-less context for inferring a sig-less def's type.
open import Once.TypeCheck.Classify using (NamedCtx; TopCtx; topCtx; emptyTopCtx; PolyCtx; ctxWithImportsAndPolys; emptyPolyCtx)
open import Once.TypeCheck.Error using (renderError)
open import Relation.Nullary using (Dec)
import Data.String.Properties as SProp
open import Once.Type.Rigid using (rigidOf; RigidFree; rigidFree?)
open import Once.Functor.Translate using (IsConcrete)
open import Once.Functor.Decide using (isConcrete?)
open import Once.Type.Honest using (HonestFFI; honest?)
open import Once.Type.DecEq using (_≟T_)
import Data.Nat
-- D072: the untrusted principal-type oracle (validated by checkElab).
import Once.TypeCheck.Principal as Principal

-- Surface → IR elaboration
open import Once.Surface.Elaborate using (elaborateFull)
open import Once.Denotation.Realize using (realize)

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
{-# CATCHALL #-}
validateMain ty = inj₁ ("main must have type IO Unit (= Eff Unit Unit), but got: " ++ showType ty)

-- D253: `main` is an entry like any other. It is not rewritten: its entry
-- form is the direct-call morphism (`directCallIR`), which at `IO Unit` is
-- `apply ∘ ⟨ ir ∘ terminal , id ⟩` — it RUNS the action on the Unit input,
-- and `_start` calls `once_main` like any caller calls an entry.

-- | Plan 0.50 Stage 2 (D064): emit a top-level definition as a DIRECT-CALL
-- MORPHISM. References now elaborate to `lift-morphism (SigOp once_f)` and
-- compile to a direct `call once_f` (`compile-sigOp`), so `once_f` must be the
-- arrow `f : A → B` (`once_f(a) : B`), NOT a closure-returner `once_f() : Bᴬ`.
-- An arrow function's `cfIR : IR Unit (A ⇒ B)` (the curried closure) is
-- uncurried to `apply ∘ ⟨ cfIR ∘ terminal , id ⟩ : IR A B` — the verified
-- `apply` consumes the closure with the incoming argument `id`. `main` is no
-- exception (D253): at `IO Unit = Unit ⇒[eff] Unit` this is its entry.
directCallIR : (ty : Type) → IR ⌊ Unit ⌋ ⌊ ty ⌋ → ∃[ D ] ∃[ C ] IR ⌊ D ⌋ ⌊ C ⌋
-- Plan 0.53: `Heap`, not `Stack`. A curried direct-call
-- function's first application returns a closure that captures the first arg
-- and escapes, so its apply-pair must be heap-allocated.
-- D143: at an ERASED arrow the function takes no argument, so the uncurried
-- form's domain is `Unit`, not `A` — there is nothing for a caller to pass.
directCallIR (A ⇒[ mk-kind Zero π ] B) ir = Unit , B , apply ∘ ⟨ ir ∘ terminal , id ⟩
directCallIR (A ⇒[ mk-kind One  π ] B) ir = A , B , apply ∘ ⟨ ir ∘ terminal , id ⟩
directCallIR (A ⇒[ mk-kind Many π ] B) ir = A , B , apply ∘ ⟨ ir ∘ terminal , id ⟩
{-# CATCHALL #-}
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
-- `compileFunBody-aux` takes the VERIFIED check result explicitly (instead of a
-- `with` on `checkElabV`), so proofs can case on a bound variable and the
-- original `compileFunBody` is `aux ∘ checkElabV` by `refl` (Plan 0.48: needed
-- to prove `doOpt`-independence of success without the `with`-bite).
-- D254: the compiled term is the REALIZATION of the checker's derivation
-- (`realize`), the reference elaboration the Spec reads.
compileFunBody-aux : ∀ {ctx : NamedCtx} {body : RawExpr}
  → AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type)
  → Srf.⟦ NamedCtx.debruijn ctx ⟧ᶜ ≡ Unit
  → TE.VerifiedCheckResult ctx body ty → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFunBody-aux m doOpt ctx polys impsOf name ty δ-unit (TE.failure err , _) =
  inj₁ ("Type error in " ++ name ++ ": " ++ Error.renderError err)
compileFunBody-aux m doOpt ctx polys impsOf name ty δ-unit (TE.success _ _ _ _ , w) =
  -- Plan 0.19: the user-fn list (= `ctx + self`) is `userFns`. Plan 0.103
  -- phase 1c: a telescope body is linked in ITS declaration imports
  -- (`impsOf`), not in this function's. External syscalls are handled via
  -- the qualified-name path and never reach this resolver.
  let userList = (name , ty) ∷ TopCtx.tdefs ctx
      resolved = resolveExpr polys impsOf userList 0 (realize w)
      ir = elaborateFull m resolved
  in inj₂ (subst (λ X → IR X ⌊ ty ⌋) (cong ⌊_⌋ δ-unit) (if doOpt then optimize ir else ir))

compileFunBody : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → RawExpr → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFunBody m doOpt ctx polys impsOf name ty expr =
  compileFunBody-aux m doOpt ctx polys impsOf name ty refl
    (TE.checkElabV (ctxWithImportsAndPolys ctx polys) expr ty)

-- | Compile a function with main validation
-- For main: validates type is Eff Unit A before compiling
-- For other functions: compiles directly
--
-- Explicit-argument aux form (Plan 0.48): `compileFun-aux` dispatches on the
-- `name == "main"` Bool, `compileFun-main-aux` on the `validateMain` result —
-- both `doOpt`-free guards, so success rides on `compileFunBody` alone.
compileFun-main-aux : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → RawExpr → String ⊎ ⊤ → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFun-main-aux m doOpt ctx polys impsOf name ty expr (inj₁ err) = inj₁ err
compileFun-main-aux m doOpt ctx polys impsOf name ty expr (inj₂ _)   = compileFunBody m doOpt ctx polys impsOf name ty expr

compileFun-aux : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → RawExpr → Bool → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFun-aux m doOpt ctx polys impsOf name ty expr true  = compileFun-main-aux m doOpt ctx polys impsOf name ty expr (validateMain ty)
compileFun-aux m doOpt ctx polys impsOf name ty expr false = compileFunBody m doOpt ctx polys impsOf name ty expr

compileFun : AllocMode → Bool → TopCtx → PolyCtx → (String → TopCtx) → (name : String) (ty : Type) → RawExpr → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋
compileFun m doOpt ctx polys impsOf name ty expr = compileFun-aux m doOpt ctx polys impsOf name ty expr (name == "main")

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
    -- (D274: no `cfIsPrimitive`. An FFI declaration is a generator of Σ, not
    -- a definition, so it is never compiled to a function.)

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

inferType : TopCtx → PolyCtx → RawExpr → String ⊎ Type
inferType ctx polys body with TE.inferElab (ctxWithImportsAndPolys ctx polys) body
... | TE.success A _ _ _ _ = inj₂ A
-- D072: bidirectional synthesis failed — ask the principal-type oracle
-- (ground answers only here; schema answers route via the telescope, M3).
... | TE.failure err       =
      inferType-validate (ctxWithImportsAndPolys ctx polys) body
        ("Cannot infer type: " ++ Error.renderError err)
        (Principal.principalGround (ctxWithImportsAndPolys ctx polys) body)

-- | The explicit signature if given, otherwise the inferred type (D007).
resolveFunType : TopCtx → PolyCtx → Maybe Type → RawExpr → String ⊎ Type
resolveFunType ctx polys (just ty) body = inj₂ ty
resolveFunType ctx polys nothing   body = inferType ctx polys body

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
------------------------------------------------------------------------
-- Plan 0.103 phase 1: type every GROUND telescope entry once, at its
-- declaration (`Spec.Module.PolysTyped`). A walk over the monomorphic defs
-- mirroring `AllFunsTyped`, checking the entries declared at each position.
-- De-withed: every decision is an explicit argument (the proofs reduce it).
------------------------------------------------------------------------

seqCheck : String ⊎ ⊤ → String ⊎ ⊤ → String ⊎ ⊤
seqCheck (inj₁ e) _ = inj₁ e
seqCheck (inj₂ _) r = r

checkOK : ∀ {ctx e T} → TE.VerifiedCheckResult ctx e T → String ⊎ ⊤
checkOK (TE.failure err , _)       = inj₁ (renderError err)
checkOK (TE.success _ _ _ _ , _)   = inj₂ tt

------------------------------------------------------------------------
-- D241 (plan 0.103 6c′): compile the module TELESCOPE, in declaration order.
-- Each definition is checked in its SCOPE — the definitions declared before
-- it — exactly as `Spec.Module.ModTele` types it.
------------------------------------------------------------------------

-- The compile-time scope: `Spec.Module.Scope` — the signature Σ, the
-- monomorphic definitions — with each telescope entry's DECLARATION scope (where
-- the resolver elaborates its body at a use).
record CScope : Set where
  constructor cscope
  field
    csig  : FunCtx
    cimps : FunCtx
    ctele : List (PolyFunInfo × TopCtx)

emptyCScope : CScope
emptyCScope = cscope emptyFunCtx emptyFunCtx []

-- What the top level holds: Σ and the definitions (D274).
ctop : CScope → TopCtx
ctop sc = topCtx (CScope.csig sc) (CScope.cimps sc)

telePolys : List (PolyFunInfo × TopCtx) → List PolyFunInfo
telePolys = DL.map proj₁

cpolys : CScope → PolyCtx
cpolys sc = buildPolyCtx (telePolys (CScope.ctele sc))

-- The declaration scope of the telescope entry a name refers to — the first
-- of that name, as `lookupPolyPrefix` finds it.
declImps     : List (PolyFunInfo × TopCtx) → String → TopCtx
declImps-aux : (e : PolyFunInfo × TopCtx) → List (PolyFunInfo × TopCtx) → (x : String)
             → Dec (pfunName (proj₁ e) ≡ x) → TopCtx
declImps []       x = emptyTopCtx
declImps (e ∷ es) x = declImps-aux e es x (pfunName (proj₁ e) SProp.≟ x)
declImps-aux e es x (yes _) = proj₂ e
declImps-aux e es x (no _)  = declImps es x

-- A monomorphic definition extends the definitions…
extendScope : CScope → String → Type → CScope
extendScope sc x ty = cscope (CScope.csig sc) (extendFunCtx (CScope.cimps sc) x ty) (CScope.ctele sc)

-- …an FFI declaration the signature Σ (D274)…
extendSig : CScope → String → Type → CScope
extendSig sc x ty = cscope (extendFunCtx (CScope.csig sc) x ty) (CScope.cimps sc) (CScope.ctele sc)

-- …and a telescope definition the telescope, with its declaration scope.
addEntry : CScope → PolyFunInfo → CScope
addEntry sc pfi = cscope (CScope.csig sc) (CScope.cimps sc) ((pfi , ctop sc) ∷ CScope.ctele sc)

consCF : CompiledFun → String ⊎ List CompiledFun → String ⊎ List CompiledFun
consCF cf (inj₁ err) = inj₁ err
consCF cf (inj₂ cfs) = inj₂ (cf ∷ cfs)

-- The walk, in explicit-aux form: each decision is a bound argument, so the
-- proofs case on it without the `with`-bite.
compileEntries : AllocMode → Bool → CScope → List Entry → String ⊎ List CompiledFun
ce-fun         : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → Bool → String ⊎ List CompiledFun
ce-prim        : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → Maybe Type → String ⊎ List CompiledFun
ce-prim-conc   : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → (ty : Type)
               → Maybe (IsConcrete ty) → Maybe (HonestFFI ty) → Maybe (RigidFree ty) → String ⊎ List CompiledFun
ce-mono        : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → String ⊎ Type → String ⊎ List CompiledFun
ce-mono-g      : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → (ty : Type)
               → Maybe (RigidFree ty) → String ⊎ List CompiledFun
ce-mono-ir     : AllocMode → Bool → CScope → (fi : FunInfo) → List Entry → (ty : Type)
               → String ⊎ IR ⌊ Unit ⌋ ⌊ ty ⌋ → String ⊎ List CompiledFun
ce-poly        : AllocMode → Bool → CScope → (pfi : PolyFunInfo) → List Entry → String ⊎ ⊤ → String ⊎ List CompiledFun

compileEntries m doOpt sc []                 = inj₂ []
compileEntries m doOpt sc (e-fun fi ∷ es)    = ce-fun m doOpt sc fi es (funIsPrimitive fi)
compileEntries m doOpt sc (e-poly pfi ∷ es)  =
  ce-poly m doOpt sc pfi es
    (checkOK (TE.checkElabV (ctxWithImportsAndPolys (ctop sc) (cpolys sc)) (pfunBody pfi) (rigidOf (pfunType pfi))))

ce-fun m doOpt sc fi es true  = ce-prim m doOpt sc fi es (funType fi)
ce-fun m doOpt sc fi es false =
  ce-mono m doOpt sc fi es (resolveFunType (ctop sc) (cpolys sc) (funType fi) (funBody fi))

-- An FFI declaration has NO body to type (D241) and is not compiled: it is a
-- generator of the signature Σ (D274), and a reference to it is the SigOp.
ce-prim m doOpt sc fi es nothing   = inj₁ ("FFI signature without a type: " ++ funName fi)
ce-prim m doOpt sc fi es (just ty) = ce-prim-conc m doOpt sc fi es ty (isConcrete? ty) (honest? ty) (rigidFree? ty)
ce-prim-conc m doOpt sc fi es ty nothing _ _ =
  inj₁ ("FFI signature `" ++ funName fi ++ "` is not concrete: " ++ showType ty)
ce-prim-conc m doOpt sc fi es ty (just _) nothing _ =
  inj₁ ("FFI signature `" ++ funName fi ++ "` hides an effect: " ++ showType ty)
ce-prim-conc m doOpt sc fi es ty (just _) (just _) nothing =
  inj₁ ("FFI signature `" ++ funName fi ++ "` is not ground: " ++ showType ty)
ce-prim-conc m doOpt sc fi es ty (just conc) (just _) (just _) =
  compileEntries m doOpt (extendSig sc (funName fi) ty) es

ce-mono m doOpt sc fi es (inj₁ err) = inj₁ err
ce-mono m doOpt sc fi es (inj₂ ty)  = ce-mono-g m doOpt sc fi es ty (rigidFree? ty)
-- D243: a monomorphic definition's type is ground.
ce-mono-g m doOpt sc fi es ty nothing =
  inj₁ ("The type of `" ++ funName fi ++ "` mentions a type parameter: " ++ showType ty)
ce-mono-g m doOpt sc fi es ty (just _) =
  ce-mono-ir m doOpt sc fi es ty
    (compileFun m doOpt (ctop sc) (cpolys sc) (declImps (CScope.ctele sc)) (funName fi) ty (funBody fi))
ce-mono-ir m doOpt sc fi es ty (inj₁ err) = inj₁ err
ce-mono-ir m doOpt sc fi es ty (inj₂ ir)  =
  consCF (mkCompiledFun (bare (funName fi)) ty ir)
         (compileEntries m doOpt (extendScope sc (funName fi) ty) es)

-- D243: a telescope definition is checked ONCE, at its schema with rigid
-- parameters; its uses are instances of it.
ce-poly m doOpt sc pfi es (inj₁ err) = inj₁ ("Type error in " ++ pfunName pfi ++ ": " ++ err)
ce-poly m doOpt sc pfi es (inj₂ _)   = compileEntries m doOpt (addEntry sc pfi) es

compileResolvedModule-aux : AllocMode → Bool → Module → String ⊎ List Entry → String ⊎ List CompiledFun
compileResolvedModule-aux m doOpt mod (inj₁ err) = inj₁ err
compileResolvedModule-aux m doOpt mod (inj₂ es)  = compileEntries m doOpt emptyCScope es

compileResolvedModule : AllocMode → Bool → Module → String ⊎ List CompiledFun
compileResolvedModule m doOpt mod =
  compileResolvedModule-aux m doOpt mod (extractFunctions (extractAliases mod) mod)

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
           (inj₁ err) → inj₁ err
           (inj₂ es)  → compileEntries m doOpt emptyCScope es


-- Plan 0.50 — the symbols THIS codegen actually emits as `.globl` labels, defined
-- on the SAME `CompiledFun` list `compileFromModule` renders (`compileResolvedModule`):
-- one per compiled function (D274: every one is a definition).
emittedSyms : List CompiledFun → List String
emittedSyms []         = []
emittedSyms (cf ∷ cfs) = once-symbol-path (cfName cf) ∷ emittedSyms cfs

moduleSyms-aux : String ⊎ List CompiledFun → List String
moduleSyms-aux (inj₁ _)   = []
moduleSyms-aux (inj₂ cfs) = emittedSyms cfs

moduleSyms : AllocMode → Bool → Module → List String
moduleSyms m doOpt mod = moduleSyms-aux (compileResolvedModule m doOpt mod)

------------------------------------------------------------------------
-- Target selection and compilation
------------------------------------------------------------------------


-- | Supported architectures — the single shared enum (re-exported so
-- existing `C.Arch` references downstream are unchanged).
open import Once.Target.Arch
open import Once.Denotation.Admissible using (AdmissibleM; admissibleM?; firstBadLit)
-- Plan 0.74 K4: the rounding-warning channel. Re-exported here — not threaded
-- through `compile` — because warnings do not change what is compiled, and
-- keeping them a separate OBSERVATION is what stops them leaking into
-- `correct`. This re-export is also what puts them on the extraction path.
open import Data.Nat.Show renaming (show to showNat)
open import Data.Integer using (ℤ)
open import Data.Nat using (_∸_)
open import Data.Integer.Show renaming (show to showℤ)

-- (Plan 0.107: the per-function TEXT walk that stood here — `archTarget`,
-- `compileAllWithTarget`, and the label/symbol lists read off it for the
-- toolchain axiom's preconditions — is GONE. The file is `emit` of the program
-- image below, and the text is its print: one walk, D262.)

------------------------------------------------------------------------
-- PLAN 0.107: THE PROGRAM, AND THE ASSEMBLY FILE — ONE WALK.
--
-- The program the proofs reason about and the file the binary is assembled
-- from are computed HERE, from the same compile result, by the same
-- functions. The emitted text is `printFile` of the file. (These definitions
-- used to live in `Adequacy.SourceTrace`, beside a SEPARATE text walk that
-- only the toolchain axiom related to them — D261.)
------------------------------------------------------------------------

-- | `main`'s type, `IO Unit`.
EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

isEffUU? : (T : Type) → Maybe (T ≡ EffUU)
isEffUU? T with T ≟T EffUU
... | yes e = just e
... | no _  = nothing


-- D253: `main` is an entry like any other; the program's own `main` is the CALL
-- of it.
mainCall : IR ⌊ Unit ⌋ ⌊ Unit ⌋
mainCall = Call (bare "main")

findMain-here :
  (cf : CompiledFun) → Dec (cfName cf ≡ bare "main") → Maybe (cfType cf ≡ EffUU)
  → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
findMain-here cf (yes _) (just _) cont = just mainCall
findMain-here cf (yes _) nothing  cont = cont
findMain-here cf (no  _) _        cont = cont

-- | A module is a PROGRAM when it has an entry `main : IO Unit`.
findMain : List CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
findMain []         = nothing
findMain (cf ∷ rest) =
  findMain-here cf (cfName cf ≟cn bare "main") (isEffUU? (cfType cf)) (findMain rest)

moduleToIR-aux : String ⊎ List CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR-aux (inj₁ _)    = nothing
moduleToIR-aux (inj₂ funs) = findMain funs

moduleToIR : Module → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋)
moduleToIR mod = moduleToIR-aux (compileResolvedModule Heap false mod)

-- D244: the function table, LATEST-FIRST; each entry the DIRECT-CALL morphism
-- (D064, `directCallIR`) that `once_<name>` implements.
irFunOf : CompiledFun → IRFun
irFunOf cf = irFun (cfName cf) ⌊ proj₁ dc ⌋ ⌊ proj₁ (proj₂ dc) ⌋ (proj₂ (proj₂ dc))
  where dc = directCallIR (cfType cf) (cfIR cf)

tableOf-go : List CompiledFun → List IRFun → List IRFun
tableOf-go []         sofar = sofar
tableOf-go (cf ∷ cfs) sofar = tableOf-go cfs (irFunOf cf ∷ sofar)

tableOf : List CompiledFun → List IRFun
tableOf funs = tableOf-go funs []

tableOfResult : String ⊎ List CompiledFun → List IRFun
tableOfResult (inj₁ _)    = []
tableOfResult (inj₂ funs) = tableOf funs

moduleTable : Module → List IRFun
moduleTable mod = tableOfResult (compileResolvedModule Heap false mod)

programAt : List IRFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Maybe IRProgram
programAt tbl nothing   = nothing
programAt tbl (just ir) = just (irProgram tbl ir)

moduleToProgram : Module → Maybe IRProgram
moduleToProgram mod = programAt (moduleTable mod) (moduleToIR mod)

-- D165/D244: THE PROGRAM THE BACKEND COMPILES — every definition arith-lifted.
rewrite-fun : IRFun → IRFun
rewrite-fun e = irFun (fname e) (fdom e) (fcod e) (proj₁ (rewrite-ir (fbody e)))

rewrite-table : List IRFun → List IRFun
rewrite-table []       = []
rewrite-table (e ∷ es) = rewrite-fun e ∷ rewrite-table es

rewrite-program : IRProgram → IRProgram
rewrite-program p = irProgram (rewrite-table (table p)) (proj₁ (rewrite-ir (main p)))

-- …and the arith blocks that lifting minted, from the SAME `rewrite-ir` calls.
program-blocks : IRProgram → List ArithBlock
program-blocks p = proj₂ (rewrite-ir (main p)) DL.++ table-blocks (table p)
  where
    table-blocks : List IRFun → List ArithBlock
    table-blocks []       = []
    table-blocks (e ∷ es) = proj₂ (rewrite-ir (fbody e)) DL.++ table-blocks es

-- One block per symbol (the first): two definitions lifting the same
-- arithmetic mint the same digest, and a symbol is defined once.
dedup-go : List String → List (String × ArithBlock) → List (String × ArithBlock)
dedup-go seen []             = []
dedup-go seen ((s , b) ∷ bs) =
  if BLA.any (λ x → x == s) seen then dedup-go seen bs
                                 else (s , b) ∷ dedup-go (s ∷ seen) bs

dedup-blocks : List (String × ArithBlock) → List (String × ArithBlock)
dedup-blocks = dedup-go []

-- An arith block's symbol — what every arch's `arith-block-symbol` is.
block-symbol : ArithBlock → String
block-symbol b = once-symbol-own (block-name (block-body b))

-- The file's block table, by symbol, once each (`blocks-<arch>`).
block-syms : List ArithBlock → List String
block-syms bs = DL.map proj₁ (dedup-blocks (DL.map (λ b → block-symbol b , b) bs))

-- The symbols the program's SigOps call (`NodesOK.leaf-syms`, leaf by leaf).
calls-of : IRProgram → List String
calls-of p = leaf-syms (main p) DL.++ DL.concatMap (λ e → leaf-syms (fbody e)) (table p)

-- plan 0.107 §9 2D / D274: the interpretation symbols the file calls and `ld`
-- resolves are EXACTLY the SigOp symbols the (rewritten) program calls that are
-- not its own arith blocks — the names the code actually calls, never a
-- declaration's spelling. A call to anything else is defined in the file.
is-extern? : (p : IRProgram) (s : String) → Dec (¬ (s ∈ˢ block-syms (program-blocks p)))
is-extern? p s = ¬? (s ∈ˢ? block-syms (program-blocks p))

externs-of : IRProgram → List String
externs-of p = DL.filter (is-extern? p) (calls-of (rewrite-program p))

-- The entry unit's owner: a name no definition can have (an identifier cannot
-- start with a digit), so its labels and symbol cannot clash.
entry-owner : CanonicalName
entry-owner = bare "0entry"


------------------------------------------------------------------------
-- The per-arch file: `code` IS the lowered program image, and `_start` is its
-- first instruction — the image's `c-start` (the heap register, the outermost
-- frame); `main`'s unit ends in a silent stop. No syscall, no hand-written
-- runtime: the same on bare metal and under an OS (plan 0.107 §2½).
------------------------------------------------------------------------

FileOf : Arch → Set
FileOf x86-64  = X64F.Image
FileOf x86-32  = X32F.Image
FileOf riscv64 = RVF.Image

printFile : (arch : Arch) → FileOf arch → String
printFile x86-64  = X64F.print
printFile x86-32  = X32F.print
printFile riscv64 = RVF.print


image-of : IRProgram → AbstractTrace
image-of p = program-image entry-owner (rewrite-program p)

-- the file's arith blocks: the program's, by symbol, once each
blocks-x86-64 : IRProgram → List (String × X64F.Payload)
blocks-x86-64 p =
  DL.map (λ sb → proj₁ sb , X64A.block-payload (proj₂ sb))
    (dedup-blocks (DL.map (λ b → X64A.arith-block-symbol b , b) (program-blocks p)))

emit-x86-64 : IRProgram → X64F.Image
emit-x86-64 p =
  X64F.mkImage (proj₂ (X64L.compile-trace-cnt entry-owner 0 (image-of p))) (just 0) (blocks-x86-64 p) (externs-of p)

-- the file's arith blocks: the program's, by symbol, once each
blocks-x86-32 : IRProgram → List (String × X32F.Payload)
blocks-x86-32 p =
  DL.map (λ sb → proj₁ sb , X32A.block-payload (proj₂ sb))
    (dedup-blocks (DL.map (λ b → X32A.arith-block-symbol b , b) (program-blocks p)))

emit-x86-32 : IRProgram → X32F.Image
emit-x86-32 p =
  X32F.mkImage (proj₂ (X32L.compile-trace-cnt entry-owner 0 (image-of p))) (just 0) (blocks-x86-32 p) (externs-of p)

-- the file's arith blocks: the program's, by symbol, once each
blocks-riscv64 : IRProgram → List (String × RVF.Payload)
blocks-riscv64 p =
  DL.map (λ sb → proj₁ sb , RVA.block-payload (proj₂ sb))
    (dedup-blocks (DL.map (λ b → RVA.arith-block-symbol b , b) (program-blocks p)))

emit-riscv64 : IRProgram → RVF.Image
emit-riscv64 p =
  RVF.mkImage (proj₂ (RVL.compile-trace-cnt entry-owner 0 (image-of p))) (just 0) (blocks-riscv64 p) (externs-of p)

emitProgram : (arch : Arch) → IRProgram → FileOf arch
emitProgram x86-64  = emit-x86-64
emitProgram x86-32  = emit-x86-32
emitProgram riscv64 = emit-riscv64

-- A LIBRARY (no `main`): its functions only — no entry unit, no `_start`. The
-- verified compiler never assembles one (it has no behaviour); the CLI emits it.
lib-image : List IRFun → AbstractTrace
lib-image tbl = fns-image 0 (rewrite-table tbl)

-- A library as a program whose `main` does nothing: its blocks and externs
-- are the table's.
lib-program : List IRFun → IRProgram
lib-program tbl = irProgram tbl id

lib-blocks : List IRFun → List ArithBlock
lib-blocks tbl = program-blocks (lib-program tbl)

emitLibrary : (arch : Arch) → List IRFun → FileOf arch
emitLibrary x86-64 tbl =
  X64F.mkImage (proj₂ (X64L.compile-trace-cnt entry-owner 0 (lib-image tbl))) nothing
    (DL.map (λ sb → proj₁ sb , X64A.block-payload (proj₂ sb))
      (dedup-blocks (DL.map (λ b → X64A.arith-block-symbol b , b) (lib-blocks tbl)))) (externs-of (lib-program tbl))
emitLibrary x86-32 tbl =
  X32F.mkImage (proj₂ (X32L.compile-trace-cnt entry-owner 0 (lib-image tbl))) nothing
    (DL.map (λ sb → proj₁ sb , X32A.block-payload (proj₂ sb))
      (dedup-blocks (DL.map (λ b → X32A.arith-block-symbol b , b) (lib-blocks tbl)))) (externs-of (lib-program tbl))
emitLibrary riscv64 tbl =
  RVF.mkImage (proj₂ (RVL.compile-trace-cnt entry-owner 0 (lib-image tbl))) nothing
    (DL.map (λ sb → proj₁ sb , RVA.block-payload (proj₂ sb))
      (dedup-blocks (DL.map (λ b → RVA.arith-block-symbol b , b) (lib-blocks tbl)))) (externs-of (lib-program tbl))

-- | THE FILE OF A COMPILE RESULT — the one walk: a program file when the module
-- has `main`, a library file otherwise; the compile error if it failed.
emit-at : (arch : Arch) → List CompiledFun → Maybe (IR ⌊ Unit ⌋ ⌊ Unit ⌋) → FileOf arch
emit-at arch funs nothing   = emitLibrary arch (tableOf funs)
emit-at arch funs (just ir) = emitProgram arch (irProgram (tableOf funs) ir)

emitFromCompiled : (arch : Arch) → String ⊎ List CompiledFun → String ⊎ FileOf arch
emitFromCompiled arch (inj₁ err)  = inj₁ err
emitFromCompiled arch (inj₂ funs) = inj₂ (emit-at arch funs (findMain funs))

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

-- plan 0.107: THE TEXT IS THE PRINT OF THE FILE (one walk).
built-of : (arch : Arch) → String ⊎ FileOf arch → CompileResult
built-of arch (inj₁ err) = Error err
built-of arch (inj₂ F)   = Built (printFile arch F)

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
{-# CATCHALL #-}
showFunInfos (fi ∷ rest) = showFunInfo fi ++ "\n" ++ showFunInfos rest

showPolyFunInfos : List PolyFunInfo → String
showPolyFunInfos [] = ""
showPolyFunInfos (pfi ∷ []) = showPolyFunInfo pfi
{-# CATCHALL #-}
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
       (inj₁ err) → Error err
       (inj₂ es)  →
         case stage of λ where
           Parse → Parsed (funsOf es) (polysOf es)
           Check → case compileEntries m doOpt emptyCScope es of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) → Checked compiled
           Build → case compileEntries m doOpt emptyCScope es of λ where
             (inj₁ err) → Error err
             (inj₂ compiled) → built-of arch (emitFromCompiled arch (inj₂ compiled))


-- | Same as `compile` but starting from a pre-resolved `Module`.
-- Haskell uses this after driving transitive-import I/O and calling
-- `resolveImports` to flatten `DImport` decls into owner-tagged
-- `DSignature` decls. Skips the `parse source` step of `compile`.
-- Plan 0.14 follow-up: takes AllocMode from CLI --alloc flag.
-- Explicit-argument aux form (Plan 0.48): `cfm-ef-aux` dispatches on
-- `extractFunctions`, `cfm-stage-aux` on the stage, and the Check/Build emit
-- helpers on the `compileEntries` result — the SAME `compileEntries` call as
-- `compileResolvedModule-aux`, which is what lets `main⇒built` relate them.

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

-- PLAN 0.74 J6: THE IR GATE WAS SCAFFOLDING, AND IT IS GONE.
--
-- A second gate over the literals the MACHINE materialises (`Once.IRLits`,
-- `AdmissibleIR`, `cfm-build-lits`) lived here briefly. Its job was
-- DIAGNOSTIC: making "elaboration preserves the programmer's literals"
-- load-bearing turned a silent defect into a red tree, and that is what forced
-- the elaborator fold (`-5` is ONE literal) and dragged J5's `Word64` bakes
-- out of hiding. Both landed; what it was built to detect is fixed.
--
-- DELETED rather than left unwired, because an unwired gate is dead code that
-- hides a gap instead of surfacing it. Keeping it WIRED was the other option
-- and costs more than it buys: `ElabPreservesLits` would become a PREMISE on
-- `correct` itself, and that premise is a global induction over the
-- elaborator — a real open theorem, not a formality.
--
-- THE INVARIANT IT STOOD FOR, recorded so it is not rediscovered:
--
--     compiledIntLits (compile of m)  ⊆  moduleIntLits m
--
-- and it is nearly local: `Surface.Elaborate.intLit` is the ONLY producer of
-- an IR `Int` literal — three call sites, each already holding a source
-- literal — so whoever proves it has a bounded job, and proving it re-wires
-- the gate at zero cost to `correct`. See D117.

-- Explicit-argument aux (no `with`), matching this file's convention, so the
-- decision stays a subterm downstream proofs can rewrite by.
-- plan 0.107: THE FILE the gated build produces — the verified compiler
-- assembles it, the CLI prints it. One pipeline, two consumers.
cfm-file-gated : AllocMode → Bool → (arch : Arch) → (mod : Module)
               → List Entry
               → Dec (AdmissibleM arch mod) → String ⊎ FileOf arch
cfm-file-gated m doOpt arch mod es (no  _) = inj₁ (litRangeError arch mod)
cfm-file-gated m doOpt arch mod es (yes _) =
  emitFromCompiled arch (compileEntries m doOpt emptyCScope es)

cfm-file-ef : AllocMode → Bool → (arch : Arch) → Module → String ⊎ List Entry → String ⊎ FileOf arch
cfm-file-ef m doOpt arch mod (inj₁ err) = inj₁ err
cfm-file-ef m doOpt arch mod (inj₂ es)  = cfm-file-gated m doOpt arch mod es (admissibleM? arch mod)

compileFileFromModule : AllocMode → Bool → (arch : Arch) → Module → String ⊎ FileOf arch
compileFileFromModule m doOpt arch mod =
  cfm-file-ef m doOpt arch mod (extractFunctions (extractAliases mod) mod)

cfm-stage-aux : AllocMode → Stage → Bool → Arch → Module → List Entry → CompileResult
cfm-stage-aux m Parse doOpt arch mod es = Parsed (funsOf es) (polysOf es)
cfm-stage-aux m Check doOpt arch mod es =
  cfm-check-emit (compileEntries m doOpt emptyCScope es)
cfm-stage-aux m Build doOpt arch mod es =
  built-of arch (cfm-file-gated m doOpt arch mod es (admissibleM? arch mod))

cfm-ef-aux : AllocMode → Stage → Bool → Arch → Module → String ⊎ List Entry → CompileResult
cfm-ef-aux m stage doOpt arch mod (inj₁ err) = Error err
cfm-ef-aux m stage doOpt arch mod (inj₂ es)  = cfm-stage-aux m stage doOpt arch mod es

compileFromModule : AllocMode → Stage → Bool → Arch → Module → CompileResult
compileFromModule m stage doOpt arch mod =
  cfm-ef-aux m stage doOpt arch mod (extractFunctions (extractAliases mod) mod)