-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.Classify
--
-- Classifier helpers and named contexts shared between the elaborator
-- and the judgment.
--
-- Extracted from `Once.TypeCheck.Elaborate` (Plan 0.4 T0 Option B
-- preparation) to break the import cycle that prevented
-- `Elaborate.agda` from importing `Judgment.agda`. After the split:
--
--   * `Once.TypeCheck.Judgment`  imports `Classify` (no longer
--     `Elaborate`).
--   * `Once.TypeCheck.Elaborate` imports `Classify` and re-exports
--     it `public` for backward compatibility, then imports
--     `Judgment` (the cycle being broken makes this admissible).
--
-- Contents are unchanged from their previous location in
-- `Elaborate.agda`; only the host module has changed.
------------------------------------------------------------------------

module Once.TypeCheck.Classify where

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using (_≟_)
import Data.String
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Type
open import Once.SigEffect using (SigEffect)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Raw as Raw
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.TypeCheck.Context using (Ctx; ∅; name)
open import Once.TypeCheck.Context as Context using () renaming (_,_∷_ to extendCtx)
open import Once.Surface.Syntax as Surface using ()
  renaming (Ctx to SCtx; Expr to SExpr; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)
open import Once.Surface.Thinning using (weaken)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Named Context with de Bruijn Correspondence
------------------------------------------------------------------------

-- | Imported primitives from other modules (e.g., "S.exit0" → Eff Unit Unit)
-- These are populated from qualified imports like "import M as S"
Imports : Set
Imports = List (String × Type)

-- | Empty imports
emptyImports : Imports
emptyImports = []

-- | Declared `! <shape>` EffectShape annotations of imported external
-- arrows, keyed by the SAME qualified name as `imports` (e.g.
-- "S.exit" ↦ halts). Plan 0.38 M0.2: this is the ONLY channel by which
-- the elaborator learns an external arrow's effect — a PARALLEL map, so
-- `lookupImport`/`FunInfo`/the verified judgment stay untouched. An entry
-- is absent (`nothing` on lookup) when no `! <shape>` was declared; the
-- elaborator then falls back to the structural default (pure arrow ↦
-- `Pure`, `Eff`-arrow ↦ `Emits`).
SigEffectCtx : Set
SigEffectCtx = List (String × SigEffect)

emptySigEffects : SigEffectCtx
emptySigEffects = []

-- | Look up a declared effect shape by qualified import name.
lookupSigEffect : SigEffectCtx → String → Maybe SigEffect
lookupSigEffect [] _ = nothing
lookupSigEffect ((n , se) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just se
... | no  _ = lookupSigEffect rest x

-- | Polymorphic-definition context (plan 0.6.2). Carries each
-- user-declared poly def's schema and body so they can be
-- specialised at call sites via schema instantiation. Structurally
-- `List (name, schema, body)`; kept separate from `imports` (which
-- is ground-typed) because lookup resolves differently.
PolyCtx : Set
PolyCtx = List (String × PolyType × RawExpr)

emptyPolyCtx : PolyCtx
emptyPolyCtx = []

-- | Lookup a polymorphic def by name.
lookupPoly : PolyCtx → String → Maybe (PolyType × RawExpr)
lookupPoly [] _ = nothing
lookupPoly ((n , schema , body) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just (schema , body)
... | no  _ = lookupPoly rest x

-- | Remove the named entry from a PolyCtx. Used during schema
-- instantiation to prevent direct cycles (a poly body specialising
-- to its own name's instantiation would loop); the recursive
-- `checkElab` call sees a `PolyCtx` without the name being
-- specialised, so that name's use sites inside the body fall
-- through to the non-poly lookup path.
-- Plan 0.6.2 Phase 4 (termination principlization).
removePoly : String → PolyCtx → PolyCtx
removePoly _ [] = []
removePoly x ((n , s , b) ∷ rest) with StrProp._≟_ n x
... | yes _ = rest
... | no  _ = (n , s , b) ∷ removePoly x rest

-- | When `x` is found in `polys`, `removePoly` strictly shrinks it.
-- Load-bearing for well-founded termination of the poly-splice recursion
-- in `resolveExpr`. Plan 0.6.2 Phase 4 (final).
removePoly-decreases :
  ∀ {r : PolyType × RawExpr} (x : String) (polys : PolyCtx)
  → lookupPoly polys x ≡ just r
  → length (removePoly x polys) < length polys
removePoly-decreases x [] ()
removePoly-decreases x ((n , s , b) ∷ rest) eq with StrProp._≟_ n x
... | yes _ = s≤s ≤-refl
... | no  _ = s≤s (removePoly-decreases x rest eq)

-- | A named context paired with its de Bruijn representation
-- Includes a fresh counter for generating unique type variables during instantiation
-- and imported primitives from other modules
record NamedCtx : Set where
  constructor mkCtx
  field
    size        : ℕ
    named       : Ctx
    debruijn    : SCtx size
    freshCounter : ℕ  -- For generating fresh type variables (α₀, α₁, α₂, ...)
    imports     : Imports  -- Imported primitives (qualified names → types)
    polys       : PolyCtx  -- User polymorphic definitions (plan 0.6.2)
    sigEffects  : SigEffectCtx  -- Declared `! <shape>` effects (plan 0.38 M0.2)

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅ 0 emptyImports emptyPolyCtx emptySigEffects

-- | Create context with imports
ctxWithImports : Imports → NamedCtx
ctxWithImports imps = mkCtx 0 ∅ S∅ 0 imps emptyPolyCtx emptySigEffects

-- | Create context with imports and polymorphic defs. Plan 0.6.2.
-- `sigEffects` defaults to empty (the verified judgment / reconstruction
-- sites use this; the declared-effect map enters only at the top-level
-- body context via `ctxWithImportsAndSelfAndPolys'`). Plan 0.38 M0.2.
ctxWithImportsAndPolys : Imports → PolyCtx → NamedCtx
ctxWithImportsAndPolys imps polys = mkCtx 0 ∅ S∅ 0 imps polys emptySigEffects

-- | Create context with imports and self-reference for recursive definitions
-- The function's own name and type are added to the imports list so it can call itself.
-- This causes recursive calls to elaborate to `SigOp "name"` which the C backend
-- handles as a function call.
ctxWithImportsAndSelf : Imports → String → Type → NamedCtx
ctxWithImportsAndSelf imps name ty =
  ctxWithImports ((name , ty) ∷ imps)

-- | Same as `ctxWithImportsAndSelf` but also carries a polymorphic
-- context. Plan 0.6.2 — used by `compileFun` to make poly defs
-- available to each ground function's body during typecheck.
-- Plan 0.38 M0.2: also seeds the declared `! <shape>` effect map; this
-- is the ONE site the real map enters elaboration (the body context).
ctxWithImportsAndSelfAndPolys : Imports → PolyCtx → SigEffectCtx → String → Type → NamedCtx
ctxWithImportsAndSelfAndPolys imps polys sigEffs name ty =
  mkCtx 0 ∅ S∅ 0 ((name , ty) ∷ imps) polys sigEffs

-- | Extend context with a new binding (preserves fresh counter, imports, polys, sigEffects)
extendNamedCtx : NamedCtx → String → Type → NamedCtx
extendNamedCtx (mkCtx n Γ Δ fresh imps polys sigEffs) x A =
  mkCtx (suc n) (extendCtx Γ x A) (Δ S, A) fresh imps polys sigEffs

-- | Bump fresh counter (for generating new type variables)
bumpFresh : NamedCtx → NamedCtx
bumpFresh (mkCtx n Γ Δ fresh imps polys sigEffs) = mkCtx n Γ Δ (suc fresh) imps polys sigEffs

-- | Generate fresh type variable name
freshTVar : ℕ → String
freshTVar n = "α" ++ showℕ n
------------------------------------------------------------------------
-- Variable Lookup with Weakening and Instantiation
------------------------------------------------------------------------

-- | Look up a type in the imports list by name
lookupImport : Imports → String → Maybe Type
lookupImport [] _ = nothing
lookupImport ((n , ty) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just ty
... | no  _ = lookupImport rest x
-- | Local lookup walker. Top-level (not a where-helper inside
-- lookupLocal) so external `with lookupLocal ctx x` aligns
-- syntactically with the elaborator's internal `with lookupLocal ctx x
-- in eq` — Agda would otherwise reduce lookupLocal's body via the
-- where-helper, generating a different scrutinee shape that breaks
-- with-abstraction unification.
lookupLocal-go : ∀ {m} (x : String) (Γ : Ctx) (Δ' : SCtx m)
               → Maybe (∃[ A ] ∃[ Ψ ] (SExpr Δ' Ψ A))
lookupLocal-go x [] S∅ = nothing
lookupLocal-go x [] (_ S, _ ^ _) = nothing
lookupLocal-go x (_ ∷ _) S∅ = nothing
lookupLocal-go {m = suc m'} x (b ∷ Γ') (Δ' S, B ^ _) with Data.String._≟_ x (name b)
... | yes _ = just (B , _ , Surface.var zero)
... | no _  with lookupLocal-go x Γ' Δ'
...   | nothing        = nothing
...   | just (A , Ψ , se) = just (A , _ , weaken se)

lookupLocal : (ctx : NamedCtx) → String
            → Maybe (∃[ A ] ∃[ Ψ ] (SExpr (NamedCtx.debruijn ctx) Ψ A))
lookupLocal ctx x = lookupLocal-go x (NamedCtx.named ctx) (NamedCtx.debruijn ctx)

------------------------------------------------------------------------
-- Plan 0.4 T2: lookup view datatypes
--
-- A view that bundles the lookup outcome WITH its defining equation.
-- Pattern-matching on a constructor directly yields the eq, sidestepping
-- the with-helper opacity that captured-`refl` arguments suffer when
-- abstracted by external `with` clauses (per
-- `feedback_with_abstraction.md`: change the operational function, not
-- the proof tactics). Mirrors `AppHeadView` in spirit.
------------------------------------------------------------------------

data LookupLocalView (ctx : NamedCtx) (x : String) : Set where
  llv-found : ∀ {A Ψ se} → lookupLocal ctx x ≡ just (A , Ψ , se) → LookupLocalView ctx x
  llv-not-found : lookupLocal ctx x ≡ nothing → LookupLocalView ctx x

inspectLookupLocal : (ctx : NamedCtx) (x : String) → LookupLocalView ctx x
inspectLookupLocal ctx x with lookupLocal ctx x in eq
... | just (A , Ψ , se) = llv-found eq
... | nothing           = llv-not-found eq

data LookupImportView (ctx : NamedCtx) (x : String) : Set where
  liv-found : ∀ {T} → lookupImport (NamedCtx.imports ctx) x ≡ just T → LookupImportView ctx x
  liv-not-found : lookupImport (NamedCtx.imports ctx) x ≡ nothing → LookupImportView ctx x

inspectLookupImport : (ctx : NamedCtx) (x : String) → LookupImportView ctx x
inspectLookupImport ctx x with lookupImport (NamedCtx.imports ctx) x in eq
... | just T  = liv-found eq
... | nothing = liv-not-found eq

-- | Plan 0.6.2 Phase 3b: for `compose f g` at expected `A → C`,
-- determine the intermediate type `B` from `g`'s structural shape.
-- Plan 0.4 T2 follow-up (rule-split): this is now the *only* path for
-- t-compose-check; the inferElab-driven path (path 2) was dropped
-- because the typing rule must be locally decidable in a no-unification
-- bidirectional system.
composeArgB : NamedCtx → RawExpr → Type → Maybe Type
-- fst : (X * Y) → X, so B = X when A = X * Y.
composeArgB ctx (Raw.RVar "fst") (X * _) = just X
-- snd : (X * Y) → Y, so B = Y when A = X * Y.
composeArgB ctx (Raw.RVar "snd") (_ * Y) = just Y
-- id : X → X, so B = A.
composeArgB ctx (Raw.RVar "id") A = just A
-- terminal : X → Unit, so B = Unit.
composeArgB ctx (Raw.RVar "terminal") _ = just Unit
-- User poly name: look up schema, match domain, extract codomain.
-- Plan 0.36 Phase 1: fall back to the monomorphic named-def type (`imports`)
-- and read off its codomain, so point-free composes of named morphisms
-- (e.g. `compose exit (arr seven)`, `compose emitAll (arr getXs)`) recover B.
composeArgB ctx (Raw.RVar name) A with lookupPoly (NamedCtx.polys ctx) name
... | just (schema , _) = schemaArrowCodomain schema A
... | nothing with lookupImport (NamedCtx.imports ctx) name
...   | just (_ Once.Type.⇒[ _ ] C) = just C
...   | _ = nothing
-- Plan 0.50 Stage 3: RESOLVED canonical name — mirror the bare-name lookup via
-- `showCanonical cn` (own-module/import sigs are keyed by it).
composeArgB ctx (Raw.RResolved cn) A with lookupPoly (NamedCtx.polys ctx) (showCanonical cn)
... | just (schema , _) = schemaArrowCodomain schema A
... | nothing with lookupImport (NamedCtx.imports ctx) (showCanonical cn)
...   | just (_ Once.Type.⇒[ _ ] C) = just C
...   | _ = nothing
-- Nested compose: recurse.
composeArgB ctx (Raw.RApp (Raw.RApp (Raw.RVar "compose") f') g') A with composeArgB ctx g' A
... | nothing = nothing
... | just B' with composeArgB ctx f' B'
...   | nothing = nothing
...   | just C  = just C
-- Plan 0.36 Phase 1: `arr g` (effect lift) preserves the underlying arrow's
-- domain/codomain, so B-recovery sees through it. Lets a pure morphism be
-- lifted into an effectful compose (single-π: `compose emit (arr fst)`).
composeArgB ctx (Raw.RApp (Raw.RVar "arr") g') A = composeArgB ctx g' A
-- Plan 0.41 / D018: an integer literal is the const morphism `_ → Int`
-- (a global element), so as a `compose`-arm its codomain is `Int`.
composeArgB ctx (Raw.RInt _) _ = just Int
-- Other shapes: compose can't proceed.
composeArgB _ _ _ = nothing

-- | Recover the DOMAIN of a compose-head `f`. In `compose f g : A → C`, the
-- middle type `B` is the shared type of `f : B → C` and `g : A → B`, so it is
-- determined by *either* arm. `composeArgB` reads it off `g`'s codomain; this
-- is the symmetric partner that reads it off `f`'s domain (by lookup). Needed
-- when `g` is a value-shape whose type `composeArgB` can't reveal (e.g. an
-- `In(…)` construction) but `f` is a named morphism (e.g. `emitAll : Mu → Unit`).
domainOfHead : NamedCtx → RawExpr → Maybe Type
domainOfHead ctx (Raw.RVar name) with lookupImport (NamedCtx.imports ctx) name
... | just (D Once.Type.⇒[ _ ] _) = just D
... | _ = nothing
domainOfHead ctx (Raw.RApp (Raw.RVar "arr") f') = domainOfHead ctx f'
-- Plan 0.50 Stage 3: a RESOLVED canonical name behaves like its bare form (the
-- import table is keyed by `showCanonical cn`), so point-free composes survive
-- the resolver's `RVar → RResolved` canonicalization.
domainOfHead ctx (Raw.RResolved cn) with lookupImport (NamedCtx.imports ctx) (showCanonical cn)
... | just (D Once.Type.⇒[ _ ] _) = just D
... | _ = nothing
domainOfHead _ _ = nothing

-- | Symmetric B-recovery for `compose f g` at `A → C`: try `g`'s codomain
-- (`composeArgB`), else fall back to `f`'s domain (`domainOfHead`). Fixes
-- `composeArgB`'s g-only asymmetry — `B` is recoverable from either arm.
-- | Pick the first `just`, else the fallback. A plain (non-`with`) helper so
-- `composeMid ctx f g A` stays an abstractable neutral — needed by the
-- `morph-complete` proof (`with composeMid … | eqB`); see MorphComplete.
composeMid-pick : Maybe Type → Maybe Type → Maybe Type
composeMid-pick (just B) _  = just B
composeMid-pick nothing  fb = fb

composeMid : NamedCtx → RawExpr → RawExpr → Type → Maybe Type
composeMid ctx f g A = composeMid-pick (composeArgB ctx g A) (domainOfHead ctx f)

-- | Find a local variable's de Bruijn position and declared quantity.
findLocalVarUsage : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx) × Quantity)
findLocalVarUsage (mkCtx n Γ Δ _ _ _ _) x = go Γ Δ
  where
    go : ∀ {m} → Ctx → SCtx m → Maybe (Fin m × Quantity)
    go [] S∅ = nothing
    go [] (_ S, _ ^ _) = nothing
    go (_ ∷ _) S∅ = nothing
    go {suc m} (b ∷ Γ') (Δ' S, _ ^ q) with Data.String._≟_ x (name b)
    ... | yes _ = just (zero , q)
    ... | no  _ with go Γ' Δ'
    ...   | nothing = nothing
    ...   | just (i , q') = just (suc i , q')
-- | Polymorphic-builtin identifier for the function position of an
-- `RApp`. The elaborator handles each polymorphic builtin specially
-- (separate type-checking rules, separate error paths). Hoisting the
-- dispatch into a classifier + `Maybe PolyBuiltinApp` makes the
-- elaborator's pattern coverage explicit and avoids the neutral-term
-- obstacle with literal-string patterns (analogous to the RVar "unit"
-- refactor).
data PolyBuiltinApp : Set where
  pba-id pba-fst pba-snd pba-terminal : PolyBuiltinApp  -- infer-mode successes
  pba-inl pba-inr pba-initial : PolyBuiltinApp          -- infer-mode rejections
  pba-arr : PolyBuiltinApp                              -- Eff lift, infer mode
  pba-pair-applied : PolyBuiltinApp                     -- `RApp (RVar "pair") _` head, check mode
  pba-compose-applied : PolyBuiltinApp                  -- `RApp (RVar "compose") _` head, check mode
  pba-case-applied : PolyBuiltinApp                     -- `RApp (RVar "case") _` head, check mode (copair)
  pba-curry : PolyBuiltinApp                            -- 1-arg `curry f`, check mode
  pba-apply : PolyBuiltinApp                            -- 1-arg `apply p`, infer / check mode
  pba-In : PolyBuiltinApp                               -- 1-arg `In arg`, check mode (μ intro)
  pba-cata : PolyBuiltinApp                             -- 1-arg `cata alg`, check mode (fold)

-- | Classify an application head. `just <pba>` iff the head is an
-- `RVar` bound to one of the seven polymorphic builtins; `nothing`
-- otherwise, in which case the generic application rule applies.
classifyAppHead : RawExpr → Maybe PolyBuiltinApp
classifyAppHead (Raw.RVar x) with StrProp._≟_ x "id"
... | yes _ = just pba-id
... | no  _ with StrProp._≟_ x "fst"
...   | yes _ = just pba-fst
...   | no  _ with StrProp._≟_ x "snd"
...     | yes _ = just pba-snd
...     | no  _ with StrProp._≟_ x "terminal"
...       | yes _ = just pba-terminal
...       | no  _ with StrProp._≟_ x "inl"
...         | yes _ = just pba-inl
...         | no  _ with StrProp._≟_ x "inr"
...           | yes _ = just pba-inr
...           | no  _ with StrProp._≟_ x "initial"
...             | yes _ = just pba-initial
...             | no  _ with StrProp._≟_ x "arr"
...               | yes _ = just pba-arr
...               | no  _ with StrProp._≟_ x "curry"
...                 | yes _ = just pba-curry
...                 | no  _ with StrProp._≟_ x "apply"
...                   | yes _ = just pba-apply
...                   | no  _ with StrProp._≟_ x "In"
...                     | yes _ = just pba-In
...                     | no  _ with StrProp._≟_ x "cata"
...                       | yes _ = just pba-cata
...                       | no  _ = nothing
-- Applied-form heads: `RApp (RVar "pair" | "compose") _`. Plan 0.6
-- Phase C.7 POC-2 / POC-3.
classifyAppHead (Raw.RApp (Raw.RVar x) _) with StrProp._≟_ x "pair"
... | yes _ = just pba-pair-applied
... | no  _ with StrProp._≟_ x "compose"
...   | yes _ = just pba-compose-applied
...   | no  _ with StrProp._≟_ x "case"
...     | yes _ = just pba-case-applied
...     | no  _ = nothing
-- RApp with non-RVar head: not a builtin reference.
classifyAppHead (Raw.RApp (Raw.RApp _ _) _)         = nothing
classifyAppHead (Raw.RApp (Raw.RQualified _ _) _)   = nothing
classifyAppHead (Raw.RApp (Raw.RResolved _) _)      = nothing
classifyAppHead (Raw.RApp (Raw.RLam _ _) _)         = nothing
classifyAppHead (Raw.RApp (Raw.RLet _ _ _) _)       = nothing
classifyAppHead (Raw.RApp (Raw.RPair _ _) _)        = nothing
classifyAppHead (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) = nothing
classifyAppHead (Raw.RApp Raw.RUnit _)              = nothing
classifyAppHead (Raw.RApp (Raw.RInt _) _)           = nothing
classifyAppHead (Raw.RApp (Raw.RStringLit _) _)     = nothing
classifyAppHead (Raw.RApp (Raw.RAnnot _ _) _)       = nothing
classifyAppHead (Raw.RApp (Raw.RBinOp _ _ _) _)     = nothing
classifyAppHead (Raw.RApp (Raw.RUnaryOp _ _) _)     = nothing
classifyAppHead (Raw.RApp (Raw.RAna _ _) _)         = nothing
-- Non-RApp / non-RVar heads.
classifyAppHead (Raw.RAna _ _)            = nothing
classifyAppHead (Raw.RQualified _ _)      = nothing
classifyAppHead (Raw.RResolved _)         = nothing
classifyAppHead (Raw.RLam _ _)            = nothing
classifyAppHead (Raw.RLet _ _ _)          = nothing
classifyAppHead (Raw.RPair _ _)           = nothing
classifyAppHead (Raw.RDestruct _ _ _ _ _) = nothing
classifyAppHead Raw.RUnit                 = nothing
classifyAppHead (Raw.RInt _)              = nothing
classifyAppHead (Raw.RStringLit _)        = nothing
classifyAppHead (Raw.RAnnot _ _)          = nothing
classifyAppHead (Raw.RBinOp _ _ _)        = nothing
classifyAppHead (Raw.RUnaryOp _ _)        = nothing

-- | View-type classification of an application head. Each constructor
-- fixes the head's concrete RawExpr shape via an index, so pattern-
-- matching on an `AppHeadView f` value makes `f`'s shape available
-- in the goal structurally — no `with`-abstraction interplay. This
-- is the "eliminate opaque `with`-helpers by refactoring the
-- definition" idiom (see `docs/formal/historical/lessons-learned.md`):
-- when a proof is fighting `rewrite` against an internal `with`-
-- dispatch, the fix is to refactor the function to return a datatype
-- carrying the proof, not to layer more proof tactics.
data AppHeadView : RawExpr → Set where
  ahv-id       : AppHeadView (Raw.RVar "id")
  ahv-fst      : AppHeadView (Raw.RVar "fst")
  ahv-snd      : AppHeadView (Raw.RVar "snd")
  ahv-terminal : AppHeadView (Raw.RVar "terminal")
  ahv-inl      : AppHeadView (Raw.RVar "inl")
  ahv-inr      : AppHeadView (Raw.RVar "inr")
  ahv-initial  : AppHeadView (Raw.RVar "initial")
  ahv-arr      : AppHeadView (Raw.RVar "arr")
  ahv-curry    : AppHeadView (Raw.RVar "curry")
  ahv-apply    : AppHeadView (Raw.RVar "apply")
  ahv-In       : AppHeadView (Raw.RVar "In")
  ahv-cata     : AppHeadView (Raw.RVar "cata")
  ahv-pair-applied    : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RVar "pair") f')
  ahv-compose-applied : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RVar "compose") f')
  ahv-case-applied    : ∀ {f'} → AppHeadView (Raw.RApp (Raw.RVar "case") f')
  ahv-other    : ∀ {f} → AppHeadView f

classifyAppHeadView : (f : RawExpr) → AppHeadView f
classifyAppHeadView (Raw.RVar x) with StrProp._≟_ x "id"
... | yes refl = ahv-id
... | no  _ with StrProp._≟_ x "fst"
...   | yes refl = ahv-fst
...   | no  _ with StrProp._≟_ x "snd"
...     | yes refl = ahv-snd
...     | no  _ with StrProp._≟_ x "terminal"
...       | yes refl = ahv-terminal
...       | no  _ with StrProp._≟_ x "inl"
...         | yes refl = ahv-inl
...         | no  _ with StrProp._≟_ x "inr"
...           | yes refl = ahv-inr
...           | no  _ with StrProp._≟_ x "initial"
...             | yes refl = ahv-initial
...             | no  _ with StrProp._≟_ x "arr"
...               | yes refl = ahv-arr
...               | no  _ with StrProp._≟_ x "curry"
...                 | yes refl = ahv-curry
...                 | no  _ with StrProp._≟_ x "apply"
...                   | yes refl = ahv-apply
...                   | no  _ with StrProp._≟_ x "In"
...                     | yes refl = ahv-In
...                     | no  _ with StrProp._≟_ x "cata"
...                       | yes refl = ahv-cata
...                       | no  _ = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RVar x) _) with StrProp._≟_ x "pair"
... | yes refl = ahv-pair-applied
... | no  _    with StrProp._≟_ x "compose"
...   | yes refl = ahv-compose-applied
...   | no  _    with StrProp._≟_ x "case"
...     | yes refl = ahv-case-applied
...     | no  _    = ahv-other
-- RApp with non-RVar head: ahv-other.
classifyAppHeadView (Raw.RApp (Raw.RApp _ _) _)         = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RQualified _ _) _)   = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RResolved _) _)      = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RLam _ _) _)         = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RLet _ _ _) _)       = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RPair _ _) _)        = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RDestruct _ _ _ _ _) _) = ahv-other
classifyAppHeadView (Raw.RApp Raw.RUnit _)              = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RInt _) _)           = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RStringLit _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RAnnot _ _) _)       = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RBinOp _ _ _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RUnaryOp _ _) _)     = ahv-other
classifyAppHeadView (Raw.RApp (Raw.RAna _ _) _)         = ahv-other
classifyAppHeadView (Raw.RAna _ _)            = ahv-other
classifyAppHeadView (Raw.RQualified _ _)      = ahv-other
classifyAppHeadView (Raw.RResolved _)         = ahv-other
classifyAppHeadView (Raw.RLam _ _)            = ahv-other
classifyAppHeadView (Raw.RLet _ _ _)          = ahv-other
classifyAppHeadView (Raw.RPair _ _)           = ahv-other
classifyAppHeadView (Raw.RDestruct _ _ _ _ _) = ahv-other
classifyAppHeadView Raw.RUnit                 = ahv-other
classifyAppHeadView (Raw.RInt _)              = ahv-other
classifyAppHeadView (Raw.RStringLit _)        = ahv-other
classifyAppHeadView (Raw.RAnnot _ _)          = ahv-other
classifyAppHeadView (Raw.RBinOp _ _ _)        = ahv-other
classifyAppHeadView (Raw.RUnaryOp _ _)        = ahv-other

-- | Compat: `classifyAppHead f ≡ nothing` ⇔ `classifyAppHeadView f ≡
-- ahv-other`. Needed because existing downstream proofs (Judgment's
-- t-app premise, Soundness's sound-RApp-generic, etc.) use
-- `classifyAppHead`'s `Maybe`-return form, while the view enables
-- new proofs (`checkElab-fallback-RApp-generic` below).
classifyAppHead-nothing⇒view-other :
  ∀ {f} → classifyAppHead f ≡ nothing → classifyAppHeadView f ≡ ahv-other
-- Non-RVar heads: both classifyAppHead and classifyAppHeadView
-- reduce definitionally to their respective nothing / ahv-other.
-- Plan 0.6 Phase C.7 POC-2: the RApp case now has a nested match
-- on `RApp (RVar "pair") _`. Split: if head is `RVar "pair"`,
-- classifyAppHead returns `just pba-pair-applied` (so the premise
-- `≡ nothing` is impossible); otherwise uniform `refl`.
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar s) _} p with StrProp._≟_ s "pair"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar s) _} p | no _ with StrProp._≟_ s "compose"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar s) _} p | no _ | no _ with StrProp._≟_ s "case"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RVar _) _} _ | no _ | no _ | no _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RApp _ _) _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RQualified _ _) _} _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RResolved _) _}    _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RLam _ _) _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RLet _ _ _) _}     _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RPair _ _) _}      _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RDestruct _ _ _ _ _) _} _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp Raw.RUnit _}            _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RInt _) _}         _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RStringLit _) _}   _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RAnnot _ _) _}     _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RBinOp _ _ _) _}   _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RUnaryOp _ _) _}   _ = refl
classifyAppHead-nothing⇒view-other {Raw.RApp (Raw.RAna _ _) _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RQualified _ _}     _ = refl
classifyAppHead-nothing⇒view-other {Raw.RResolved _}        _ = refl
classifyAppHead-nothing⇒view-other {Raw.RLam _ _}           _ = refl
classifyAppHead-nothing⇒view-other {Raw.RLet _ _ _}         _ = refl
classifyAppHead-nothing⇒view-other {Raw.RPair _ _}          _ = refl
classifyAppHead-nothing⇒view-other {Raw.RDestruct _ _ _ _ _} _ = refl
classifyAppHead-nothing⇒view-other {Raw.RUnit}              _ = refl
classifyAppHead-nothing⇒view-other {Raw.RInt _}             _ = refl
classifyAppHead-nothing⇒view-other {Raw.RStringLit _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RAnnot _ _}         _ = refl
classifyAppHead-nothing⇒view-other {Raw.RBinOp _ _ _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RUnaryOp _ _}       _ = refl
classifyAppHead-nothing⇒view-other {Raw.RAna _ _}           _ = refl
-- RVar: both dispatches walk the same 7-string chain; show the
-- result alignment case-by-case.
classifyAppHead-nothing⇒view-other {Raw.RVar s} p with StrProp._≟_ s "id"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _
  with StrProp._≟_ s "fst"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _
  with StrProp._≟_ s "snd"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _
  with StrProp._≟_ s "terminal"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _
  with StrProp._≟_ s "inl"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "inr"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "initial"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "arr"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "curry"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "apply"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "In"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "cata"
... | yes _ with p
...   | ()
classifyAppHead-nothing⇒view-other {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = refl

-- Reverse bridge (Plan 0.4 T0 Option A): from view ≡ ahv-other to
-- classifyAppHead ≡ nothing. Needed by `infer-sound`'s ahv-other
-- branch to feed `sound-RApp-generic`'s `notPoly` premise (which
-- types `t-app` / `t-effApp`).
view-other⇒classifyAppHead-nothing :
  ∀ {f} → classifyAppHeadView f ≡ ahv-other → classifyAppHead f ≡ nothing
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RVar s) _} p with StrProp._≟_ s "pair"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RVar s) _} p | no _ with StrProp._≟_ s "compose"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RVar s) _} p | no _ | no _ with StrProp._≟_ s "case"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RVar _) _} _ | no _ | no _ | no _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RApp _ _) _}       _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RQualified _ _) _} _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RResolved _) _}    _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RLam _ _) _}       _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RLet _ _ _) _}     _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RPair _ _) _}      _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RDestruct _ _ _ _ _) _} _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp Raw.RUnit _}            _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RInt _) _}         _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RStringLit _) _}   _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RAnnot _ _) _}     _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RBinOp _ _ _) _}   _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RUnaryOp _ _) _}   _ = refl
view-other⇒classifyAppHead-nothing {Raw.RApp (Raw.RAna _ _) _}       _ = refl
view-other⇒classifyAppHead-nothing {Raw.RQualified _ _}     _ = refl
view-other⇒classifyAppHead-nothing {Raw.RResolved _}        _ = refl
view-other⇒classifyAppHead-nothing {Raw.RLam _ _}           _ = refl
view-other⇒classifyAppHead-nothing {Raw.RLet _ _ _}         _ = refl
view-other⇒classifyAppHead-nothing {Raw.RPair _ _}          _ = refl
view-other⇒classifyAppHead-nothing {Raw.RDestruct _ _ _ _ _} _ = refl
view-other⇒classifyAppHead-nothing {Raw.RUnit}              _ = refl
view-other⇒classifyAppHead-nothing {Raw.RInt _}             _ = refl
view-other⇒classifyAppHead-nothing {Raw.RStringLit _}       _ = refl
view-other⇒classifyAppHead-nothing {Raw.RAnnot _ _}         _ = refl
view-other⇒classifyAppHead-nothing {Raw.RBinOp _ _ _}       _ = refl
view-other⇒classifyAppHead-nothing {Raw.RUnaryOp _ _}       _ = refl
view-other⇒classifyAppHead-nothing {Raw.RAna _ _}           _ = refl
view-other⇒classifyAppHead-nothing {Raw.RVar s} p with StrProp._≟_ s "id"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _
  with StrProp._≟_ s "fst"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _
  with StrProp._≟_ s "snd"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _
  with StrProp._≟_ s "terminal"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _
  with StrProp._≟_ s "inl"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "inr"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "initial"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "arr"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "curry"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "apply"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "In"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _
  with StrProp._≟_ s "cata"
... | yes refl with p
...   | ()
view-other⇒classifyAppHead-nothing {Raw.RVar s} p | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ | no _ = refl
data BareBuiltinClass : String → Set where
  bbc-id       : BareBuiltinClass "id"
  bbc-fst      : BareBuiltinClass "fst"
  bbc-snd      : BareBuiltinClass "snd"
  bbc-terminal : BareBuiltinClass "terminal"
  bbc-initial  : BareBuiltinClass "initial"
  bbc-inl      : BareBuiltinClass "inl"
  bbc-inr      : BareBuiltinClass "inr"
  bbc-arr      : BareBuiltinClass "arr"
  bbc-other    : ∀ {x} → BareBuiltinClass x

classifyBareBuiltin : (x : String) → BareBuiltinClass x
classifyBareBuiltin x with StrProp._≟_ x "id"
... | yes refl = bbc-id
... | no  _ with StrProp._≟_ x "fst"
...   | yes refl = bbc-fst
...   | no  _ with StrProp._≟_ x "snd"
...     | yes refl = bbc-snd
...     | no  _ with StrProp._≟_ x "terminal"
...       | yes refl = bbc-terminal
...       | no  _ with StrProp._≟_ x "initial"
...         | yes refl = bbc-initial
...         | no  _ with StrProp._≟_ x "inl"
...           | yes refl = bbc-inl
...           | no  _ with StrProp._≟_ x "inr"
...             | yes refl = bbc-inr
...             | no  _ with StrProp._≟_ x "arr"
...               | yes refl = bbc-arr
...               | no  _ = bbc-other

-- Bundle for AppHeadView: pairs the view with its defining equation.
-- Lets callers recover a term-level witness `classifyAppHeadView f ≡ v`
-- after a `with`-match — used to feed the reverse bridge
-- `view-other⇒classifyAppHead-nothing`.
ViewBundle : RawExpr → Set
ViewBundle f =
  ∃-syntax (λ v → classifyAppHeadView f ≡ v)

viewBundle : (f : RawExpr) → ViewBundle f
viewBundle f = classifyAppHeadView f , refl
