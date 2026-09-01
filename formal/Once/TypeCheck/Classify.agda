-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
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
-- Plan 0.58 (OCP-0006): import the IR-FREE `Once.Surface.Context` (not
-- `Surface.Syntax`, which carries `Once.IR` via `Expr`). `lookupLocal` now
-- returns the de-Bruijn `Fin` index (not a `var i` `SExpr`), so `Classify` —
-- and hence `NamedCtx`/the typing judgment — is IR-free.
open import Once.Surface.Context as Surface using ()
  renaming (Ctx to SCtx; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)

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

-- | Plan 0.58 (telescope redesign): look up a poly def AND return its
-- PREFIX (the tail after the matched entry). The `PolyCtx` is now read as
-- an ORDERED telescope — head = most-recently-declared def, tail = the
-- definitions it is allowed to reference (its prefix). A def's body is
-- typed in that prefix, so a reference can only reach EARLIER defs:
-- acyclicity is manifest in the structure (no `removePoly`), and because
-- the returned prefix is a structural sub-list, the elaborator's inline
-- reference resolution terminates structurally (POC-A) with no `Acc`.
-- (The topological sort at the module boundary — Plan 0.58 T3 — arranges
-- the defs so this order is a valid dependency order; a cycle is rejected.)
lookupPolyPrefix : PolyCtx → String → Maybe (PolyType × RawExpr × PolyCtx)
lookupPolyPrefix [] _ = nothing
lookupPolyPrefix ((n , s , b) ∷ rest) x with StrProp._≟_ n x
... | yes _ = just (s , b , rest)
... | no  _ = lookupPolyPrefix rest x

-- | The returned prefix is STRICTLY shorter than the input telescope —
-- the well-founded measure for the elaborator's inline reference
-- resolution (Plan 0.58 E1: `checkElab` re-elaborates a def's body in
-- its prefix, terminating because the prefix strictly shrinks).
lookupPolyPrefix-decreases :
  ∀ (x : String) (polys : PolyCtx) {s : PolyType} {b : RawExpr} {prefix : PolyCtx}
  → lookupPolyPrefix polys x ≡ just (s , b , prefix)
  → length prefix < length polys
lookupPolyPrefix-decreases x [] ()
lookupPolyPrefix-decreases x ((n , s' , b') ∷ rest) eq with StrProp._≟_ n x
... | yes _ = aux eq
  where
    aux : ∀ {s b prefix} → just (s' , b' , rest) ≡ just (s , b , prefix)
        → length prefix < length ((n , s' , b') ∷ rest)
    aux refl = ≤-refl
... | no  _ = m≤n⇒m≤1+n (lookupPolyPrefix-decreases x rest eq)

-- | `lookupPolyPrefix` and `lookupPoly` find the SAME entry (same head-first
-- search) — so a prefix lookup yields the corresponding plain lookup. Lets the
-- canon/preserve proofs reuse their `lookupPoly`-based `PolyInB` witnesses.
lookupPolyPrefix⇒lookupPoly : ∀ (p : PolyCtx) (x : String) {s body prefix}
  → lookupPolyPrefix p x ≡ just (s , body , prefix) → lookupPoly p x ≡ just (s , body)
lookupPolyPrefix⇒lookupPoly [] x ()
lookupPolyPrefix⇒lookupPoly ((n , s' , b') ∷ rest) x lp with StrProp._≟_ n x
... | yes _ = aux lp
  where
    aux : ∀ {s body prefix} → just (s' , b' , rest) ≡ just (s , body , prefix)
        → just (s' , b') ≡ just (s , body)
    aux refl = refl
... | no  _ = lookupPolyPrefix⇒lookupPoly rest x lp

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
               → Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar Δ' Ψ A))
lookupLocal-go x [] S∅ = nothing
lookupLocal-go x [] (_ S, _ ^ _) = nothing
lookupLocal-go x (_ ∷ _) S∅ = nothing
lookupLocal-go {m = suc m'} x (b ∷ Γ') (Δ' S, B ^ _) with Data.String._≟_ x (name b)
... | yes _ = just (_ , _ , Surface.svar zero)
... | no _  with lookupLocal-go x Γ' Δ'
...   | nothing = nothing
...   | just (A , Ψ , Surface.svar i) = just (_ , _ , Surface.svar (suc i))

lookupLocal : (ctx : NamedCtx) → String
            → Maybe (∃[ A ] ∃[ Ψ ] (Surface.SVar (NamedCtx.debruijn ctx) Ψ A))
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
  llv-found : ∀ {A Ψ eV} → lookupLocal ctx x ≡ just (A , Ψ , eV) → LookupLocalView ctx x
  llv-not-found : lookupLocal ctx x ≡ nothing → LookupLocalView ctx x

inspectLookupLocal : (ctx : NamedCtx) (x : String) → LookupLocalView ctx x
inspectLookupLocal ctx x with lookupLocal ctx x in eq
... | just (A , Ψ , eV) = llv-found eq
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
-- User poly name / named morphism: look up schema (poly) or fall back to the
-- monomorphic named-def type (`imports`) and read off its codomain. SHARED by the
-- bare `RVar` general case AND the resolved `RResolved` case (keyed by
-- `showCanonical cn`) — so the two coincide DEFINITIONALLY (needed by
-- `CanonComposeMid.composeArgB-RVar-resolved`).
composeArgB-lookup : NamedCtx → String → Type → Maybe Type
composeArgB-lookup ctx name A with lookupPoly (NamedCtx.polys ctx) name
... | just (schema , _) = schemaArrowCodomain schema A
... | nothing with lookupImport (NamedCtx.imports ctx) name
...   | just (_ Once.Type.⇒[ _ ] C) = just C
...   | _ = nothing

-- fst/snd : recover the matching projection's codomain when A is a product, else
-- fall through to the lookup path (a user `fst`/`snd` shadow).
composeArgB-fst : NamedCtx → Type → Maybe Type
composeArgB-fst ctx (X * _) = just X
composeArgB-fst ctx A       = composeArgB-lookup ctx "fst" A

composeArgB-snd : NamedCtx → Type → Maybe Type
composeArgB-snd ctx (_ * Y) = just Y
composeArgB-snd ctx A       = composeArgB-lookup ctx "snd" A

-- RVar dispatch via explicit `≟` (not literal patterns) so the builtins are
-- distinguished from an ABSTRACT name in proofs (the literal-pattern opacity fix).
composeArgB-rvar : NamedCtx → String → Type → Maybe Type
composeArgB-rvar ctx name A with name ≟ "fst"
... | yes _ = composeArgB-fst ctx A
... | no  _ with name ≟ "snd"
...   | yes _ = composeArgB-snd ctx A
...   | no  _ with name ≟ "id"
...     | yes _ = just A
...     | no  _ with name ≟ "terminal"
...       | yes _ = just Unit
...       | no  _ = composeArgB-lookup ctx name A

composeArgB : NamedCtx → RawExpr → Type → Maybe Type
composeArgB ctx (Raw.RVar name) A   = composeArgB-rvar ctx name A
composeArgB ctx (Raw.RResolved cn) A = composeArgB-lookup ctx (showCanonical cn) A
-- Nested compose: recurse. The head is dispatched by an explicit `≟` rather
-- than a literal pattern, for the SAME reason `composeArgB-rvar` above is —
-- a literal pattern is stuck on an ABSTRACT head name, so a proof that only
-- knows `name ≢ "compose"` could not reduce this clause. Behaviour is
-- unchanged: every non-`compose` head still falls to `nothing`.
composeArgB ctx (Raw.RApp (Raw.RApp (Raw.RVar name) f') g') A with name ≟ "compose"
... | no _ = nothing
... | yes _ with composeArgB ctx g' A
...   | nothing = nothing
...   | just B' with composeArgB ctx f' B'
...     | nothing = nothing
...     | just C  = just C
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
-- Read a domain off an import-table lookup (shared by the bare `RVar` and the
-- canonicalized `RResolved` heads so the two coincide DEFINITIONALLY — needed by
-- `CanonComposeMid.domainOfHead-canon`; behaviour is identical to the old inline
-- `with`-blocks).
domainOfHead-arrow : Maybe Type → Maybe Type
domainOfHead-arrow (just (D Once.Type.⇒[ _ ] _)) = just D
domainOfHead-arrow _ = nothing

domainOfHead : NamedCtx → RawExpr → Maybe Type
domainOfHead ctx (Raw.RVar name) = domainOfHead-arrow (lookupImport (NamedCtx.imports ctx) name)
-- Plan 0.50 Stage 3: a RESOLVED canonical name behaves like its bare form (the
-- import table is keyed by `showCanonical cn`), so point-free composes survive
-- the resolver's `RVar → RResolved` canonicalization.
domainOfHead ctx (Raw.RResolved cn) = domainOfHead-arrow (lookupImport (NamedCtx.imports ctx) (showCanonical cn))
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
  pba-pair-applied : PolyBuiltinApp                     -- `RApp (RVar "pair") _` head, check mode
  pba-compose-applied : PolyBuiltinApp                  -- `RApp (RVar "compose") _` head, check mode
  pba-case-applied : PolyBuiltinApp                     -- `RApp (RVar "case") _` head, check mode (copair)
  pba-curry : PolyBuiltinApp                            -- 1-arg `curry f`, check mode
  pba-apply : PolyBuiltinApp                            -- 1-arg `apply p`, infer / check mode
  pba-In : PolyBuiltinApp                               -- 1-arg `In arg`, check mode (μ intro)
  pba-cata : PolyBuiltinApp                             -- 1-arg `cata alg`, check mode (fold)

-- | `classifyAppHead` (head → `Maybe PolyBuiltinApp`) is DEFINED BELOW, after
-- `classifyAppHeadView`, as `viewToPba ∘ classifyAppHeadView` — a single source
-- of truth for the string dispatch (OCP-0008 de-withing). The old parallel
-- nested-≟ ladder is retired; the two compat bridges collapse to near-trivial.

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
...             | no  _ with StrProp._≟_ x "curry"
...               | yes refl = ahv-curry
...               | no  _ with StrProp._≟_ x "apply"
...                 | yes refl = ahv-apply
...                 | no  _ with StrProp._≟_ x "In"
...                   | yes refl = ahv-In
...                   | no  _ with StrProp._≟_ x "cata"
...                     | yes refl = ahv-cata
...                     | no  _ = ahv-other
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
classifyAppHeadView (Raw.RApp (Raw.RFloat _ _ _ _) _)     = ahv-other
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
classifyAppHeadView (Raw.RFloat _ _ _ _)        = ahv-other
classifyAppHeadView (Raw.RStringLit _)        = ahv-other
classifyAppHeadView (Raw.RAnnot _ _)          = ahv-other
classifyAppHeadView (Raw.RBinOp _ _ _)        = ahv-other
classifyAppHeadView (Raw.RUnaryOp _ _)        = ahv-other

-- | Map an app-head VIEW to its `Maybe PolyBuiltinApp`. This is the single
-- source of truth linking the view to the `Maybe`-return classifier.
viewToPba : ∀ {f} → AppHeadView f → Maybe PolyBuiltinApp
viewToPba ahv-id              = just pba-id
viewToPba ahv-fst             = just pba-fst
viewToPba ahv-snd             = just pba-snd
viewToPba ahv-terminal        = just pba-terminal
viewToPba ahv-inl             = just pba-inl
viewToPba ahv-inr             = just pba-inr
viewToPba ahv-initial         = just pba-initial
viewToPba ahv-curry           = just pba-curry
viewToPba ahv-apply           = just pba-apply
viewToPba ahv-In              = just pba-In
viewToPba ahv-cata            = just pba-cata
viewToPba ahv-pair-applied    = just pba-pair-applied
viewToPba ahv-compose-applied = just pba-compose-applied
viewToPba ahv-case-applied    = just pba-case-applied
viewToPba ahv-other           = nothing

-- | `classifyAppHead` derived from the view (OCP-0008 single-dispatch). Reduces
-- to exactly the same values as the retired parallel ladder (e.g.
-- `classifyAppHead (RVar "id") = viewToPba ahv-id = just pba-id`).
classifyAppHead : RawExpr → Maybe PolyBuiltinApp
classifyAppHead f = viewToPba (classifyAppHeadView f)

-- | Compat: `classifyAppHead f ≡ nothing` ⇔ `classifyAppHeadView f ≡
-- ahv-other`. Needed because existing downstream proofs (Judgment's
-- t-app premise, Soundness's sound-RApp-generic, etc.) use
-- `classifyAppHead`'s `Maybe`-return form, while the view enables
-- new proofs (`checkElab-fallback-RApp-generic` below).
classifyAppHead-nothing⇒view-other :
  ∀ {f} → classifyAppHead f ≡ nothing → classifyAppHeadView f ≡ ahv-other
-- classifyAppHead = viewToPba ∘ classifyAppHeadView, so case the view: every
-- builtin constructor makes viewToPba ≡ just _ (contradicts p); only ahv-other.
classifyAppHead-nothing⇒view-other {f} p with classifyAppHeadView f | p
... | ahv-id              | ()
... | ahv-fst             | ()
... | ahv-snd             | ()
... | ahv-terminal        | ()
... | ahv-inl             | ()
... | ahv-inr             | ()
... | ahv-initial         | ()
... | ahv-curry           | ()
... | ahv-apply           | ()
... | ahv-In              | ()
... | ahv-cata            | ()
... | ahv-pair-applied    | ()
... | ahv-compose-applied | ()
... | ahv-case-applied    | ()
... | ahv-other           | _  = refl

-- Reverse bridge (Plan 0.4 T0 Option A): from view ≡ ahv-other to
-- classifyAppHead ≡ nothing. Needed by `infer-sound`'s ahv-other
-- branch to feed `sound-RApp-generic`'s `notPoly` premise (which
-- types `t-app` / `t-effApp`).
view-other⇒classifyAppHead-nothing :
  ∀ {f} → classifyAppHeadView f ≡ ahv-other → classifyAppHead f ≡ nothing
-- rewrite the view to ahv-other; classifyAppHead reduces to viewToPba ahv-other = nothing.
view-other⇒classifyAppHead-nothing {f} p rewrite p = refl

data BareBuiltinClass : String → Set where
  bbc-id       : BareBuiltinClass "id"
  bbc-fst      : BareBuiltinClass "fst"
  bbc-snd      : BareBuiltinClass "snd"
  bbc-terminal : BareBuiltinClass "terminal"
  bbc-initial  : BareBuiltinClass "initial"
  bbc-inl      : BareBuiltinClass "inl"
  bbc-inr      : BareBuiltinClass "inr"
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
...             | no  _ = bbc-other

-- Bundle for AppHeadView: pairs the view with its defining equation.
-- Lets callers recover a term-level witness `classifyAppHeadView f ≡ v`
-- after a `with`-match — used to feed the reverse bridge
-- `view-other⇒classifyAppHead-nothing`.
ViewBundle : RawExpr → Set
ViewBundle f =
  ∃-syntax (λ v → classifyAppHeadView f ≡ v)

viewBundle : (f : RawExpr) → ViewBundle f
viewBundle f = classifyAppHeadView f , refl
