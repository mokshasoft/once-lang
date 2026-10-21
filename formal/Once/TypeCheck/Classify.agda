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
--   * `Once.Internal.Typing`  imports `Classify` (no longer
--     `Elaborate`).
--   * `Once.TypeCheck.Elaborate` imports `Classify` and re-exports
--     it `public` for backward compatibility, then imports
--     `Judgment` (the cycle being broken makes this admissible).
--
-- Contents are unchanged from their previous location in
-- `Elaborate.agda`; only the host module has changed.
------------------------------------------------------------------------

module Once.TypeCheck.Classify where

open import Once.Internal.Typing.Scope

open import Data.String using (String; _++_)
open import Data.String.Properties as StrProp using (_≟_)
open import Agda.Builtin.Equality.Erase using (primEraseEquality)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.Definitions using (DecidableEquality)
import Data.String
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Product using (_×_; _,_; ∃-syntax; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import Once.Spec.Grade
open import Once.Type.Grade
open import Once.Internal.Type
open import Once.Internal.Type.Poly
open import Once.Type
open import Once.Internal.Syntax using (RawExpr)
open import Once.Internal.Syntax as Raw
open import Once.TypeCheck.Raw as Raw
open import Once.Spec.Name using (CanonicalName; canonical; gen; NotGenerator)
open import Once.Spec.Name using (generatorNS)
open import Once.CanonicalName using (gen-inj)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Once.Internal.Typing.Scope using (Ctx)
open import Once.TypeCheck.Context using (∅)
open Once.Internal.Typing.Scope.Binding using (name)
-- Plan 0.58 (OCP-0006): import the IR-FREE `Once.Surface.Context` (not
-- `Surface.Syntax`, which carries `Once.IR` via `Expr`). `lookupLocal` now
-- returns the de-Bruijn `Fin` index (not a `var i` `SExpr`), so `Classify` —
-- and hence `NamedCtx`/the typing judgment — is IR-free.
open import Once.Internal.Context as Surface using () renaming (Ctx to SCtx; ∅ to S∅; _,_ to _S,_; _,_^_ to _S,_^_)

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Named Context with de Bruijn Correspondence
------------------------------------------------------------------------

emptyImports : Imports
emptyImports = []

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

-- | The converse: a plain lookup's entry is found by the prefix lookup too.
lookupPoly⇒lookupPolyPrefix : ∀ (p : PolyCtx) (x : String) {s body}
  → lookupPoly p x ≡ just (s , body)
  → Σ PolyCtx (λ prefix → lookupPolyPrefix p x ≡ just (s , body , prefix))
lookupPoly⇒lookupPolyPrefix [] x ()
lookupPoly⇒lookupPolyPrefix ((n , s' , b') ∷ rest) x lp with StrProp._≟_ n x
... | yes _ = aux lp
  where
    aux : ∀ {s body} → just (s' , b') ≡ just (s , body)
        → Σ PolyCtx (λ prefix → just (s' , b' , rest) ≡ just (s , body , prefix))
    aux refl = rest , refl
... | no  _ = lookupPoly⇒lookupPolyPrefix rest x lp

-- | Empty context
emptyCtx : NamedCtx
emptyCtx = mkCtx 0 ∅ S∅ emptyImports emptyPolyCtx emptyImports

-- | D274: what is in scope at the top level, outside the telescope: the
-- program's signature Σ (its FFI declarations, generators) and its monomorphic
-- definitions — kept apart, as `NamedCtx` keeps them.
record TopCtx : Set where
  constructor topCtx
  field
    tsig  : Imports
    tdefs : Imports

emptyTopCtx : TopCtx
emptyTopCtx = topCtx emptyImports emptyImports

-- | Create a top-level context with polymorphic defs. Plan 0.6.2.
ctxWithImportsAndPolys : TopCtx → PolyCtx → NamedCtx
ctxWithImportsAndPolys tc polys = mkCtx 0 ∅ S∅ (TopCtx.tdefs tc) polys (TopCtx.tsig tc)

------------------------------------------------------------------------
-- Variable Lookup with Weakening and Instantiation
------------------------------------------------------------------------

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

-- | Find a local variable's de Bruijn position and declared quantity.
findLocalVarUsage : (ctx : NamedCtx) → String → Maybe (Fin (NamedCtx.size ctx) × Quantity)
findLocalVarUsage (mkCtx n Γ Δ _ _ _) x = go Γ Δ
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
... | ahv-ana             | ()
... | ahv-Out             | ()
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

-- D136: the BARE-name view, on the CANONICAL name. This replaces
-- `BareBuiltinClass`/`classifyBareBuiltin`, which dispatched on a bare
-- string and so could not tell the generator `fst` from a user's. After the
-- resolver runs, a generator IS `RResolved (gen g)` and nothing else is, so
-- this view is exact rather than a guess.
data GenView : CanonicalName → Set where
  gv-id       : GenView (gen "id")
  gv-fst      : GenView (gen "fst")
  gv-snd      : GenView (gen "snd")
  gv-terminal : GenView (gen "terminal")
  gv-initial  : GenView (gen "initial")
  gv-inl      : GenView (gen "inl")
  gv-inr      : GenView (gen "inr")
  gv-unit     : GenView (gen "unit")
  -- D134/D136: `gv-other` CARRIES the property it decides. Without this the
  -- constructor is uninformative (`∀ {cn}`), so the elaborator's own dispatch
  -- could not discharge `t-var-resolved`'s side condition — the analogue of
  -- `isGround-inj₂-¬Ground`, which works only because `inj₂` is informative.
  gv-other  : ∀ {cn} → NotGenerator cn → GenView cn

-- A two-component name whose namespace is NOT `Generators` is no generator:
-- one `refl`-match recovers the namespace, so a single polymorphic refutation
-- fills all eight slots.
notGen-ns : ∀ {ns g} → ¬ (ns ≡ generatorNS) → NotGenerator (canonical (ns ∷ g ∷ []))
notGen-ns {ns} {g} ¬ns = f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ []ᴬ
  where
    f : ∀ {h} → canonical (ns ∷ g ∷ []) ≢ gen h
    f refl = ¬ns refl

-- Any other component count is disjoint from `gen _` by LENGTH.
notGen-shape : ∀ {ps} → (∀ {h : String} → canonical ps ≢ gen h) → NotGenerator (canonical ps)
notGen-shape f = f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ f ∷ᴬ []ᴬ

classifyGen : (cn : CanonicalName) → GenView cn
classifyGen (canonical (ns ∷ g ∷ [])) with ns ≟ₛ generatorNS
... | no ¬ns = gv-other (notGen-ns ¬ns)
... | yes refl with g ≟ₛ "id"
...   | yes refl = gv-id
...   | no  ¬id with g ≟ₛ "fst"
...     | yes refl = gv-fst
...     | no  ¬fs with g ≟ₛ "snd"
...       | yes refl = gv-snd
...       | no  ¬sn with g ≟ₛ "terminal"
...         | yes refl = gv-terminal
...         | no  ¬te with g ≟ₛ "initial"
...           | yes refl = gv-initial
...           | no  ¬in with g ≟ₛ "inl"
...             | yes refl = gv-inl
...             | no  ¬il with g ≟ₛ "inr"
...               | yes refl = gv-inr
...               | no  ¬ir with g ≟ₛ "unit"
...                 | yes refl = gv-unit
...                 | no  ¬un = gv-other
                                 ( (λ e → ¬id (gen-inj e))
                                 ∷ᴬ (λ e → ¬fs (gen-inj e))
                                 ∷ᴬ (λ e → ¬sn (gen-inj e))
                                 ∷ᴬ (λ e → ¬te (gen-inj e))
                                 ∷ᴬ (λ e → ¬in (gen-inj e))
                                 ∷ᴬ (λ e → ¬il (gen-inj e))
                                 ∷ᴬ (λ e → ¬ir (gen-inj e))
                                 ∷ᴬ (λ e → ¬un (gen-inj e))
                                 ∷ᴬ []ᴬ )
classifyGen (canonical [])              = gv-other (notGen-shape λ ())
classifyGen (canonical (_ ∷ []))        = gv-other (notGen-shape λ ())
classifyGen (canonical (_ ∷ _ ∷ _ ∷ _)) = gv-other (notGen-shape λ ())

-- D136: `BareBuiltinClass` / `classifyBareBuiltin` are DELETED. They asked
-- "does this bare STRING name a generator?" — the collision this plan removes.
-- A generator is `RResolved (gen g)` and is classified by `GenView` above; a
-- bare name is a lexical binder or an ordinary reference, and asking the old
-- question of it was actively WRONG: it rejected a user's own polymorphic `id`
-- (which D136 allows) and would have read a generator off a shadowing binder.

-- Bundle for AppHeadView: pairs the view with its defining equation.
-- Lets callers recover a term-level witness `classifyAppHeadView f ≡ v`
-- after a `with`-match — used to feed the reverse bridge
-- `view-other⇒classifyAppHead-nothing`.
ViewBundle : RawExpr → Set
ViewBundle f =
  ∃-syntax (λ v → classifyAppHeadView f ≡ v)

viewBundle : (f : RawExpr) → ViewBundle f
viewBundle f = classifyAppHeadView f , refl
