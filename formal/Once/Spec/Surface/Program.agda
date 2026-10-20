{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Program — the program a module denotes.
--
--   * Its SIGNATURE Σ: its own `signature` declarations and those of the
--     modules it imports, each a first-order type, named by its module's
--     full path.
--   * Its DEFINITIONS, in declaration order (a telescope: a body sees only the
--     definitions before it): each body checked at its type
--     (`Spec.Surface.Typing`) and elaborated to a core term, typed by the core
--     judgment over its type variables. A definition's type is its body's
--     principal type over its domains (it checks at no strictly smaller type
--     with the same domains); a signature only confirms it (D314, D007).
--     Without a signature, the type is the one the body SYNTHESIZES (D323):
--     the definition decides it alone. A body that only checks — a λ — has
--     no type of its own: its domain is a context, which only a signature
--     declares.
--   * Its ENTRY: the definition named `main`, used at `Eff Unit Unit` (D315,
--     `Spec.Core.Program`).
------------------------------------------------------------------------

module Once.Spec.Surface.Program where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.String using (String)
open import Function using (Injective)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Grade using (Many; mk-kind; pure; act; eff)
open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Type
  using (Ty; Fun; KCtx; ∅ₖ; base; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; K; Id; _⊕_; _⊗_; Occurs; OccursF)
open import Once.Spec.Sub using (_<:ᶜ_)
open import Once.Spec.Signature
  using (BTy; unit; void; int; float; DeclType; constant; value; operation; _∶_; Signature; WellFormed; OneName)
import Once.Spec.Signature as BT
open import Once.Spec.Context using (∅; [])
open import Once.Spec.Core.Syntax using (Defs; []; _▷_; Schema; module Schema; schema; Tm)
open Schema using (arity; kinds; type)
import Once.Spec.Core.Typing as CoreTyping
import Once.Spec.Core.Program as CoreProgram
open import Once.Spec.Surface.Syntax
open import Once.Spec.Surface.Resolution
  using (ModuleMap; FirstAt; Expands; Env; env; aliases; Unaliased; Resolves)
import Once.Spec.Surface.Typing as SurfaceTyping

------------------------------------------------------------------------
-- The signature
------------------------------------------------------------------------

-- A base type as written.
data BaseType : PolyType → BTy → Set where
  bt-unit  : BaseType PUnit unit
  bt-void  : BaseType PVoid void
  bt-int   : BaseType PInt int
  bt-float : BaseType PFloat float
  bt-*     : ∀ {A B a b} → BaseType A a → BaseType B b → BaseType (A P* B) (a BT.* b)
  bt-+     : ∀ {A B a b} → BaseType A a → BaseType B b → BaseType (A P+ B) (a BT.+ b)

-- A `signature` declaration's type: a base type (a constant), a pure arrow
-- between base types (a value), or an `Act` arrow between them (an
-- operation; it is used at `Eff` by subtyping).
data DeclTypeOf : PolyType → DeclType → Set where
  dt-const : ∀ {A a} → BaseType A a → DeclTypeOf A (constant a)
  dt-pure  : ∀ {A B a b q} → BaseType A a → BaseType B b → DeclTypeOf (A P⇒[ q ] B) (value a q b)
  dt-act   : ∀ {A B a b} → BaseType A a → BaseType B b → DeclTypeOf (PAct A B) (operation a Many b)

data NotSignature : Decl → Set where
  ns-tsig   : ∀ {x t}    → NotSignature (DTypeSig x t)
  ns-def    : ∀ {x e}    → NotSignature (DFunDef x e)
  ns-alias  : ∀ {x ps t} → NotSignature (DTypeAlias x ps t)
  ns-import : ∀ {i}      → NotSignature (DImport i)

-- A module's own `signature`s, named under the module's path.
data SignaturesOf (path : List String) : List Decl → Signature → Set where
  so-nil   : SignaturesOf path [] []
  so-sig   : ∀ {x A t ds Σ} → DeclTypeOf A t → SignaturesOf path ds Σ
           → SignaturesOf path (DSignature x A ∷ ds) ((canonical (path ++ (x ∷ [])) ∶ t) ∷ Σ)
  so-other : ∀ {d ds Σ} → NotSignature d → SignaturesOf path ds Σ → SignaturesOf path (d ∷ ds) Σ

data NotImport : Decl → Set where
  ni-sig   : ∀ {x t}    → NotImport (DSignature x t)
  ni-tsig  : ∀ {x t}    → NotImport (DTypeSig x t)
  ni-def   : ∀ {x e}    → NotImport (DFunDef x e)
  ni-alias : ∀ {x ps t} → NotImport (DTypeAlias x ps t)

-- The `signature`s of the modules a module imports.
data Imported (mm : ModuleMap) : List Decl → Signature → Set where
  im-nil    : Imported mm [] []
  im-import : ∀ {p a p′ ds′ ds Σ₁ Σ₂} → FirstAt p (mkModule ds′) mm → Expands p p′
            → SignaturesOf p′ ds′ Σ₁ → Imported mm ds Σ₂
            → Imported mm (DImport (mkImport p a) ∷ ds) (Σ₁ ++ Σ₂)
  im-other  : ∀ {d ds Σ} → NotImport d → Imported mm ds Σ → Imported mm (d ∷ ds) Σ

-- The program's signature: its own, and its imports'.
SignatureOf : ModuleMap → List Decl → Signature → Set
SignatureOf mm ds Σ = Σ[ Σ₀ ∈ Signature ] Σ[ Σᵢ ∈ Signature ]
                        SignaturesOf [] ds Σ₀ × Imported mm ds Σᵢ × Σ ≡ Σ₀ ++ Σᵢ

------------------------------------------------------------------------
-- A type with variables: a schema
------------------------------------------------------------------------

data TypeOf {a} (ns : Fin a → String) : PolyType → Ty a → Set
data FunOf  {a} (ns : Fin a → String) : PolyFunctor → Fun a → Set
data TypeOf {a} ns where
  to-var   : ∀ {x} (i : Fin a) → ns i ≡ x → TypeOf ns (PTVar x) (var i)
  to-unit  : TypeOf ns PUnit Unit
  to-void  : TypeOf ns PVoid Void
  to-int   : TypeOf ns PInt Int
  to-float : TypeOf ns PFloat Float
  to-*     : ∀ {A B A′ B′} → TypeOf ns A A′ → TypeOf ns B B′ → TypeOf ns (A P* B) (A′ * B′)
  to-+     : ∀ {A B A′ B′} → TypeOf ns A A′ → TypeOf ns B B′ → TypeOf ns (A P+ B) (A′ + B′)
  to-⇒     : ∀ {A B A′ B′ q} → TypeOf ns A A′ → TypeOf ns B B′ → TypeOf ns (A P⇒[ q ] B) (A′ ⇒[ mk-kind q pure ] B′)
  to-act   : ∀ {A B A′ B′} → TypeOf ns A A′ → TypeOf ns B B′ → TypeOf ns (PAct A B) (A′ ⇒[ mk-kind Many act ] B′)
  to-eff   : ∀ {A B A′ B′} → TypeOf ns A A′ → TypeOf ns B B′ → TypeOf ns (PEff A B) (A′ ⇒[ mk-kind Many eff ] B′)
  to-μ     : ∀ {F F′} → FunOf ns F F′ → TypeOf ns (Pμ F) (μ F′)
  to-ν     : ∀ {F F′ f} → FunOf ns F F′ → TypeOf ns (Pν F f) (ν F′ f)
data FunOf {a} ns where
  fo-K  : ∀ {A A′} → TypeOf ns A A′ → FunOf ns (PK A) (K A′)
  fo-Id : FunOf ns PId Id
  fo-⊕  : ∀ {F G F′ G′} → FunOf ns F F′ → FunOf ns G G′ → FunOf ns (F P⊕ G) (F′ ⊕ G′)
  fo-⊗  : ∀ {F G F′ G′} → FunOf ns F F′ → FunOf ns G G′ → FunOf ns (F P⊗ G) (F′ ⊗ G′)

-- A variable that occurs under a functor constant, where only a base type may
-- stand.
data UnderK  {a} (i : Fin a) : Ty a → Set
data UnderKF {a} (i : Fin a) : Fun a → Set
data UnderK i where
  uk-*ˡ : ∀ {A B} → UnderK i A → UnderK i (A * B)
  uk-*ʳ : ∀ {A B} → UnderK i B → UnderK i (A * B)
  uk-+ˡ : ∀ {A B} → UnderK i A → UnderK i (A + B)
  uk-+ʳ : ∀ {A B} → UnderK i B → UnderK i (A + B)
  uk-⇒ˡ : ∀ {A k B} → UnderK i A → UnderK i (A ⇒[ k ] B)
  uk-⇒ʳ : ∀ {A k B} → UnderK i B → UnderK i (A ⇒[ k ] B)
  uk-μ  : ∀ {F} → UnderKF i F → UnderK i (μ F)
  uk-ν  : ∀ {F f} → UnderKF i F → UnderK i (ν F f)
data UnderKF {a} i where
  uk-K  : ∀ {A} → Occurs i A → UnderKF i (K A)
  uk-⊕ˡ : ∀ {F G} → UnderKF i F → UnderKF i (F ⊕ G)
  uk-⊕ʳ : ∀ {F G} → UnderKF i G → UnderKF i (F ⊕ G)
  uk-⊗ˡ : ∀ {F G} → UnderKF i F → UnderKF i (F ⊗ G)
  uk-⊗ʳ : ∀ {F G} → UnderKF i G → UnderKF i (F ⊗ G)

-- A written type is the schema `∀ Δ. A`: its distinct variables, each used,
-- and of base kind exactly when it occurs under a functor constant (D238).
record SchemaOf (T : PolyType) (sc : Schema) : Set where
  field
    names    : Fin (arity sc) → String
    distinct : Injective _≡_ _≡_ names
    reads    : TypeOf names T (type sc)
    used     : ∀ i → Occurs i (type sc)
    kinded   : ∀ i → (UnderK i (type sc) → kinds sc i ≡ base) × (kinds sc i ≡ base → UnderK i (type sc))

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

module _ (Σ : Signature) where

  open CoreProgram Σ using (Tele; []; def)

  _∷ⁿ_ : ∀ {s} → CanonicalName → (Fin s → CanonicalName) → Fin (suc s) → CanonicalName
  (c ∷ⁿ nm) zero    = c
  (c ∷ⁿ nm) (suc d) = nm d

  -- A body at a schema: checked, elaborated, and its core term typed.
  record Body {s} (S : Defs s) (nm : Fin s → CanonicalName) (sc : Schema) (e : Expr) : Set where
    field
      term  : Tm S (arity sc) 0
      check : SurfaceTyping._⊢_⇐_↝_ Σ S nm (kinds sc) SurfaceTyping.∅ e (type sc) term
      typed : CoreTyping._⊩_⊢[_]_∷_!_ Σ S (kinds sc) ∅ [] term (type sc) pure

  -- The schema is the body's principal type: it checks at no strictly smaller
  -- type with the same domains. The domains are the schema's annotation (a
  -- body is a morphism out of a given object); minimality over them would ask
  -- for a greatest domain, which need not exist (`Void -> Int` also checks at
  -- `Int -> Int`, while `Int -> Int` and `Unit -> Int` are incomparable).
  Principal : ∀ {s} (S : Defs s) (nm : Fin s → CanonicalName) (sc : Schema) (e : Expr) → Set
  Principal S nm sc e =
    ∀ {A t} → A <:ᶜ type sc
    → SurfaceTyping._⊢_⇐_↝_ Σ S nm (kinds sc) SurfaceTyping.∅ e A t
    → CoreTyping._⊩_⊢[_]_∷_!_ Σ S (kinds sc) ∅ [] t A pure
    → A ≡ type sc

  data NotDefinition : Decl → Set where
    nd-sig    : ∀ {x t}    → NotDefinition (DSignature x t)
    nd-alias  : ∀ {x ps t} → NotDefinition (DTypeAlias x ps t)
    nd-import : ∀ {i}      → NotDefinition (DImport i)

  -- Walking the declarations from `S` (named `nm`, meaning `tl`) to `S′`.
  data Walk {s} (S : Defs s) (nm : Fin s → CanonicalName) (tl : Tele S)
       : List Decl → ∀ {s′} (S′ : Defs s′) → (Fin s′ → CanonicalName) → Tele S′ → Set where
    w-end   : Walk S nm tl [] S nm tl
    w-skip  : ∀ {d ds s′} {S′ : Defs s′} {nm′ tl′}
            → NotDefinition d → Walk S nm tl ds S′ nm′ tl′ → Walk S nm tl (d ∷ ds) S′ nm′ tl′
    -- A definition with a signature: the signature is the body's principal
    -- type.
    w-sig   : ∀ {x T e ds sc s′} {S′ : Defs s′} {nm′ tl′}
            → SchemaOf T sc → (b : Body S nm sc e) → Principal S nm sc e
            → Walk (S ▷ sc) (canonical (x ∷ []) ∷ⁿ nm) (def tl sc (Body.term b) (Body.typed b)) ds S′ nm′ tl′
            → Walk S nm tl (DTypeSig x T ∷ DFunDef x e ∷ ds) S′ nm′ tl′
    -- A definition without one: the type its body synthesizes (no type
    -- variables), which is its principal type.
    w-nosig : ∀ {x e ds A t s′} {S′ : Defs s′} {nm′ tl′}
            → SurfaceTyping._⊢_⇒_↝_ Σ S nm ∅ₖ SurfaceTyping.∅ e A t
            → (typed : CoreTyping._⊩_⊢[_]_∷_!_ Σ S ∅ₖ ∅ [] t A pure)
            → Principal S nm (schema 0 ∅ₖ A) e
            → Walk (S ▷ schema 0 ∅ₖ A) (canonical (x ∷ []) ∷ⁿ nm) (def tl (schema 0 ∅ₖ A) t typed) ds S′ nm′ tl′
            → Walk S nm tl (DFunDef x e ∷ ds) S′ nm′ tl′

------------------------------------------------------------------------
-- The program of a module
------------------------------------------------------------------------

data NotFunDef : Decl → Set where
  nf-sig    : ∀ {x t}    → NotFunDef (DSignature x t)
  nf-tsig   : ∀ {x t}    → NotFunDef (DTypeSig x t)
  nf-alias  : ∀ {x ps t} → NotFunDef (DTypeAlias x ps t)
  nf-import : ∀ {i}      → NotFunDef (DImport i)

-- Every definition's body resolved; the other declarations unchanged.
data ResolvesDecls (E : Env) : List Decl → List Decl → Set where
  rd-nil  : ResolvesDecls E [] []
  rd-def  : ∀ {x e e′ ds ds′} → Resolves E [] e e′ → ResolvesDecls E ds ds′
          → ResolvesDecls E (DFunDef x e ∷ ds) (DFunDef x e′ ∷ ds′)
  rd-other : ∀ {d ds ds′} → NotFunDef d → ResolvesDecls E ds ds′ → ResolvesDecls E (d ∷ ds) (d ∷ ds′)

-- A module, with the other modules of its compilation unit, denotes a
-- program over its signature.
record Denotes (mm : ModuleMap) (m : Module) (Σ : Signature) (p : CoreProgram.Program Σ) : Set where
  open CoreProgram Σ using (Tele; [])
  field
    signature : SignatureOf mm (Module.decls m) Σ
    unaliased : List (String × List String)
    unaliases : Unaliased mm (Module.decls m) unaliased
    resolved  : List Decl
    resolves  : ResolvesDecls (env unaliased (aliases (Module.decls m))) (Module.decls m) resolved
    names     : Fin (CoreProgram.Program.size p) → CanonicalName
    walk      : Walk Σ [] (λ ()) [] resolved (CoreProgram.Program.sig p) names (CoreProgram.Program.defs p)
    distinct  : Injective _≡_ _≡_ names
    -- Every entry has its own name, operations included (D249): an operation
    -- of Σ is declared once, and no definition is named as one.
    sig-distinct : OneName Σ
    def-not-sig  : ∀ d {t} → ¬ ((names d ∶ t) ∈ Σ)
    entry     : names (CoreProgram.Program.main p) ≡ canonical ("main" ∷ [])
