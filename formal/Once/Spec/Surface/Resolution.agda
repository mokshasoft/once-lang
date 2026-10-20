{-# OPTIONS --safe #-}
-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Surface.Resolution — what each written name denotes.
--
-- A name bound by an enclosing λ, `let` or `destruct` is that variable
-- (lexical binders shadow everything). Otherwise a generator's name is the
-- generator (D136); a name exported by an unaliased import is that module's
-- (its full path, the first such import); any other name is the module's own
-- definition. `name@alias` is the aliased module's, `name@this` the module's
-- own. A module path written with the leading shorthand `I` means
-- `Interpretations`.
--
-- The program's entry, `main`, is not a name a definition can refer to
-- (D324): it is where the program starts, not a morphism to compose with, so
-- no definition can run the program again from its start — its only
-- repetition is structured recursion.
--
-- An import contributes the `signature` declarations of the module it names:
-- the operations of the Interpretations the program is compiled against.
------------------------------------------------------------------------

module Once.Spec.Surface.Resolution where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Name using (CanonicalName; canonical; gen; GenWord)
open import Once.Spec.Surface.Syntax

------------------------------------------------------------------------
-- Tables
------------------------------------------------------------------------

-- The first entry with key `x` has value `v`.
data FirstAt {K V : Set} (x : K) (v : V) : List (K × V) → Set where
  fa-here  : ∀ {rest} → FirstAt x v ((x , v) ∷ rest)
  fa-there : ∀ {y w rest} → y ≢ x → FirstAt x v rest → FirstAt x v ((y , w) ∷ rest)

-- No entry has key `x`.
Absent : {K V : Set} → K → List (K × V) → Set
Absent x = All (λ e → proj₁ e ≢ x)

-- The `I` shorthand.
data Expands : List String → List String → Set where
  ex-nil   : Expands [] []
  ex-I     : ∀ {rest} → Expands ("I" ∷ rest) ("Interpretations" ∷ rest)
  ex-other : ∀ {c rest} → c ≢ "I" → Expands (c ∷ rest) (c ∷ rest)

-- The other modules of the compilation unit, by path.
ModuleMap : Set
ModuleMap = List (List String × Module)

-- The names a module exports: its `signature` declarations.
exports : List Decl → List String
exports []                         = []
exports (DSignature x t ∷ ds)      = x ∷ exports ds
exports (DTypeSig _ _ ∷ ds)        = exports ds
exports (DFunDef _ _ ∷ ds)         = exports ds
exports (DTypeAlias _ _ _ ∷ ds)    = exports ds
exports (DImport _ ∷ ds)           = exports ds

-- Aliased imports: alias ↦ path.
aliases : List Decl → List (String × List String)
aliases []                                          = []
aliases (DImport (mkImport p (just a)) ∷ ds)        = (a , p) ∷ aliases ds
aliases (DImport (mkImport p nothing) ∷ ds)         = aliases ds
aliases (DSignature _ _ ∷ ds)                       = aliases ds
aliases (DTypeSig _ _ ∷ ds)                         = aliases ds
aliases (DFunDef _ _ ∷ ds)                          = aliases ds
aliases (DTypeAlias _ _ _ ∷ ds)                     = aliases ds

-- Unaliased imports: each exported name ↦ the importing path.
mapPath : List String → List String → List (String × List String)
mapPath p []       = []
mapPath p (x ∷ xs) = (x , p) ∷ mapPath p xs

data NotUnaliasedImport : Decl → Set where
  nu-aliased : ∀ {p a}    → NotUnaliasedImport (DImport (mkImport p (just a)))
  nu-sig     : ∀ {x t}    → NotUnaliasedImport (DSignature x t)
  nu-tsig    : ∀ {x t}    → NotUnaliasedImport (DTypeSig x t)
  nu-def     : ∀ {x e}    → NotUnaliasedImport (DFunDef x e)
  nu-alias   : ∀ {x ps t} → NotUnaliasedImport (DTypeAlias x ps t)

data Unaliased (mm : ModuleMap) : List Decl → List (String × List String) → Set where
  un-nil    : Unaliased mm [] []
  un-import : ∀ {p ds′ ds um} → FirstAt p (mkModule ds′) mm → Unaliased mm ds um
            → Unaliased mm (DImport (mkImport p nothing) ∷ ds) (mapPath p (exports ds′) ++ um)
  un-other  : ∀ {d ds um} → NotUnaliasedImport d → Unaliased mm ds um → Unaliased mm (d ∷ ds) um

------------------------------------------------------------------------
-- Names in expressions
------------------------------------------------------------------------

record Env : Set where
  constructor env
  field
    unaliased : List (String × List String)   -- name ↦ path, from unaliased imports
    aliased   : List (String × List String)   -- alias ↦ path

-- A written name, not bound locally.
data ResolvesName (E : Env) : String → Expr → Set where
  rn-gen    : ∀ {x} → GenWord x → ResolvesName E x (RResolved (gen x))
  rn-import : ∀ {x p p′} → ¬ GenWord x → FirstAt x p (Env.unaliased E) → Expands p p′
            → ResolvesName E x (RResolved (canonical (p′ ++ (x ∷ []))))
  rn-own    : ∀ {x} → ¬ GenWord x → Absent x (Env.unaliased E) → x ≢ "main"
            → ResolvesName E x (RResolved (canonical (x ∷ [])))

-- An expression, under the locally bound names `bound`.
data Resolves (E : Env) (bound : List String) : Expr → Expr → Set where
  r-local : ∀ {x} → x ∈ bound → Resolves E bound (RVar x) (RVar x)
  r-name  : ∀ {x e} → ¬ (x ∈ bound) → ResolvesName E x e → Resolves E bound (RVar x) e
  r-this  : ∀ {x} → x ≢ "main" → Resolves E bound (RQualified x "this") (RResolved (canonical (x ∷ [])))
  r-qual  : ∀ {x a p p′} → a ≢ "this" → FirstAt a p (Env.aliased E) → Expands p p′
          → Resolves E bound (RQualified x a) (RResolved (canonical (p′ ++ (x ∷ []))))
  -- An alias that names no import is read as a path of one component.
  r-qual-path : ∀ {x a} → a ≢ "this" → Absent a (Env.aliased E)
              → Resolves E bound (RQualified x a) (RResolved (canonical (a ∷ x ∷ [])))
  r-res   : ∀ {c} → Resolves E bound (RResolved c) (RResolved c)
  r-app   : ∀ {f f′ a a′} → Resolves E bound f f′ → Resolves E bound a a′
          → Resolves E bound (RApp f a) (RApp f′ a′)
  r-lam   : ∀ {x b b′} → Resolves E (x ∷ bound) b b′ → Resolves E bound (RLam x b) (RLam x b′)
  r-let   : ∀ {x e e′ b b′} → Resolves E bound e e′ → Resolves E (x ∷ bound) b b′
          → Resolves E bound (RLet x e b) (RLet x e′ b′)
  r-pair  : ∀ {a a′ b b′} → Resolves E bound a a′ → Resolves E bound b b′
          → Resolves E bound (RPair a b) (RPair a′ b′)
  r-destruct : ∀ {e e′ xl el el′ xr er er′}
             → Resolves E bound e e′ → Resolves E (xl ∷ bound) el el′ → Resolves E (xr ∷ bound) er er′
             → Resolves E bound (RDestruct e xl el xr er) (RDestruct e′ xl el′ xr er′)
  r-unit  : Resolves E bound RUnit RUnit
  r-int   : ∀ {i} → Resolves E bound (RInt i) (RInt i)
  r-float : ∀ {i f l} → Resolves E bound (RFloat i f l) (RFloat i f l)
  r-annot : ∀ {e e′ T} → Resolves E bound e e′ → Resolves E bound (RAnnot e T) (RAnnot e′ T)
  r-binop : ∀ {op a a′ b b′} → Resolves E bound a a′ → Resolves E bound b b′
          → Resolves E bound (RBinOp op a b) (RBinOp op a′ b′)
  r-neg   : ∀ {e e′} → Resolves E bound e e′ → Resolves E bound (RNeg e) (RNeg e′)
