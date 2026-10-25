-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Internal.Resolution — NAME RESOLUTION, in the compiler's internal
-- language. Plan 0.81. Which `CanonicalName` each written reference denotes;
-- the Spec's is `Once.Spec.Surface.Resolution`, related by `SpecFront.Resolve`.
--
-- Until this module existed, resolution was constrained only by three
-- "something survives it" facts (`resolver-preserves-typing`,
-- `resolver-reflects-typing`, `resolver-preserves-trace`). A resolver that sent
-- `foo` to the WRONG module while keeping the program well-typed and
-- behaviour-preserving satisfied all three. This relation says what the answer
-- IS, and `Once.Adequacy.ResolveBridge` proves the executable
-- `Once.Parser.Module.Resolve.resolveImports` computes it.
--
-- WRITTEN AS RULES, DELIBERATELY. It is the counterpart of the grammar
-- relation for the parser, and it earns its keep only by being an INDEPENDENT
-- statement: every side condition here is a PROPERTY (`x ∈ bound`,
-- `GenWord x`, `FirstAt a p am`), never a call to the decider the resolver
-- happens to use (`_∈?_`, `isBuiltinName`, `lookupImportAlias`). Reading it
-- off `canonExpr` would make the bridge lemmas tautologies (D134).
--
-- D136 is the substance of `rv-gen`/`rv-own`: a lexical binder shadows, a
-- RESERVED WORD is the generator whatever else is in scope, and only a name
-- that is neither takes an import path or the own module.
------------------------------------------------------------------------

module Once.Internal.Resolution where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

open import Once.Spec.Name using (canonical; gen; GenWord)
open import Once.Internal.ResolvedRefs using (GoodRefs)
open import Once.Spec.Surface.Syntax using (RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Parser.Module.Core using (Resolved; resolved)
open import Once.Spec.Surface.Syntax using (Module; mkModule; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (Import)
open import Once.Parser.Module.Resolve using (ModuleMap;
  importedOf; collectAliases; collectUnaliased)

------------------------------------------------------------------------
-- Environments, as DATA (they are tables, not procedures).
--
--   `bound` — the binders in scope, innermost first.
--   `um`    — unaliased imports: which module path exports each bare name.
--   `am`    — aliased imports: which module path each alias names.
------------------------------------------------------------------------

AliasMap : Set
AliasMap = List (String × List String)

UnaliasedMap : Set
UnaliasedMap = List (String × List String)

-- Association-list lookup is FIRST-MATCH, and the relation has to say so:
-- `(x , p) ∈ um` would also hold for a LATER duplicate, and then the resolver
-- (which takes the first) would not implement the relation. Found by trying to
-- prove `resolves-sound` — the permissive version is unprovable, which is
-- exactly the kind of thing an independent relation is for.
data FirstAt {K A : Set} (x : K) (p : A) : List (K × A) → Set where
  fa-here  : ∀ {rest} → FirstAt x p ((x , p) ∷ rest)
  fa-there : ∀ {y q rest} → y ≢ x → FirstAt x p rest → FirstAt x p ((y , q) ∷ rest)

-- `x` names no entry of the table.
Absent : {K A : Set} → K → List (K × A) → Set
Absent x = All (λ e → proj₁ e ≢ x)

------------------------------------------------------------------------
-- The `I` path abbreviation: a leading `I` abbreviates `Interpretations`.
-- Two rules rather than a call to `expandPath`.
------------------------------------------------------------------------

data ExpandsTo : List String → List String → Set where
  ex-nil   : ExpandsTo [] []
  ex-I     : ∀ {rest} → ExpandsTo ("I" ∷ rest) ("Interpretations" ∷ rest)
  ex-other : ∀ {c rest} → c ≢ "I" → ExpandsTo (c ∷ rest) (c ∷ rest)

------------------------------------------------------------------------
-- A bare reference. THE four-way decision, and the whole of D136.
------------------------------------------------------------------------

data ResolvesVar (bound : List String) (um : UnaliasedMap) : String → RawExpr → Set where

  -- A lexical binder shadows everything, generators included.
  rv-binder : ∀ {x}
            → x ∈ bound
            → ResolvesVar bound um x (RVar x)

  -- A RESERVED WORD is the generator. It does not matter what else is in
  -- scope: the namespace is compiler-owned, and a definition whose name a
  -- generator has taken is reached as `name@this`.
  rv-gen : ∀ {x}
         → ¬ (x ∈ bound) → GenWord x
         → ResolvesVar bound um x (RResolved (gen x))

  -- Neither: an unaliased import that exports it, at that module's full path.
  rv-import : ∀ {x path path'}
            → ¬ (x ∈ bound) → ¬ GenWord x
            → FirstAt x path um → ExpandsTo path path'
            → ResolvesVar bound um x (RResolved (canonical (path' ++ (x ∷ []))))

  -- Neither, and no import claims it: the OWN module, polymorphic or not
  -- (R11, D330). Generators and imports come first (the Spec's order).
  rv-own : ∀ {x}
         → ¬ (x ∈ bound) → ¬ GenWord x → Absent x um
         → ResolvesVar bound um x (RResolved (canonical (x ∷ [])))

------------------------------------------------------------------------
-- Expressions. Every non-reference form is a congruence; binders extend
-- `bound`, which is the only reason this is indexed by a scope at all.
------------------------------------------------------------------------

data ResolvesExpr (um : UnaliasedMap) (am : AliasMap)
                  : List String → RawExpr → RawExpr → Set where

  re-var : ∀ {bound x e}
         → ResolvesVar bound um x e
         → ResolvesExpr um am bound (RVar x) e

  -- D136: `name@this` is the OWN-MODULE escape hatch — how a definition whose
  -- name a generator has taken is reached. `this` is a RESERVED alias, decided
  -- before the alias table is consulted, so the other two rules must exclude
  -- it or the three would overlap.
  re-this : ∀ {bound name}
          → ResolvesExpr um am bound (RQualified name "this")
                                     (RResolved (canonical (name ∷ [])))

  -- `name@A` at a known alias is that module's path; at an unknown alias it is
  -- read as a path of ONE component, `A.name` (the Spec's `r-qual-path`).
  re-qual : ∀ {bound name alias path path'}
          → alias ≢ "this"
          → FirstAt alias path am → ExpandsTo path path'
          → ResolvesExpr um am bound (RQualified name alias)
                                     (RResolved (canonical (path' ++ (name ∷ []))))
  re-qual-path : ∀ {bound name alias}
               → alias ≢ "this"
               → Absent alias am
               → ResolvesExpr um am bound (RQualified name alias)
                                          (RResolved (canonical (alias ∷ name ∷ [])))

  -- Already resolved: the identity. This is what makes `name@this` and every
  -- compiler-generated reference a fixed point.
  re-res : ∀ {bound cn} → ResolvesExpr um am bound (RResolved cn) (RResolved cn)

  re-app : ∀ {bound f f' a a'}
         → ResolvesExpr um am bound f f' → ResolvesExpr um am bound a a'
         → ResolvesExpr um am bound (RApp f a) (RApp f' a')

  re-lam : ∀ {bound x b b'}
         → ResolvesExpr um am (x ∷ bound) b b'
         → ResolvesExpr um am bound (RLam x b) (RLam x b')

  re-let : ∀ {bound x e₁ e₁' e₂ e₂'}
         → ResolvesExpr um am bound e₁ e₁'
         → ResolvesExpr um am (x ∷ bound) e₂ e₂'
         → ResolvesExpr um am bound (RLet x e₁ e₂) (RLet x e₁' e₂')

  re-pair : ∀ {bound a a' b b'}
          → ResolvesExpr um am bound a a' → ResolvesExpr um am bound b b'
          → ResolvesExpr um am bound (RPair a b) (RPair a' b')

  re-destruct : ∀ {bound s s' xl el el' xr er er'}
              → ResolvesExpr um am bound s s'
              → ResolvesExpr um am (xl ∷ bound) el el'
              → ResolvesExpr um am (xr ∷ bound) er er'
              → ResolvesExpr um am bound (RDestruct s xl el xr er)
                                         (RDestruct s' xl el' xr er')

  re-annot : ∀ {bound e e' t}
           → ResolvesExpr um am bound e e'
           → ResolvesExpr um am bound (RAnnot e t) (RAnnot e' t)

  re-binop : ∀ {bound op a a' b b'}
           → ResolvesExpr um am bound a a' → ResolvesExpr um am bound b b'
           → ResolvesExpr um am bound (RBinOp op a b) (RBinOp op a' b')

  re-unop : ∀ {bound e e'}
          → ResolvesExpr um am bound e e'
          → ResolvesExpr um am bound (RNeg e) (RNeg e')


  -- Literals are fixed points.
  re-unit  : ∀ {bound} → ResolvesExpr um am bound RUnit RUnit
  re-int   : ∀ {bound n} → ResolvesExpr um am bound (RInt n) (RInt n)
  re-float : ∀ {bound i f l} → ResolvesExpr um am bound (RFloat i f l) (RFloat i f l)

------------------------------------------------------------------------
-- Declarations. Only a function BODY carries references; every other form
-- is untouched.
------------------------------------------------------------------------

data ResolvesDecl (um : UnaliasedMap) (am : AliasMap)
                  : Decl → Decl → Set where
  -- R11: the resolved body does not name `main` (`ResolvedRefs`).
  rd-fundef : ∀ {name body body'}
            → ResolvesExpr um am [] body body'
            → GoodRefs body'
            → ResolvesDecl um am (DFunDef name body)
                                       (DFunDef name body')
  -- Signatures, aliases and imports carry no references. ENUMERATED rather
  -- than a catch-all with a negative side condition: the reader sees that every
  -- declaration form has been considered, and nothing has to supply a `≢`.
  rd-typesig   : ∀ {n t}     → ResolvesDecl um am (DTypeSig n t) (DTypeSig n t)
  rd-signature : ∀ {n t} → ResolvesDecl um am (DSignature n t) (DSignature n t)
  rd-typealias : ∀ {n ps t}  → ResolvesDecl um am (DTypeAlias n ps t) (DTypeAlias n ps t)
  rd-import    : ∀ {imp}     → ResolvesDecl um am (DImport imp) (DImport imp)

------------------------------------------------------------------------
-- Declaration lists, and modules.
------------------------------------------------------------------------

-- WHERE THE LINE IS. This plan specifies the NAME MAP — which canonical name a
-- written reference denotes. It does NOT relationalise every helper: the module
-- table lookup is `FirstAt` (a real relation, because first-match matters), but
-- `importedOf`, `collectAliases` and `collectUnaliased` are
-- structural projections and pure renderers, and are named directly — the same
-- status `showCanonical` already has inside the typing rules. Nothing here
-- names a DECIDER about what a name means, which is the property that makes the
-- bridge lemmas non-trivial.
-- A declaration that is not an import. `resolveDecls` keeps an import as it
-- is and maps `canonDecl` over everything else, so the two cases are kept
-- apart.
data NotImport : Decl → Set where
  nim-typesig : ∀ {n t}     → NotImport (DTypeSig n t)
  nim-fundef  : ∀ {n b}     → NotImport (DFunDef n b)
  nim-sig     : ∀ {n t}     → NotImport (DSignature n t)
  nim-alias   : ∀ {n ps t}  → NotImport (DTypeAlias n ps t)

data ResolvesDecls (mm : ModuleMap)
                   (um : UnaliasedMap) (am : AliasMap)
                   : List Decl → List Decl → Set where
  rds-nil  : ResolvesDecls mm um am [] []
  rds-cons : ∀ {d d' ds ds'}
           → NotImport d
           → ResolvesDecl um am d d'
           → ResolvesDecls mm um am ds ds'
           → ResolvesDecls mm um am (d ∷ ds) (d' ∷ ds')
  -- An import stays where it was written (R10: a type signature an import
  -- separates from its definition is still separated); the module it names
  -- is one of the table's, consulted by first match. Its signatures are read
  -- from the table (`importedOf`), not copied in (plan 0.122).
  rds-import : ∀ {imp impDs ds ds'}
             → FirstAt (Import.path imp) (mkModule impDs) mm
             → ResolvesDecls mm um am ds ds'
             → ResolvesDecls mm um am (DImport imp ∷ ds) (DImport imp ∷ ds')

data ResolvesModule (mm : ModuleMap) : Module → Resolved → Set where
  rm : ∀ {ds ds'}
     → ResolvesDecls mm (collectUnaliased mm ds) (collectAliases ds) ds ds'
     → ResolvesModule mm (mkModule ds) (resolved (mkModule ds') (importedOf mm ds))
