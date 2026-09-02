-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Spec.Resolution — NAME RESOLUTION (OCP-0006, spec). Plan 0.81.
--
-- SPEC (trust boundary): which `CanonicalName` each written reference denotes.
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
-- happens to use (`elemStr`, `isBuiltinName`, `lookupImportAlias`). Reading it
-- off `canonExpr` would make the bridge lemmas tautologies (D134).
--
-- D136 is the substance of `rv-gen`/`rv-own`: a lexical binder shadows, a
-- RESERVED WORD is the generator whatever else is in scope, and only a name
-- that is neither takes an import path or the own module.
------------------------------------------------------------------------

module Once.Spec.Resolution where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

open import Once.CanonicalName using (CanonicalName; canonical; gen; GenWord)
open import Once.Spec.Syntax using (RawExpr; RVar; RQualified; RResolved; RApp;
  RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RStringLit; RAnnot;
  RBinOp; RUnaryOp; RAna)
open import Once.Parser.Module.Core using (Module; mkModule; Decl;
  DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; Import)
open import Once.Parser.Module.Resolve using (ModuleMap;
  signaturesWithOwner; ownerOf; collectAliases; collectUnaliased)

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

  -- Neither, and no import claims it: the OWN module.
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

  -- `name@A` at a known alias is that module's path; at an unknown alias it is
  -- left alone (the typing rules then have nothing to look it up by).
  re-qual : ∀ {bound name alias path path'}
          → FirstAt alias path am → ExpandsTo path path'
          → ResolvesExpr um am bound (RQualified name alias)
                                     (RResolved (canonical (path' ++ (name ∷ []))))
  re-qual-unknown : ∀ {bound name alias}
                  → Absent alias am
                  → ResolvesExpr um am bound (RQualified name alias)
                                             (RQualified name alias)

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

  re-unop : ∀ {bound op e e'}
          → ResolvesExpr um am bound e e'
          → ResolvesExpr um am bound (RUnaryOp op e) (RUnaryOp op e')

  re-ana : ∀ {bound F c c'}
         → ResolvesExpr um am bound c c'
         → ResolvesExpr um am bound (RAna F c) (RAna F c')

  -- Literals are fixed points.
  re-unit  : ∀ {bound} → ResolvesExpr um am bound RUnit RUnit
  re-int   : ∀ {bound n} → ResolvesExpr um am bound (RInt n) (RInt n)
  re-float : ∀ {bound i f l p} → ResolvesExpr um am bound (RFloat i f l p) (RFloat i f l p)
  re-str   : ∀ {bound s} → ResolvesExpr um am bound (RStringLit s) (RStringLit s)

------------------------------------------------------------------------
-- Declarations. Only a function BODY carries references; every other form
-- is untouched.
------------------------------------------------------------------------

data ResolvesDecl (polys : List String) (um : UnaliasedMap) (am : AliasMap)
                  : Decl → Decl → Set where
  rd-fundef : ∀ {name alloc body body'}
            → ResolvesExpr um am polys body body'
            → ResolvesDecl polys um am (DFunDef name alloc body)
                                       (DFunDef name alloc body')
  -- Signatures, aliases and imports carry no references. ENUMERATED rather
  -- than a catch-all with a negative side condition: the reader sees that every
  -- declaration form has been considered, and nothing has to supply a `≢`.
  rd-typesig   : ∀ {n t}     → ResolvesDecl polys um am (DTypeSig n t) (DTypeSig n t)
  rd-signature : ∀ {n o t e} → ResolvesDecl polys um am (DSignature n o t e) (DSignature n o t e)
  rd-typealias : ∀ {n ps t}  → ResolvesDecl polys um am (DTypeAlias n ps t) (DTypeAlias n ps t)
  rd-import    : ∀ {imp}     → ResolvesDecl polys um am (DImport imp) (DImport imp)

------------------------------------------------------------------------
-- Declaration lists, and modules.
--
-- SCOPE-PARAMETERISED, deliberately. The initial scope is the module's
-- POLYMORPHIC definitions (they stay bare, so the poly telescope can δ-reduce
-- at the use site), and the resolver computes it with `polyDefNames`, which
-- calls `siglessSchema` — i.e. the PRINCIPALITY ORACLE. Specifying which
-- definitions are polymorphic therefore means specifying the oracle, which is
-- plan 0.59's subject, not this one. Taking the scope as a parameter keeps the
-- two questions separate and keeps this relation honest about what it pins:
-- given the scope, WHICH CANONICAL NAME each reference denotes.
------------------------------------------------------------------------

-- WHERE THE LINE IS. This plan specifies the NAME MAP — which canonical name a
-- written reference denotes. It does NOT relationalise every helper: the module
-- table lookup is `FirstAt` (a real relation, because first-match matters), but
-- `signaturesWithOwner`, `ownerOf`, `collectAliases` and `collectUnaliased` are
-- structural projections and pure renderers, and are named directly — the same
-- status `showCanonical` already has inside the typing rules. Nothing here
-- names a DECIDER about what a name means, which is the property that makes the
-- bridge lemmas non-trivial.
-- A declaration that is not an import. `resolveDecls` REPLACES an import and
-- maps `canonDecl` over everything else, so the two cases must be kept apart:
-- without this, `rds-cons` could also derive "a `DImport` survives", which is
-- not what the resolver does.
data NotImport : Decl → Set where
  nim-typesig : ∀ {n t}     → NotImport (DTypeSig n t)
  nim-fundef  : ∀ {n a b}   → NotImport (DFunDef n a b)
  nim-sig     : ∀ {n o t e} → NotImport (DSignature n o t e)
  nim-alias   : ∀ {n ps t}  → NotImport (DTypeAlias n ps t)

data ResolvesDecls (mm : ModuleMap) (polys : List String)
                   (um : UnaliasedMap) (am : AliasMap)
                   : List Decl → List Decl → Set where
  rds-nil  : ResolvesDecls mm polys um am [] []
  rds-cons : ∀ {d d' ds ds'}
           → NotImport d
           → ResolvesDecl polys um am d d'
           → ResolvesDecls mm polys um am ds ds'
           → ResolvesDecls mm polys um am (d ∷ ds) (d' ∷ ds')
  -- An import is REPLACED by the imported module's signatures, owned by the
  -- importing site. The module table is consulted by first match.
  rds-import : ∀ {imp impDs ds ds'}
             → FirstAt (Import.path imp) (mkModule impDs) mm
             → ResolvesDecls mm polys um am ds ds'
             → ResolvesDecls mm polys um am (DImport imp ∷ ds)
                             (signaturesWithOwner (ownerOf imp) impDs ++ ds')

data ResolvesModule (mm : ModuleMap) (polys : List String) : Module → Module → Set where
  rm : ∀ {ds ds'}
     → ResolvesDecls mm polys (collectUnaliased mm ds) (collectAliases ds) ds ds'
     → ResolvesModule mm polys (mkModule ds) (mkModule ds')
