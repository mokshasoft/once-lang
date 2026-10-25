-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ResolveBridge — the executable resolver IMPLEMENTS the
-- resolution spec. Plan 0.81 step 2.
--
-- PROOF (not trusted). `Once.Internal.Resolution` says which `CanonicalName` each
-- written reference denotes, as rules over PROPERTIES. This module proves that
-- `Once.Parser.Module.Resolve.canonExpr` computes exactly that:
--
--   `resolves-sound`    : the relation's answer IS the resolver's answer.
--   `resolves-complete` : the resolver's answer satisfies the relation.
--
-- Together they replace the three `ResolverBridge` obligations, none of which
-- constrained the name map at all (they said only that typing, typing
-- backwards, or traces SURVIVED resolution).
--
-- The work is entirely in the decider bridges below — property to boolean
-- and back. That is the shape D134 asks for, and it is why the relation had to
-- be written independently: if it named `_∈?_`/`isBuiltinName`/`lookupUnaliased`
-- directly, these lemmas would be `refl` and would prove nothing.
------------------------------------------------------------------------

module Once.Adequacy.ResolveBridge where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; does; proof)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Once.Internal.ResolvedRefs using (GoodRefs; goodRefs?)
open import Relation.Nullary.Reflects using (Reflects; invert)
open import Relation.Nullary.Decidable using (dec-true; dec-false)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Name using (GenWord)
open import Once.Spec.Surface.Syntax using (RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct; RUnit; RInt; RFloat; RAnnot; RBinOp; RNeg)
open import Once.Internal.Syntax using (RawExpr)
open import Once.Spec.Surface.Syntax using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; canonDecl; isBuiltinName; expandPath;
         lookupUnaliased; lookupImportAlias;
         isBuiltinName-sound; isBuiltinName-false; ¬GenWord-isBuiltinName)
open import Once.Internal.Resolution
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Once.Parser.Module.Core using (Resolved; resolved)
open import Once.Spec.Surface.Syntax using (Module; mkModule)
open import Once.Spec.Surface.Syntax using (Import)
open import Once.Parser.Module.Resolve using (ModuleMap; resolveImports;
  resolveDecls; resolveDecls-import-aux; resolveDecls-cons-aux; consDecl; consDecl-at;
  lookupModule; _path≟_; importedOf;
  collectAliases; collectUnaliased)

------------------------------------------------------------------------
-- Decider bridge 1: binder scope is stdlib's `_∈?_` (`dec-true`/`dec-false`
-- one way, `Reflects` the other).
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Decider bridge 2: the unaliased-import table. `lookupUnaliased` compares
-- `x ≟ n`; `lookupImportAlias` compares `a ≟ x`. Same relation, opposite
-- orientation — hence two families rather than one.
------------------------------------------------------------------------

lookupUn-complete : ∀ (um : UnaliasedMap) (x : String) (p : List String)
                  → FirstAt x p um → lookupUnaliased um x ≡ just p
lookupUn-complete ((n , q) ∷ rest) x p fa-here with x ≟ n
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
lookupUn-complete ((n , q) ∷ rest) x p (fa-there n≢x fa) with x ≟ n
... | yes refl = ⊥-elim (n≢x refl)
... | no  _    = lookupUn-complete rest x p fa

lookupUn-absent : ∀ (um : UnaliasedMap) (x : String)
                → Absent x um → lookupUnaliased um x ≡ nothing
lookupUn-absent []             x _        = refl
lookupUn-absent ((n , q) ∷ rs) x (d ∷ ds) with x ≟ n
... | yes refl = ⊥-elim (d refl)
... | no  _    = lookupUn-absent rs x ds

lookupUn-sound : ∀ (um : UnaliasedMap) (x : String) (p : List String)
               → lookupUnaliased um x ≡ just p → FirstAt x p um
lookupUn-sound ((n , q) ∷ rest) x p eq with x ≟ n
lookupUn-sound ((n , q) ∷ rest) x .q refl | yes refl = fa-here
... | no ¬e = fa-there (λ n≡x → ¬e (sym n≡x)) (lookupUn-sound rest x p eq)

lookupUn-nothing : ∀ (um : UnaliasedMap) (x : String)
                 → lookupUnaliased um x ≡ nothing → Absent x um
lookupUn-nothing []             x _  = []
lookupUn-nothing ((n , q) ∷ rs) x eq with x ≟ n
lookupUn-nothing ((n , q) ∷ rs) x () | yes _
... | no ¬e = (λ n≡x → ¬e (sym n≡x)) ∷ lookupUn-nothing rs x eq

------------------------------------------------------------------------
-- Decider bridge 3: the alias table.
------------------------------------------------------------------------

lookupAl-complete : ∀ (am : AliasMap) (a : String) (p : List String)
                  → FirstAt a p am → lookupImportAlias am a ≡ just p
lookupAl-complete ((n , q) ∷ rest) a p fa-here with n ≟ a
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
lookupAl-complete ((n , q) ∷ rest) a p (fa-there n≢a fa) with n ≟ a
... | yes e = ⊥-elim (n≢a e)
... | no  _ = lookupAl-complete rest a p fa

lookupAl-absent : ∀ (am : AliasMap) (a : String)
                → Absent a am → lookupImportAlias am a ≡ nothing
lookupAl-absent []             a _        = refl
lookupAl-absent ((n , q) ∷ rs) a (d ∷ ds) with n ≟ a
... | yes e = ⊥-elim (d e)
... | no  _ = lookupAl-absent rs a ds

lookupAl-sound : ∀ (am : AliasMap) (a : String) (p : List String)
               → lookupImportAlias am a ≡ just p → FirstAt a p am
lookupAl-sound ((n , q) ∷ rest) a p eq with n ≟ a
lookupAl-sound ((n , q) ∷ rest) .n .q refl | yes refl = fa-here
... | no ¬e = fa-there ¬e (lookupAl-sound rest a p eq)

lookupAl-nothing : ∀ (am : AliasMap) (a : String)
                 → lookupImportAlias am a ≡ nothing → Absent a am
lookupAl-nothing []             a _  = []
lookupAl-nothing ((n , q) ∷ rs) a eq with n ≟ a
lookupAl-nothing ((n , q) ∷ rs) a () | yes _
... | no ¬e = ¬e ∷ lookupAl-nothing rs a eq

------------------------------------------------------------------------
-- Decider bridge 4: the `I` path abbreviation.
------------------------------------------------------------------------

expandPath-complete : ∀ (p q : List String) → ExpandsTo p q → expandPath p ≡ q
expandPath-complete [] [] ex-nil = refl
expandPath-complete ("I" ∷ rest) _ ex-I with "I" ≟ "I"
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
{-# CATCHALL #-}
expandPath-complete (c ∷ rest) _ (ex-other c≢I) with c ≟ "I"
... | yes e = ⊥-elim (c≢I e)
... | no  _ = refl

expandPath-sound : ∀ (p : List String) → ExpandsTo p (expandPath p)
expandPath-sound []       = ex-nil
expandPath-sound (c ∷ rest) with c ≟ "I"
... | yes refl = ex-I
... | no ¬e    = ex-other ¬e

-- The remaining direction of the reserved-word bridge (`Resolve` already has
-- the other three).
GenWord-isBuiltinName : ∀ (x : String) → GenWord x → isBuiltinName x ≡ true
GenWord-isBuiltinName x gw with isBuiltinName x in eb
... | true  = refl
... | false = ⊥-elim (isBuiltinName-false x eb gw)

------------------------------------------------------------------------
-- THE BRIDGE, at a bare reference. Four arms, one per rule.
------------------------------------------------------------------------

resolvesVar-sound : ∀ (bound : List String) (um : UnaliasedMap) (x : String) (e : RawExpr)
                  → ResolvesVar bound um x e
                  → canonVar (does (x ∈? bound)) (isBuiltinName x) (lookupUnaliased um x) x ≡ e
resolvesVar-sound bound um x _ (rv-binder i)
  rewrite dec-true (x ∈? bound) i = refl
resolvesVar-sound bound um x _ (rv-gen ∉ gw)
  rewrite dec-false (x ∈? bound) ∉ | GenWord-isBuiltinName x gw = refl
resolvesVar-sound bound um x _ (rv-import ∉ ¬gw fa ex)
  rewrite dec-false (x ∈? bound) ∉ | ¬GenWord-isBuiltinName x ¬gw
        | lookupUn-complete um x _ fa | expandPath-complete _ _ ex = refl
resolvesVar-sound bound um x _ (rv-own ∉ ¬gw ab)
  rewrite dec-false (x ∈? bound) ∉ | ¬GenWord-isBuiltinName x ¬gw
        | lookupUn-absent um x ab = refl

resolvesVar-complete : ∀ (bound : List String) (um : UnaliasedMap) (x : String)
                     → ResolvesVar bound um x
                         (canonVar (does (x ∈? bound)) (isBuiltinName x) (lookupUnaliased um x) x)
resolvesVar-complete bound um x with does (x ∈? bound) in eb
... | true  = rv-binder (invert (subst (Reflects (x ∈ bound)) eb (proof (x ∈? bound))))
... | false with isBuiltinName x in eg
...   | true  = rv-gen (invert (subst (Reflects (x ∈ bound)) eb (proof (x ∈? bound)))) (isBuiltinName-sound x eg)
...   | false with lookupUnaliased um x in eu
...     | just p  = rv-import (invert (subst (Reflects (x ∈ bound)) eb (proof (x ∈? bound)))) (isBuiltinName-false x eg)
                              (lookupUn-sound um x p eu) (expandPath-sound p)
...     | nothing = rv-own (invert (subst (Reflects (x ∈ bound)) eb (proof (x ∈? bound)))) (isBuiltinName-false x eg)
                           (lookupUn-nothing um x eu)

------------------------------------------------------------------------
-- THE BRIDGE, at an expression. Congruence throughout; the two interesting
-- leaves are `RVar` (above) and `RQualified`.
------------------------------------------------------------------------

resolves-sound : ∀ (um : UnaliasedMap) (am : AliasMap) (bound : List String)
                 (e e' : RawExpr)
               → ResolvesExpr um am bound e e' → canonExpr bound um am e ≡ e'
resolves-sound um am bound _ _ (re-var rv) = resolvesVar-sound bound um _ _ rv
resolves-sound um am bound _ _ (re-this {name = n}) with "this" ≟ "this"
... | yes _ = refl
... | no ¬e = ⊥-elim (¬e refl)
resolves-sound um am bound _ _ (re-qual {alias = a} a≢ fa ex) with a ≟ "this"
... | yes e = ⊥-elim (a≢ e)
... | no  _ rewrite lookupAl-complete am a _ fa | expandPath-complete _ _ ex = refl
resolves-sound um am bound _ _ (re-qual-path {alias = a} a≢ ab) with a ≟ "this"
... | yes e = ⊥-elim (a≢ e)
... | no  _ rewrite lookupAl-absent am a ab = refl
resolves-sound um am bound _ _ re-res = refl
resolves-sound um am bound _ _ (re-app rf ra) =
  cong₂ RApp (resolves-sound um am bound _ _ rf) (resolves-sound um am bound _ _ ra)
resolves-sound um am bound _ _ (re-lam {x = x} rb) =
  cong (RLam x) (resolves-sound um am (x ∷ bound) _ _ rb)
resolves-sound um am bound _ _ (re-let {x = x} r₁ r₂) =
  cong₂ (RLet x) (resolves-sound um am bound _ _ r₁)
                 (resolves-sound um am (x ∷ bound) _ _ r₂)
resolves-sound um am bound _ _ (re-pair ra rb) =
  cong₂ RPair (resolves-sound um am bound _ _ ra) (resolves-sound um am bound _ _ rb)
resolves-sound um am bound _ _ (re-destruct {xl = xl} {xr = xr} rs rl rr) =
  cong₃ (λ a b c → RDestruct a xl b xr c)
        (resolves-sound um am bound _ _ rs)
        (resolves-sound um am (xl ∷ bound) _ _ rl)
        (resolves-sound um am (xr ∷ bound) _ _ rr)
  where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'}
          → a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
    cong₃ f refl refl refl = refl
resolves-sound um am bound _ _ (re-annot {t = t} r) =
  cong (λ z → RAnnot z t) (resolves-sound um am bound _ _ r)
resolves-sound um am bound _ _ (re-binop {op = op} ra rb) =
  cong₂ (RBinOp op) (resolves-sound um am bound _ _ ra) (resolves-sound um am bound _ _ rb)
resolves-sound um am bound _ _ (re-unop r) =
  cong RNeg (resolves-sound um am bound _ _ r)
resolves-sound um am bound _ _ re-unit  = refl
resolves-sound um am bound _ _ re-int   = refl
resolves-sound um am bound _ _ re-float = refl

resolves-complete : ∀ (um : UnaliasedMap) (am : AliasMap) (bound : List String)
                    (e : RawExpr)
                  → ResolvesExpr um am bound e (canonExpr bound um am e)
resolves-complete um am bound (RVar x) = re-var (resolvesVar-complete bound um x)
resolves-complete um am bound (RQualified n a) with a ≟ "this"
... | yes refl = re-this
... | no a≢ with lookupImportAlias am a in ea
...   | just p  = re-qual a≢ (lookupAl-sound am a p ea) (expandPath-sound p)
...   | nothing = re-qual-path a≢ (lookupAl-nothing am a ea)
resolves-complete um am bound (RResolved cn) = re-res
resolves-complete um am bound (RApp f a) =
  re-app (resolves-complete um am bound f) (resolves-complete um am bound a)
resolves-complete um am bound (RLam x b) = re-lam (resolves-complete um am (x ∷ bound) b)
resolves-complete um am bound (RLet x e₁ e₂) =
  re-let (resolves-complete um am bound e₁) (resolves-complete um am (x ∷ bound) e₂)
resolves-complete um am bound (RPair a b) =
  re-pair (resolves-complete um am bound a) (resolves-complete um am bound b)
resolves-complete um am bound (RDestruct s xl el xr er) =
  re-destruct (resolves-complete um am bound s)
              (resolves-complete um am (xl ∷ bound) el)
              (resolves-complete um am (xr ∷ bound) er)
resolves-complete um am bound (RAnnot e t) = re-annot (resolves-complete um am bound e)
resolves-complete um am bound (RBinOp op a b) =
  re-binop (resolves-complete um am bound a) (resolves-complete um am bound b)
resolves-complete um am bound (RNeg e) = re-unop (resolves-complete um am bound e)
resolves-complete um am bound RUnit           = re-unit
resolves-complete um am bound (RInt n)        = re-int
resolves-complete um am bound (RFloat i f l) = re-float

------------------------------------------------------------------------
-- THE BRIDGE, at a declaration. Only a function body carries references.
------------------------------------------------------------------------

resolvesDecl-sound : ∀ (um : UnaliasedMap) (am : AliasMap)
                     (d d' : Decl)
                   → ResolvesDecl um am d d' → canonDecl um am d ≡ d'
resolvesDecl-sound um am _ _ (rd-fundef {name = n} rb _) =
  cong (DFunDef n) (resolves-sound um am [] _ _ rb)
resolvesDecl-sound um am _ _ rd-typesig   = refl
resolvesDecl-sound um am _ _ rd-signature = refl
resolvesDecl-sound um am _ _ rd-typealias = refl
resolvesDecl-sound um am _ _ rd-import    = refl

-- R11: a definition's resolved body is good (the resolver's check).
DeclGood : Decl → Set
DeclGood (DFunDef _ b) = GoodRefs b
{-# CATCHALL #-}
DeclGood _             = ⊤

resolvesDecl-complete : ∀ (um : UnaliasedMap) (am : AliasMap)
                        (d : Decl) → DeclGood (canonDecl um am d)
                      → ResolvesDecl um am d (canonDecl um am d)
resolvesDecl-complete um am (DFunDef n b) g =
  rd-fundef (resolves-complete um am [] b) g
resolvesDecl-complete um am (DTypeSig n t)      _ = rd-typesig
resolvesDecl-complete um am (DSignature n t)  _ = rd-signature
resolvesDecl-complete um am (DTypeAlias n ps t) _ = rd-typealias
resolvesDecl-complete um am (DImport imp)       _ = rd-import

-- The resolver's check, either way.
consDecl-ok : ∀ {um am d d'} (tl : List Decl) → ResolvesDecl um am d d'
            → consDecl d' tl ≡ inj₂ (d' ∷ tl)
consDecl-ok tl (rd-fundef {name = n} {body' = b′} rb g) = at (goodRefs? b′)
  where
    at : (dg : Dec (GoodRefs b′)) → consDecl-at n b′ dg tl ≡ inj₂ (DFunDef n b′ ∷ tl)
    at (yes _) = refl
    at (no ¬g) = ⊥-elim (¬g g)
consDecl-ok tl rd-typesig   = refl
consDecl-ok tl rd-signature = refl
consDecl-ok tl rd-typealias = refl
consDecl-ok tl rd-import    = refl

consDecl-inv : ∀ (d : Decl) (tl ds' : List Decl) → consDecl d tl ≡ inj₂ ds'
             → (ds' ≡ d ∷ tl) × DeclGood d
consDecl-inv (DFunDef n b) tl ds' eq = at (goodRefs? b) eq
  where
    at : (dg : Dec (GoodRefs b)) → consDecl-at n b dg tl ≡ inj₂ ds' → (ds' ≡ DFunDef n b ∷ tl) × GoodRefs b
    at (yes g) refl = refl , g
    at (no _) ()
consDecl-inv (DTypeSig n t)      tl _ refl = refl , tt
consDecl-inv (DSignature n t)  tl _ refl = refl , tt
consDecl-inv (DTypeAlias n ps t) tl _ refl = refl , tt
consDecl-inv (DImport imp)       tl _ refl = refl , tt

------------------------------------------------------------------------
-- THE BRIDGE, at a module. Covers IMPORTS: `resolveDecls` replaces a
-- `DImport` by the imported module's signatures, or FAILS when the module map
-- has no entry for the path — and `FirstAt` is exactly "the map has one, at
-- first match", so the two agree without a residual.
------------------------------------------------------------------------

-- Decider bridge 5: the module table. Keyed by PATH, so it needs the list
-- equality test bridged the same way the string one was.
path≟-refl : ∀ (p : List String) → (p path≟ p) ≡ true
path≟-refl []       = refl
path≟-refl (x ∷ xs) with x ≟ x
... | yes _ = path≟-refl xs
... | no ¬e = ⊥-elim (¬e refl)

path≟-sound : ∀ (p q : List String) → (p path≟ q) ≡ true → p ≡ q
path≟-sound []       []       _  = refl
path≟-sound (x ∷ xs) (y ∷ ys) eq with x ≟ y
... | yes refl = cong (x ∷_) (path≟-sound xs ys eq)
path≟-sound (x ∷ xs) (y ∷ ys) () | no _

lookupMod-complete : ∀ (mm : ModuleMap) (path : List String) (m : Module)
                   → FirstAt path m mm → lookupModule mm path ≡ just m
lookupMod-complete ((p , q) ∷ rest) path m fa-here rewrite path≟-refl path = refl
lookupMod-complete ((p , q) ∷ rest) path m (fa-there p≢ fa) with p path≟ path in ep
... | true  = ⊥-elim (p≢ (path≟-sound p path ep))
... | false = lookupMod-complete rest path m fa

-- The aux CARRIES its equations, so a plain `rewrite` on the lookup cannot fire
-- (it would have to rewrite the `refl` proof alongside). Generalise over both
-- (scrutinee, equation) pairs and match — the J-style bridge the codebase uses
-- wherever a de-withed aux has to be driven from outside.
import-red : ∀ (um : UnaliasedMap) (am : AliasMap)
               (mm : ModuleMap) (imp : Import) (rest : List Decl)
               (impDs tailDs : List Decl)
           → lookupModule mm (Import.path imp) ≡ just (mkModule impDs)
           → resolveDecls um am mm rest ≡ inj₂ tailDs
           → resolveDecls um am mm (DImport imp ∷ rest)
               ≡ inj₂ (DImport imp ∷ tailDs)
import-red um am mm imp rest impDs tailDs elm err = go _ refl _ refl
  where
    go : ∀ (lm : Maybe Module) (e1 : lookupModule mm (Import.path imp) ≡ lm)
           (rr : String ⊎ List Decl) (e2 : resolveDecls um am mm rest ≡ rr)
       → resolveDecls-import-aux um am mm imp rest lm e1 rr e2
           ≡ inj₂ (DImport imp ∷ tailDs)
    go lm e1 rr e2 with trans (sym e1) elm | trans (sym e2) err
    ... | refl | refl = refl

resolvesDecls-sound : ∀ (mm : ModuleMap)
                      (um : UnaliasedMap) (am : AliasMap) (ds ds' : List Decl)
                    → ResolvesDecls mm um am ds ds'
                    → resolveDecls um am mm ds ≡ inj₂ ds'
resolvesDecls-sound mm um am _ _ rds-nil = refl
resolvesDecls-sound mm um am _ _ (rds-cons nim-typesig rd rds)
  rewrite resolvesDecls-sound mm um am _ _ rds
        | resolvesDecl-sound um am _ _ rd = refl
resolvesDecls-sound mm um am _ _ (rds-cons {d = d} {d' = d'} {ds' = ds'} nim-fundef rd rds) =
  trans (cong (resolveDecls-cons-aux um am d) (resolvesDecls-sound mm um am _ _ rds))
        (trans (cong (λ d″ → consDecl d″ ds') (resolvesDecl-sound um am _ _ rd)) (consDecl-ok ds' rd))
resolvesDecls-sound mm um am _ _ (rds-cons nim-sig rd rds)
  rewrite resolvesDecls-sound mm um am _ _ rds
        | resolvesDecl-sound um am _ _ rd = refl
resolvesDecls-sound mm um am _ _ (rds-cons nim-alias rd rds)
  rewrite resolvesDecls-sound mm um am _ _ rds
        | resolvesDecl-sound um am _ _ rd = refl
resolvesDecls-sound mm um am _ _
  (rds-import {imp = imp} {impDs = impDs} {ds = ds} {ds' = ds'} fa rds) =
  import-red um am mm imp ds impDs ds'
    (lookupMod-complete mm (Import.path imp) (mkModule impDs) fa)
    (resolvesDecls-sound mm um am ds ds' rds)

resolvesModule-sound : ∀ (mm : ModuleMap) (ds : List Decl) (mR : Resolved)
                     → ResolvesModule mm (mkModule ds) mR
                     → resolveImports mm (mkModule ds) ≡ inj₂ mR
resolvesModule-sound mm ds _ (rm rds)
  rewrite resolvesDecls-sound mm (collectUnaliased mm ds)
                              (collectAliases ds) ds _ rds = refl

path≟-false⇒≢ : ∀ (p q : List String) → (p path≟ q) ≡ false → p ≢ q
path≟-false⇒≢ p .p eq refl with trans (sym (path≟-refl p)) eq
... | ()

lookupMod-sound : ∀ (mm : ModuleMap) (path : List String) (m : Module)
                → lookupModule mm path ≡ just m → FirstAt path m mm
lookupMod-sound ((p , q) ∷ rest) path m eq with p path≟ path in ep
lookupMod-sound ((p , q) ∷ rest) path .q refl | true
  rewrite path≟-sound p path ep = fa-here
... | false = fa-there (path≟-false⇒≢ p path ep) (lookupMod-sound rest path m eq)

-- The completeness direction, now PROVEN. `resolveDecls` was de-withed in plan
-- 0.81 for exactly this: with the module-table lookup and the recursive call as
-- explicit PARAMETERS carrying their equations, the hypothesis
-- `resolveDecls … ≡ inj₂ ds'` reduces as soon as those two are matched. A
-- `with` could never make that happen — the hypothesis mentions neither
-- scrutinee, so nothing abstracts it and no `rewrite` fires.
mutual
  resolvesDecls-complete : ∀ (mm : ModuleMap)
                           (um : UnaliasedMap) (am : AliasMap) (ds ds' : List Decl)
                         → resolveDecls um am mm ds ≡ inj₂ ds'
                         → ResolvesDecls mm um am ds ds'
  resolvesDecls-complete mm um am [] _ refl = rds-nil
  resolvesDecls-complete mm um am (DImport imp ∷ rest) ds' eq =
    rdc-import mm um am imp rest ds'
      (lookupModule mm (Import.path imp)) refl
      (resolveDecls um am mm rest) refl eq
  resolvesDecls-complete mm um am (DTypeSig n t ∷ rest) ds' eq =
    rdc-cons mm um am (DTypeSig n t) nim-typesig rest ds'
      (resolveDecls um am mm rest) refl eq
  resolvesDecls-complete mm um am (DFunDef n b ∷ rest) ds' eq =
    rdc-cons mm um am (DFunDef n b) nim-fundef rest ds'
      (resolveDecls um am mm rest) refl eq
  resolvesDecls-complete mm um am (DSignature n t ∷ rest) ds' eq =
    rdc-cons mm um am (DSignature n t) nim-sig rest ds'
      (resolveDecls um am mm rest) refl eq
  resolvesDecls-complete mm um am (DTypeAlias n ps t ∷ rest) ds' eq =
    rdc-cons mm um am (DTypeAlias n ps t) nim-alias rest ds'
      (resolveDecls um am mm rest) refl eq

  rdc-import : ∀ (mm : ModuleMap) (um : UnaliasedMap)
                 (am : AliasMap) (imp : Import) (rest : List Decl) (ds' : List Decl)
             → (lm : Maybe Module) (elm : lookupModule mm (Import.path imp) ≡ lm)
             → (rr : String ⊎ List Decl) (err : resolveDecls um am mm rest ≡ rr)
             → resolveDecls-import-aux um am mm imp rest lm elm rr err ≡ inj₂ ds'
             → ResolvesDecls mm um am (DImport imp ∷ rest) ds'
  rdc-import mm um am imp rest ds' nothing elm rr err ()
  rdc-import mm um am imp rest ds' (just (mkModule impDs)) elm (inj₁ e) err ()
  rdc-import mm um am imp rest _ (just (mkModule impDs)) elm (inj₂ tailDs) err refl =
    rds-import (lookupMod-sound mm (Import.path imp) (mkModule impDs) elm)
               (resolvesDecls-complete mm um am rest tailDs err)

  rdc-cons : ∀ (mm : ModuleMap) (um : UnaliasedMap)
               (am : AliasMap) (d : Decl) → NotImport d
           → ∀ (rest : List Decl) (ds' : List Decl)
           → (rr : String ⊎ List Decl) (err : resolveDecls um am mm rest ≡ rr)
           → resolveDecls-cons-aux um am d rr ≡ inj₂ ds'
           → ResolvesDecls mm um am (d ∷ rest) ds'
  rdc-cons mm um am d nim rest ds' (inj₁ e) err ()
  rdc-cons mm um am d nim rest ds' (inj₂ tailDs) err eq =
    let (e , g) = consDecl-inv (canonDecl um am d) tailDs ds' eq
    in subst (ResolvesDecls mm um am (d ∷ rest)) (sym e)
             (rds-cons nim (resolvesDecl-complete um am d g)
                       (resolvesDecls-complete mm um am rest tailDs err))

resolveImports-ok : ∀ (mm : ModuleMap) (ds ds' : List Decl)
                  → resolveDecls (collectUnaliased mm ds)
                                 (collectAliases ds) mm ds ≡ inj₂ ds'
                  → resolveImports mm (mkModule ds) ≡ inj₂ (resolved (mkModule ds') (importedOf mm ds))
resolveImports-ok mm ds ds' err rewrite err = refl

resolveImports-bad : ∀ (mm : ModuleMap) (ds : List Decl) (e : String)
                   → resolveDecls (collectUnaliased mm ds)
                                  (collectAliases ds) mm ds ≡ inj₁ e
                   → resolveImports mm (mkModule ds) ≡ inj₁ e
resolveImports-bad mm ds e err rewrite err = refl

resolvesModule-complete : ∀ (mm : ModuleMap) (ds : List Decl) (mR : Resolved)
                        → resolveImports mm (mkModule ds) ≡ inj₂ mR
                        → ResolvesModule mm (mkModule ds) mR
resolvesModule-complete mm ds mR eqR =
  go (resolveDecls (collectUnaliased mm ds) (collectAliases ds) mm ds) refl
  where
    go : ∀ (rr : String ⊎ List Decl)
       → resolveDecls (collectUnaliased mm ds)
                      (collectAliases ds) mm ds ≡ rr
       → ResolvesModule mm (mkModule ds) mR
    go (inj₁ e)   err with trans (sym eqR) (resolveImports-bad mm ds e err)
    ...               | ()
    go (inj₂ ds') err with trans (sym eqR) (resolveImports-ok mm ds ds' err)
    ...               | refl =
      rm (resolvesDecls-complete mm (collectUnaliased mm ds)
                                 (collectAliases ds) ds ds' err)
