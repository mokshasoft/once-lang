-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ResolveBridge — the executable resolver IMPLEMENTS the
-- resolution spec. Plan 0.81 step 2.
--
-- PROOF (not trusted). `Once.Spec.Resolution` says which `CanonicalName` each
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
-- The work is entirely in the four decider bridges below — property to boolean
-- and back. That is the shape D134 asks for, and it is why the relation had to
-- be written independently: if it named `elemStr`/`isBuiltinName`/`lookupUnaliased`
-- directly, these lemmas would be `refl` and would prove nothing.
------------------------------------------------------------------------

module Once.Adequacy.ResolveBridge where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; _≟_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂)

open import Once.CanonicalName using (CanonicalName; canonical; gen; GenWord)
open import Once.TypeCheck.Raw
  using (RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair;
         RDestruct; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature;
  DTypeAlias; DImport)
open import Once.Parser.Module.Resolve
  using (canonExpr; canonVar; canonDecl; elemStr; isBuiltinName; expandPath;
         lookupUnaliased; lookupImportAlias;
         isBuiltinName-sound; isBuiltinName-false; ¬GenWord-isBuiltinName)
open import Once.Spec.Resolution

------------------------------------------------------------------------
-- Decider bridge 1: binder scope. `elemStr` vs `_∈_`.
------------------------------------------------------------------------

elemStr-complete : ∀ (x : String) (bound : List String) → x ∈ bound → elemStr x bound ≡ true
elemStr-complete x (y ∷ ys) (here refl) with x ≟ y
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)
elemStr-complete x (y ∷ ys) (there i) with x ≟ y
... | yes _ = refl
... | no  _ = elemStr-complete x ys i

∉⇒elemStr-false : ∀ (x : String) (bound : List String) → ¬ (x ∈ bound) → elemStr x bound ≡ false
∉⇒elemStr-false x []       ∉ = refl
∉⇒elemStr-false x (y ∷ ys) ∉ with x ≟ y
... | yes refl = ⊥-elim (∉ (here refl))
... | no  _    = ∉⇒elemStr-false x ys (λ i → ∉ (there i))

elemStr-sound : ∀ (x : String) (bound : List String) → elemStr x bound ≡ true → x ∈ bound
elemStr-sound x (y ∷ ys) eq with x ≟ y
... | yes refl = here refl
... | no  _    = there (elemStr-sound x ys eq)

elemStr-false⇒∉ : ∀ (x : String) (bound : List String) → elemStr x bound ≡ false → ¬ (x ∈ bound)
elemStr-false⇒∉ x (y ∷ ys) eq i with x ≟ y
elemStr-false⇒∉ x (y ∷ ys) () i | yes _
elemStr-false⇒∉ x (y ∷ ys) eq (here refl) | no ¬p = ⊥-elim (¬p refl)
elemStr-false⇒∉ x (y ∷ ys) eq (there i)   | no  _ = elemStr-false⇒∉ x ys eq i

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
                  → canonVar (elemStr x bound) (isBuiltinName x) (lookupUnaliased um x) x ≡ e
resolvesVar-sound bound um x _ (rv-binder i)
  rewrite elemStr-complete x bound i = refl
resolvesVar-sound bound um x _ (rv-gen ∉ gw)
  rewrite ∉⇒elemStr-false x bound ∉ | GenWord-isBuiltinName x gw = refl
resolvesVar-sound bound um x _ (rv-import ∉ ¬gw fa ex)
  rewrite ∉⇒elemStr-false x bound ∉ | ¬GenWord-isBuiltinName x ¬gw
        | lookupUn-complete um x _ fa | expandPath-complete _ _ ex = refl
resolvesVar-sound bound um x _ (rv-own ∉ ¬gw ab)
  rewrite ∉⇒elemStr-false x bound ∉ | ¬GenWord-isBuiltinName x ¬gw
        | lookupUn-absent um x ab = refl

resolvesVar-complete : ∀ (bound : List String) (um : UnaliasedMap) (x : String)
                     → ResolvesVar bound um x
                         (canonVar (elemStr x bound) (isBuiltinName x) (lookupUnaliased um x) x)
resolvesVar-complete bound um x with elemStr x bound in eb
... | true  = rv-binder (elemStr-sound x bound eb)
... | false with isBuiltinName x in eg
...   | true  = rv-gen (elemStr-false⇒∉ x bound eb) (isBuiltinName-sound x eg)
...   | false with lookupUnaliased um x in eu
...     | just p  = rv-import (elemStr-false⇒∉ x bound eb) (isBuiltinName-false x eg)
                              (lookupUn-sound um x p eu) (expandPath-sound p)
...     | nothing = rv-own (elemStr-false⇒∉ x bound eb) (isBuiltinName-false x eg)
                           (lookupUn-nothing um x eu)

------------------------------------------------------------------------
-- THE BRIDGE, at an expression. Congruence throughout; the two interesting
-- leaves are `RVar` (above) and `RQualified`.
------------------------------------------------------------------------

resolves-sound : ∀ (um : UnaliasedMap) (am : AliasMap) (bound : List String)
                 (e e' : RawExpr)
               → ResolvesExpr um am bound e e' → canonExpr bound um am e ≡ e'
resolves-sound um am bound _ _ (re-var rv) = resolvesVar-sound bound um _ _ rv
resolves-sound um am bound _ _ (re-qual {alias = a} fa ex)
  rewrite lookupAl-complete am a _ fa | expandPath-complete _ _ ex = refl
resolves-sound um am bound _ _ (re-qual-unknown {alias = a} ab)
  rewrite lookupAl-absent am a ab = refl
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
resolves-sound um am bound _ _ (re-unop {op = op} r) =
  cong (RUnaryOp op) (resolves-sound um am bound _ _ r)
resolves-sound um am bound _ _ (re-ana {F = F} r) =
  cong (RAna F) (resolves-sound um am bound _ _ r)
resolves-sound um am bound _ _ re-unit  = refl
resolves-sound um am bound _ _ re-int   = refl
resolves-sound um am bound _ _ re-float = refl
resolves-sound um am bound _ _ re-str   = refl

resolves-complete : ∀ (um : UnaliasedMap) (am : AliasMap) (bound : List String)
                    (e : RawExpr)
                  → ResolvesExpr um am bound e (canonExpr bound um am e)
resolves-complete um am bound (RVar x) = re-var (resolvesVar-complete bound um x)
resolves-complete um am bound (RQualified n a) with lookupImportAlias am a in ea
... | just p  = re-qual (lookupAl-sound am a p ea) (expandPath-sound p)
... | nothing = re-qual-unknown (lookupAl-nothing am a ea)
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
resolves-complete um am bound (RUnaryOp op e) = re-unop (resolves-complete um am bound e)
resolves-complete um am bound (RAna F c) = re-ana (resolves-complete um am bound c)
resolves-complete um am bound RUnit           = re-unit
resolves-complete um am bound (RInt n)        = re-int
resolves-complete um am bound (RFloat i f l p) = re-float
resolves-complete um am bound (RStringLit s)  = re-str

------------------------------------------------------------------------
-- THE BRIDGE, at a declaration. Only a function body carries references.
------------------------------------------------------------------------

resolvesDecl-sound : ∀ (polys : List String) (um : UnaliasedMap) (am : AliasMap)
                     (d d' : Decl)
                   → ResolvesDecl polys um am d d' → canonDecl polys um am d ≡ d'
resolvesDecl-sound polys um am _ _ (rd-fundef {name = n} {alloc = al} rb) =
  cong (DFunDef n al) (resolves-sound um am polys _ _ rb)
resolvesDecl-sound polys um am _ _ rd-typesig   = refl
resolvesDecl-sound polys um am _ _ rd-signature = refl
resolvesDecl-sound polys um am _ _ rd-typealias = refl
resolvesDecl-sound polys um am _ _ rd-import    = refl

resolvesDecl-complete : ∀ (polys : List String) (um : UnaliasedMap) (am : AliasMap)
                        (d : Decl)
                      → ResolvesDecl polys um am d (canonDecl polys um am d)
resolvesDecl-complete polys um am (DFunDef n al b) =
  rd-fundef (resolves-complete um am polys b)
resolvesDecl-complete polys um am (DTypeSig n t)      = rd-typesig
resolvesDecl-complete polys um am (DSignature n o t e) = rd-signature
resolvesDecl-complete polys um am (DTypeAlias n ps t) = rd-typealias
resolvesDecl-complete polys um am (DImport imp)       = rd-import
