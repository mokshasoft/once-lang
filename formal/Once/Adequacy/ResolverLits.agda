-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ResolverLits — RESOLUTION PRESERVES `Int` LITERALS
-- (plan 0.74 J4, D115).
--
-- Admissibility is stated over the UN-resolved module — that is what
-- `src ⊢R tp` gives — while the compiler gates on the RESOLVED one. They must
-- have the same `Int` literals or the gate and the meaning are talking about
-- different programs.
--
-- They do, for two reasons that are checkable rather than hopeful:
--
--   * `canonDecl` rewrites only a `DFunDef`'s body, via `canonExpr`, which is
--     a structural rewrite turning `RQualified`/`RVar` into `RResolved` and
--     leaving `RInt` exactly where it was.
--   * imports are inlined by `signaturesWithOwner`, which keeps ONLY
--     `DSignature` decls and DROPS everything else — so no imported function
--     body, and hence no imported literal, is ever added.
--
-- Sibling of `resolver-preserves-trace` / `resolver-preserves-typing`; this is
-- the same "resolution does not change what matters" family.
------------------------------------------------------------------------

module Once.Adequacy.ResolverLits where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Empty using (⊥; ⊥-elim)
open import Once.Parser.Module.Core using (Import)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (ℤ)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Once.TypeCheck.Raw using
  ( RawExpr; RVar; RQualified; RResolved; RApp; RLam; RLet; RPair; RDestruct
  ; RUnit; RInt; RFloat; RStringLit; RAnnot; RBinOp; RUnaryOp; RAna
  ; OpNeg )
open import Once.Parser.Module.Core using
  ( Module; mkModule; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport )
open import Once.Parser.Module.Resolve using
  ( canonExpr; canonVar; canonDecl; signaturesWithOwner; resolveDecls
  ; resolveImports; lookupImportAlias; lookupUnaliased; lookupModule
  ; AliasMap; UnaliasedMap; ModuleMap; collectAliases; collectUnaliased
  ; polyDefNames; ownerOf; expandPath; elemStr; isBuiltinName )
open import Once.Denotation.Admissible using
  ( rawIntLits; negLits; declIntLits; moduleIntLits )

------------------------------------------------------------------------
-- `canonExpr` moves references, never literals
------------------------------------------------------------------------

-- `canonVar` produces an `RVar` or an `RResolved` — a leaf either way, so no
-- literal can appear or vanish. Enumerated, so a new form of reference would
-- have to be confronted here rather than silently returning `[]`.
canonVar-lits : ∀ (b : Bool) (mp : Maybe (List String)) (x : String)
              → rawIntLits (canonVar b mp x) ≡ []
canonVar-lits true  _          x = refl
canonVar-lits false (just _)   x = refl
canonVar-lits false nothing    x = refl

-- The same at the operand of a unary minus. It is a SEPARATE lemma and not a
-- corollary because `negLits` asks a question `rawIntLits` does not: is this
-- operand a NUMERAL? So preserving the literals is no longer enough — the
-- resolver must also preserve whether an operand IS one, or `-2147483648`
-- could resolve into something the spec no longer reads as a single literal.
-- It does preserve it, and for a blunt reason: `canonExpr` only ever rewrites
-- names (`RVar`/`RQualified` → `RResolved`) and rebuilds every other node with
-- its own head. It cannot manufacture an `RInt`, and it cannot destroy one.
negLits-canonVar : ∀ (b : Bool) (mp : Maybe (List String)) (x : String)
                 → negLits (canonVar b mp x) ≡ []
negLits-canonVar true  _        x = refl
negLits-canonVar false (just _) x = refl
negLits-canonVar false nothing  x = refl

canonExpr-lits : ∀ (bound : List String) (um : UnaliasedMap) (am : AliasMap) (e : RawExpr)
               → rawIntLits (canonExpr bound um am e) ≡ rawIntLits e
negLits-lits   : ∀ (bound : List String) (um : UnaliasedMap) (am : AliasMap) (e : RawExpr)
               → negLits (canonExpr bound um am e) ≡ negLits e
canonExpr-lits bound um am (RQualified name alias) with lookupImportAlias am alias
... | just _  = refl
... | nothing = refl
canonExpr-lits bound um am (RVar x)  =
  canonVar-lits (elemStr x bound ∨ isBuiltinName x) (lookupUnaliased um x) x
canonExpr-lits bound um am (RResolved _) = refl
canonExpr-lits bound um am RUnit         = refl
canonExpr-lits bound um am (RInt n)      = refl
canonExpr-lits bound um am (RFloat _ _ _ _) = refl
canonExpr-lits bound um am (RStringLit _) = refl
canonExpr-lits bound um am (RApp f x) =
  cong₂ _++_ (canonExpr-lits bound um am f) (canonExpr-lits bound um am x)
canonExpr-lits bound um am (RLam x b) = canonExpr-lits (x ∷ bound) um am b
canonExpr-lits bound um am (RLet x e₁ e₂) =
  cong₂ _++_ (canonExpr-lits bound um am e₁) (canonExpr-lits (x ∷ bound) um am e₂)
canonExpr-lits bound um am (RPair a b) =
  cong₂ _++_ (canonExpr-lits bound um am a) (canonExpr-lits bound um am b)
canonExpr-lits bound um am (RDestruct s xl el xr er) =
  cong₂ _++_ (canonExpr-lits bound um am s)
    (cong₂ _++_ (canonExpr-lits (xl ∷ bound) um am el)
                (canonExpr-lits (xr ∷ bound) um am er))
canonExpr-lits bound um am (RAnnot e _)     = canonExpr-lits bound um am e
canonExpr-lits bound um am (RBinOp _ a b)   =
  cong₂ _++_ (canonExpr-lits bound um am a) (canonExpr-lits bound um am b)
canonExpr-lits bound um am (RUnaryOp OpNeg e) = negLits-lits bound um am e
canonExpr-lits bound um am (RAna _ c)       = canonExpr-lits bound um am c

-- ENUMERATED, exactly as `rawIntLits` is, and for the same reason: a catch-all
-- would quietly cover a constructor added later, and the case it covered wrong
-- would be the one where a resolved operand stopped looking like a numeral.
-- Every clause but the first defers to `canonExpr-lits` — `negLits` reduces to
-- `rawIntLits` on both sides as soon as the head constructor is known, and
-- `canonExpr` keeps the head.
negLits-lits bound um am (RInt n)      = refl
negLits-lits bound um am (RVar x)      =
  negLits-canonVar (elemStr x bound ∨ isBuiltinName x) (lookupUnaliased um x) x
negLits-lits bound um am (RQualified name alias) with lookupImportAlias am alias
... | just _  = refl
... | nothing = refl
negLits-lits bound um am (RResolved _)  = refl
negLits-lits bound um am RUnit          = refl
negLits-lits bound um am (RFloat _ _ _ _) = refl
negLits-lits bound um am (RStringLit _) = refl
negLits-lits bound um am (RApp f x)     = canonExpr-lits bound um am (RApp f x)
negLits-lits bound um am (RLam x b)     = canonExpr-lits bound um am (RLam x b)
negLits-lits bound um am (RLet x e₁ e₂) = canonExpr-lits bound um am (RLet x e₁ e₂)
negLits-lits bound um am (RPair a b)    = canonExpr-lits bound um am (RPair a b)
negLits-lits bound um am (RDestruct s xl el xr er) =
  canonExpr-lits bound um am (RDestruct s xl el xr er)
negLits-lits bound um am (RAnnot e T)   = canonExpr-lits bound um am (RAnnot e T)
negLits-lits bound um am (RBinOp o a b) = canonExpr-lits bound um am (RBinOp o a b)
negLits-lits bound um am (RUnaryOp o e) = canonExpr-lits bound um am (RUnaryOp o e)
negLits-lits bound um am (RAna t c)     = canonExpr-lits bound um am (RAna t c)

canonDecl-lits : ∀ (polys : List String) (um : UnaliasedMap) (am : AliasMap) (d : Decl)
               → declIntLits (canonDecl polys um am d) ≡ declIntLits d
canonDecl-lits polys um am (DFunDef _ _ body) = canonExpr-lits polys um am body
canonDecl-lits polys um am (DTypeSig _ _)     = refl
canonDecl-lits polys um am (DSignature _ _ _ _) = refl
canonDecl-lits polys um am (DTypeAlias _ _ _) = refl
canonDecl-lits polys um am (DImport _)        = refl

------------------------------------------------------------------------
-- Inlined imports contribute no literals
------------------------------------------------------------------------

-- `declsIntLits` for a decl list, matching `moduleIntLits`' own walk.
declsIntLits : List Decl → List ℤ
declsIntLits []       = []
declsIntLits (d ∷ ds) = declIntLits d ++ declsIntLits ds

-- THE reason imports are safe: `signaturesWithOwner` keeps only `DSignature`
-- and drops the rest, so an imported module's function bodies — and their
-- literals — never enter the importer.
sigsWithOwner-lits : ∀ (owner : Maybe String) (ds : List Decl)
                   → declsIntLits (signaturesWithOwner owner ds) ≡ []
sigsWithOwner-lits owner []                        = refl
sigsWithOwner-lits owner (DSignature _ _ _ _ ∷ ds) = sigsWithOwner-lits owner ds
sigsWithOwner-lits owner (DTypeSig _ _ ∷ ds)       = sigsWithOwner-lits owner ds
sigsWithOwner-lits owner (DFunDef _ _ _ ∷ ds)      = sigsWithOwner-lits owner ds
sigsWithOwner-lits owner (DTypeAlias _ _ _ ∷ ds)   = sigsWithOwner-lits owner ds
sigsWithOwner-lits owner (DImport _ ∷ ds)          = sigsWithOwner-lits owner ds

------------------------------------------------------------------------
-- …and therefore resolution preserves the literals
--
-- `resolveDecls` is a nested `with`-chain (on `lookupModule`, then on the
-- recursive call), so this mirrors it clause for clause. The two substantive
-- steps are the lemmas above: the IMPORT case discharges by
-- `sigsWithOwner-lits` (nothing is added), the ORDINARY case by
-- `canonDecl-lits` (nothing is moved). Everything else is list bookkeeping.
------------------------------------------------------------------------

declsIntLits-++ : ∀ (xs ys : List Decl)
                → declsIntLits (xs ++ ys) ≡ declsIntLits xs ++ declsIntLits ys
declsIntLits-++ []       ys = refl
declsIntLits-++ (d ∷ xs) ys =
  trans (cong (declIntLits d ++_) (declsIntLits-++ xs ys))
        (sym (++-assoc (declIntLits d) (declsIntLits xs) (declsIntLits ys)))

inj₂-inj : ∀ {A B : Set} {x y : B} → (inj₂ {A = A} x) ≡ inj₂ y → x ≡ y
inj₂-inj refl = refl

inj₁≢inj₂ : ∀ {A B : Set} {e : A} {x : B} → inj₁ e ≡ inj₂ x → ⊥
inj₁≢inj₂ ()

resolveDecls-lits : ∀ (polys : List String) (um : UnaliasedMap) (am : AliasMap)
                      (modMap : ModuleMap) (ds ds' : List Decl)
                  → resolveDecls polys um am modMap ds ≡ inj₂ ds'
                  → declsIntLits ds' ≡ declsIntLits ds
resolveDecls-lits polys um am modMap [] ds' eq = cong declsIntLits (sym (inj₂-inj eq))

-- THE IMPORT CASE: `signaturesWithOwner` adds only `DSignature` decls, which
-- carry no literals, so the inlined prefix contributes `[]`.
resolveDecls-lits polys um am modMap (DImport imp ∷ rest) ds' eq
  with lookupModule modMap (Import.path imp)
... | nothing = ⊥-elim (inj₁≢inj₂ eq)
... | just (mkModule impDs)
      with resolveDecls polys um am modMap rest
         | resolveDecls-lits polys um am modMap rest
...      | inj₁ err    | _  = ⊥-elim (inj₁≢inj₂ eq)
...      | inj₂ tailDs | ih =
           trans (cong declsIntLits (sym (inj₂-inj eq)))
                 (trans (declsIntLits-++ (signaturesWithOwner (ownerOf imp) impDs) tailDs)
                        (trans (cong (_++ declsIntLits tailDs)
                                     (sigsWithOwner-lits (ownerOf imp) impDs))
                               (ih tailDs refl)))

-- ORDINARY DECL: `canonDecl` rewrites references and leaves literals alone.
resolveDecls-lits polys um am modMap (DTypeSig n t ∷ rest) ds' eq
  with resolveDecls polys um am modMap rest
     | resolveDecls-lits polys um am modMap rest
... | inj₁ err    | _  = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ tailDs | ih =
      trans (cong declsIntLits (sym (inj₂-inj eq)))
            (cong₂ _++_ (canonDecl-lits polys um am (DTypeSig n t))
                        (ih tailDs refl))

-- ORDINARY DECL: `canonDecl` rewrites references and leaves literals alone.
resolveDecls-lits polys um am modMap (DFunDef n a b ∷ rest) ds' eq
  with resolveDecls polys um am modMap rest
     | resolveDecls-lits polys um am modMap rest
... | inj₁ err    | _  = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ tailDs | ih =
      trans (cong declsIntLits (sym (inj₂-inj eq)))
            (cong₂ _++_ (canonDecl-lits polys um am (DFunDef n a b))
                        (ih tailDs refl))

-- ORDINARY DECL: `canonDecl` rewrites references and leaves literals alone.
resolveDecls-lits polys um am modMap (DSignature n o t e ∷ rest) ds' eq
  with resolveDecls polys um am modMap rest
     | resolveDecls-lits polys um am modMap rest
... | inj₁ err    | _  = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ tailDs | ih =
      trans (cong declsIntLits (sym (inj₂-inj eq)))
            (cong₂ _++_ (canonDecl-lits polys um am (DSignature n o t e))
                        (ih tailDs refl))

-- ORDINARY DECL: `canonDecl` rewrites references and leaves literals alone.
resolveDecls-lits polys um am modMap (DTypeAlias n ps t ∷ rest) ds' eq
  with resolveDecls polys um am modMap rest
     | resolveDecls-lits polys um am modMap rest
... | inj₁ err    | _  = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ tailDs | ih =
      trans (cong declsIntLits (sym (inj₂-inj eq)))
            (cong₂ _++_ (canonDecl-lits polys um am (DTypeAlias n ps t))
                        (ih tailDs refl))

------------------------------------------------------------------------
-- The statement the gate needs
------------------------------------------------------------------------

moduleIntLits≡decls : ∀ (ds : List Decl) → moduleIntLits (mkModule ds) ≡ declsIntLits ds
moduleIntLits≡decls []       = refl
moduleIntLits≡decls (d ∷ ds) = cong (declIntLits d ++_) (moduleIntLits≡decls ds)

-- | RESOLUTION PRESERVES `Int` LITERALS. The sibling of
-- `resolver-preserves-trace` / `-typing`: resolution does not change what the
-- gate looks at, so admissibility over the UN-resolved module and over the
-- RESOLVED one are the same statement — which is what lets the spec state it
-- over the former while the compiler checks the latter.
resolver-preserves-intLits : ∀ (mm : ModuleMap) (mU mR : Module)
                           → resolveImports mm mU ≡ inj₂ mR
                           → moduleIntLits mU ≡ moduleIntLits mR
resolver-preserves-intLits mm (mkModule ds) mR eq
  with resolveDecls (polyDefNames ds) (collectUnaliased mm ds) (collectAliases ds) mm ds
     | resolveDecls-lits (polyDefNames ds) (collectUnaliased mm ds) (collectAliases ds) mm ds
... | inj₁ err  | _  = ⊥-elim (inj₁≢inj₂ eq)
... | inj₂ ds'  | ih =
      trans (moduleIntLits≡decls ds)
            (trans (sym (ih ds' refl))
                   (trans (sym (moduleIntLits≡decls ds'))
                          (cong moduleIntLits (inj₂-inj eq))))
