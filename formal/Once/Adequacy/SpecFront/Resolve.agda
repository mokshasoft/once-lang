-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Resolve — the compiler's resolution of a body is
-- the Spec's (plan 0.121 §3.6, F2).
--
-- The two resolutions take the same decisions, in the same order — a binder,
-- a generator, an unaliased import, the own module (D136); `name@this`,
-- `name@alias` — over the same tables, and write every name alike (R11,
-- D330). Given a body (the compiler's expressions are the Spec's), its
-- resolution by the compiler, and the resolved body good (`ResolvedRefs`: it does not name
-- `main`, and its annotations are surface types), the Spec resolves the body
-- too, to an expression `RX`-related to the compiler's (`res-expr`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Resolve where

import Once.Spec.Surface.Syntax as O

open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String)

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

open import Once.Spec.Name using (CanonicalName; canonical; gen)
open import Once.Internal.Syntax as O using (RawExpr)
import Once.Spec.Surface.Syntax as S
open import Once.Internal.Resolution as LR
  using (UnaliasedMap; AliasMap; ResolvesVar; rv-binder; rv-gen; rv-import; rv-own;
         ResolvesExpr; re-var; re-this; re-qual; re-qual-path; re-res; re-app; re-lam; re-let; re-pair; re-destruct; re-annot;
         re-binop; re-unop; re-unit; re-int; re-float; ExpandsTo; ex-nil; ex-I; ex-other)
open import Once.Spec.Surface.Resolution as SR
  using (Env; env; Resolves; ResolvesName; rn-gen; rn-import; rn-own;
         r-local; r-name; r-this; r-qual; r-qual-path; r-res; r-app; r-lam; r-let; r-pair; r-destruct; r-unit; r-int; r-float;
         r-annot; r-binop; r-neg; Expands; fa-here; fa-there)
import Once.Spec.Surface.Resolution
open import Once.Internal.ResolvedRefs using (GoodName; GoodRefs)
open import Once.Adequacy.SpecFront.Expr
  using (RX; x-local; x-res; x-app; x-lam; x-let; x-pair; x-destruct; x-unit; x-int; x-float; x-annot; x-binop; x-neg)

------------------------------------------------------------------------
-- The tables
------------------------------------------------------------------------

private
  fa→ : ∀ {K V : Set} {x : K} {v : V} {t} → LR.FirstAt x v t → SR.FirstAt x v t
  fa→ LR.fa-here         = fa-here
  fa→ (LR.fa-there ne f) = fa-there ne (fa→ f)

  ex→ : ∀ {p p′} → ExpandsTo p p′ → Expands p p′
  ex→ ex-nil       = SR.ex-nil
  ex→ ex-I         = SR.ex-I
  ex→ (ex-other n) = SR.ex-other n

  -- a good name is not `main`
  good-main : ∀ {c} → GoodName c → c ≢ canonical ("main" ∷ [])
  good-main g e = g e refl

  -- a generator is a good name
  gen-good : ∀ x → GoodName (gen x)
  gen-good x ()

  x-good : ∀ {bound c} → GoodName c → RX bound (O.RResolved c) (S.RResolved c)
  x-good g = x-res (good-main g)

------------------------------------------------------------------------
-- An expression
------------------------------------------------------------------------

res-expr : ∀ {um am bound eU eC} → ResolvesExpr um am bound eU eC → GoodRefs eC
         → Σ[ eS ∈ S.Expr ] Resolves (env um am) bound eU eS × RX bound eC eS
res-expr (re-var (rv-binder m)) g = _ , r-local m , x-local m
res-expr (re-var (rv-gen nb gw)) g = _ , r-name nb (rn-gen gw) , x-good (gen-good _)
res-expr (re-var (rv-import nb ngw fa ex)) g = _ , r-name nb (rn-import ngw (fa→ fa) (ex→ ex)) , x-good g
res-expr (re-var (rv-own {x = x} nb ngw ab)) g = _ , r-name nb (rn-own ngw ab (g refl)) , x-good g
res-expr re-this g = _ , r-this (g refl) , x-good g
res-expr (re-qual na fa ex) g = _ , r-qual na (fa→ fa) (ex→ ex) , x-good g
res-expr (re-qual-path na ab) g = _ , r-qual-path na ab , x-good g
res-expr re-res g = _ , r-res , x-good g
res-expr (re-app f a) (gf , ga) =
  let (f′ , rf , xf) = res-expr f gf ; (a′ , ra , xa) = res-expr a ga in _ , r-app rf ra , x-app xf xa
res-expr (re-lam b) g = let (b′ , rb , xb) = res-expr b g in _ , r-lam rb , x-lam xb
res-expr (re-let e b) (ge , gb) =
  let (e′ , re′ , xe) = res-expr e ge ; (b′ , rb , xb) = res-expr b gb in _ , r-let re′ rb , x-let xe xb
res-expr (re-pair a b) (ga , gb) =
  let (a′ , ra , xa) = res-expr a ga ; (b′ , rb , xb) = res-expr b gb in _ , r-pair ra rb , x-pair xa xb
res-expr (re-destruct s l r) (gs , gl , gr) =
  let (s′ , rs , xs) = res-expr s gs ; (l′ , rl , xl) = res-expr l gl ; (r′ , rr , xr) = res-expr r gr
  in _ , r-destruct rs rl rr , x-destruct xs xl xr
res-expr (re-annot e) g = let (e′ , re′ , xe) = res-expr e g in _ , r-annot re′ , x-annot xe
res-expr (re-binop a b) (ga , gb) =
  let (a′ , ra , xa) = res-expr a ga ; (b′ , rb , xb) = res-expr b gb in _ , r-binop ra rb , x-binop xa xb
res-expr (re-unop e) g = let (e′ , re′ , xe) = res-expr e g in _ , r-neg re′ , x-neg xe
res-expr re-unit g = _ , r-unit , x-unit
res-expr re-int g = _ , r-int , x-int
res-expr re-float g = _ , r-float , x-float

------------------------------------------------------------------------
-- The declarations
------------------------------------------------------------------------

open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Once.Spec.Signature using (Signature)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (mkImport; Import)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
import Once.Spec.Surface.Program as SPr

-- The resolved declarations: the Spec's, related to the compiler's.
module Decls (Σ : Signature) where
  open import Once.Adequacy.SpecFront.Align Σ using (DR; dr-nil; dr-tsig; dr-def; dr-sig; dr-import; dr-alias)

  -- the definitions' resolved bodies are good (the resolver's check)
  res-decls : ∀ {mm um am dsU dsR ds′} → LR.ResolvesDecls mm um am dsU dsR → Pointwise DEmb dsU ds′
            → Σ[ dsR′ ∈ List S.Decl ] SPr.ResolvesDecls (env um am) ds′ dsR′ × DR dsR′ dsR
  res-decls LR.rds-nil [] = [] , SPr.rd-nil , dr-nil
  res-decls (LR.rds-cons LR.nim-fundef (LR.rd-fundef rb g) rds) (d-fundef ∷ pw) =
    let (e′ , re′ , rx) = res-expr rb g ; (ds′ , rd , dr) = res-decls rds pw
    in _ , SPr.rd-def re′ rd , dr-def rx dr
  res-decls (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) (d-typesig ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-tsig rd , dr-tsig dr
  res-decls (LR.rds-cons LR.nim-sig LR.rd-signature rds) (d-signature ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-sig rd , dr-sig dr
  res-decls (LR.rds-cons LR.nim-alias LR.rd-typealias rds) (d-alias ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-alias rd , dr-alias dr
  res-decls (LR.rds-import _ rds) (d-import ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-import rd , dr-import dr

------------------------------------------------------------------------
-- The tables
------------------------------------------------------------------------

open import Once.Parser.Module.Core using (Module; mkModule)
import Data.List
import Data.Maybe
open import Once.Parser.Module.Resolve using (ModuleMap; collectAliases; collectUnaliased; sigNames; lookupModule)
open import Once.Adequacy.ResolveBridge using (lookupMod-complete)
open import Relation.Binary.PropositionalEquality using (trans; cong₂; subst)

open import Once.Adequacy.SpecFront.ModRel using (ModRel; find)

-- its exported names
names-eq : ∀ {ds ds′} → Pointwise DEmb ds ds′ → sigNames ds ≡ SR.exports ds′
names-eq [] = refl
names-eq (d-typesig ∷ pw)   = names-eq pw
names-eq (d-fundef ∷ pw)  = names-eq pw
names-eq (d-signature ∷ pw) = cong (_ ∷_) (names-eq pw)
names-eq (d-alias ∷ pw)     = names-eq pw
names-eq (d-import ∷ pw)    = names-eq pw

map-path : ∀ (p : List String) xs → Data.List.map (λ n → (n , p)) xs ≡ SR.mapPath p xs
map-path p []       = refl
map-path p (x ∷ xs) = cong (_ ∷_) (map-path p xs)

-- The aliased imports.
aliases-eq : ∀ {dsU ds′} → Pointwise DEmb dsU ds′ → collectAliases dsU ≡ SR.aliases ds′
aliases-eq [] = refl
aliases-eq (d-typesig ∷ pw)   = aliases-eq pw
aliases-eq (d-fundef ∷ pw)  = aliases-eq pw
aliases-eq (d-signature ∷ pw) = aliases-eq pw
aliases-eq (d-alias ∷ pw)     = aliases-eq pw
aliases-eq (d-import {a = just a} ∷ pw) = cong (_ ∷_) (aliases-eq pw)
aliases-eq (d-import {a = nothing} ∷ pw) = aliases-eq pw

-- The unaliased imports: every module an import names is found (the
-- compiler's resolution looked it up).
unaliased-of : ∀ {mm mm′ um am dsU dsR ds′} → ModRel mm mm′ → LR.ResolvesDecls mm um am dsU dsR → Pointwise DEmb dsU ds′
             → SR.Unaliased mm′ ds′ (collectUnaliased mm dsU)
unaliased-of mr LR.rds-nil [] = SR.un-nil
unaliased-of mr (LR.rds-cons LR.nim-fundef _ rds) (d-fundef ∷ pw) = SR.un-other SR.nu-def (unaliased-of mr rds pw)
unaliased-of mr (LR.rds-cons LR.nim-typesig _ rds) (d-typesig ∷ pw) = SR.un-other SR.nu-tsig (unaliased-of mr rds pw)
unaliased-of mr (LR.rds-cons LR.nim-sig _ rds) (d-signature ∷ pw) = SR.un-other SR.nu-sig (unaliased-of mr rds pw)
unaliased-of mr (LR.rds-cons LR.nim-alias _ rds) (d-alias ∷ pw) = SR.un-other SR.nu-alias (unaliased-of mr rds pw)
unaliased-of mr (LR.rds-import fa rds) (d-import {a = just a} ∷ pw) = SR.un-other SR.nu-aliased (unaliased-of mr rds pw)
unaliased-of {mm = mm} {mm′} mr (LR.rds-import {impDs = impDs} {ds = rest} fa rds) (d-import {p = p} {a = nothing} ∷ pw)
  rewrite lookupMod-complete mm p (mkModule impDs) fa =
  let (ds″ , fa′ , pw′) = find mr fa in
  subst (λ u → SR.Unaliased mm′ (S.DImport (S.mkImport p nothing) ∷ _) (u Data.List.++ collectUnaliased mm rest))
        (sym (trans (cong (Data.List.map (λ n → (n , p))) (names-eq pw′)) (map-path p (SR.exports ds″))))
        (SR.un-import fa′ (unaliased-of mr rds pw))
