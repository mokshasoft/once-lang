-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Resolve — the compiler's resolution of a body is
-- the Spec's (plan 0.121 §3.6, F2).
--
-- The two resolutions take the same decisions, in the same order — a binder,
-- a generator, an unaliased import, the own module (D136); `name@this`,
-- `name@alias` — over the same tables. They write one case differently: the
-- compiler keeps a reference to an own POLYMORPHIC definition bare, where the
-- Spec writes `canonical [x]` (`RX`'s `x-own`). Given a body as written in
-- both grammars (`Emb`), its resolution by the compiler, and the resolved
-- body good (`ResolvedRefs`: it names neither `main` nor an own polymorphic
-- definition canonically, and its annotations are surface types), the Spec
-- resolves the body too, to an expression `RX`-related to the compiler's
-- (`res-expr`).
------------------------------------------------------------------------

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Relation.Nullary using (¬_)

module Once.Adequacy.SpecFront.Resolve
  (ps : List String)
  -- the entry is not a polymorphic definition
  (main∉ps : ¬ ("main" ∈ ps))
  where

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

open import Once.Spec.Name using (CanonicalName; canonical; gen)
open import Once.Lang.Syntax as O using (RawExpr)
import Once.Spec.Surface.Syntax as S
open import Once.Lang.Resolution as LR
  using (UnaliasedMap; AliasMap; ResolvesVar; rv-binder; rv-gen; rv-import; rv-own-poly; rv-own;
         ResolvesExpr; re-var; re-this; re-qual; re-qual-path; re-res; re-app; re-lam; re-let; re-pair; re-destruct; re-annot;
         re-binop; re-unop; re-ana; re-unit; re-int; re-float; ExpandsTo; ex-nil; ex-I; ex-other)
open import Once.Spec.Surface.Resolution as SR
  using (Env; env; Resolves; ResolvesName; rn-gen; rn-import; rn-own;
         r-local; r-name; r-this; r-qual; r-qual-path; r-res; r-app; r-lam; r-let; r-pair; r-destruct; r-unit; r-int; r-float;
         r-annot; r-binop; r-neg; Expands; fa-here; fa-there)
import Once.Spec.Surface.Resolution
open import Once.Lang.ResolvedRefs using (GoodName; GoodRefs)
open import Once.Adequacy.SpecGrammar.Expr using (Emb; e-var; e-qual; e-res; e-app; e-lam; e-let; e-pair; e-destruct; e-unit;
  e-int; e-float; e-annot; e-binop; e-neg)
open import Once.Adequacy.SpecFront.Expr
  using (RX; NotOwnPoly; x-local; x-own; x-res; x-app; x-lam; x-let; x-pair; x-destruct; x-unit; x-int; x-float; x-annot; x-binop; x-neg)

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

  -- a good name is no own polymorphic definition's, and not `main`
  good-nop : ∀ {c} → GoodName ps c → NotOwnPoly ps c
  good-nop g e = proj₂ (g e)

  good-main : ∀ {c} → GoodName ps c → c ≢ canonical ("main" ∷ [])
  good-main g e = proj₁ (g e) refl

  -- a generator is a good name
  gen-good : ∀ x → GoodName ps (gen x)
  gen-good x ()

  x-good : ∀ {bound c} → GoodName ps c → RX ps bound (O.RResolved c) (S.RResolved c)
  x-good g = x-res (good-nop g) (good-main g)

------------------------------------------------------------------------
-- An expression
------------------------------------------------------------------------

res-expr : ∀ {um am bound eU eC eU′} → ResolvesExpr ps um am bound eU eC → Emb eU eU′ → GoodRefs ps eC
         → Σ[ eS ∈ S.Expr ] Resolves (env um am) bound eU′ eS × RX ps bound eC eS
res-expr (re-var (rv-binder m)) e-var g = _ , r-local m , x-local m
res-expr (re-var (rv-gen nb gw)) e-var g = _ , r-name nb (rn-gen gw) , x-good (gen-good _)
res-expr (re-var (rv-import nb ngw fa ex)) e-var g = _ , r-name nb (rn-import ngw (fa→ fa) (ex→ ex)) , x-good g
res-expr {bound = bound} (re-var (rv-own-poly {x = x} nb ngw ab x∈)) e-var g =
  _ , r-name nb (rn-own ngw ab (λ e → main∉ps (subst′ e x∈))) , x-own nb x∈
  where
    subst′ : x ≡ "main" → x ∈ ps → "main" ∈ ps
    subst′ refl m = m
res-expr (re-var (rv-own {x = x} nb ngw ab x∉)) e-var g = _ , r-name nb (rn-own ngw ab (proj₁ (g refl))) , x-good g
res-expr re-this e-qual g = _ , r-this (proj₁ (g refl)) , x-good g
res-expr (re-qual na fa ex) e-qual g = _ , r-qual na (fa→ fa) (ex→ ex) , x-good g
res-expr (re-qual-path na ab) e-qual g = _ , r-qual-path na ab , x-good g
res-expr re-res e-res g = _ , r-res , x-good g
res-expr (re-app f a) (e-app ef ea) (gf , ga) =
  let (f′ , rf , xf) = res-expr f ef gf ; (a′ , ra , xa) = res-expr a ea ga in _ , r-app rf ra , x-app xf xa
res-expr (re-lam b) (e-lam eb) g = let (b′ , rb , xb) = res-expr b eb g in _ , r-lam rb , x-lam xb
res-expr (re-let e b) (e-let ee eb) (ge , gb) =
  let (e′ , re′ , xe) = res-expr e ee ge ; (b′ , rb , xb) = res-expr b eb gb in _ , r-let re′ rb , x-let xe xb
res-expr (re-pair a b) (e-pair ea eb) (ga , gb) =
  let (a′ , ra , xa) = res-expr a ea ga ; (b′ , rb , xb) = res-expr b eb gb in _ , r-pair ra rb , x-pair xa xb
res-expr (re-destruct s l r) (e-destruct es el er) (gs , gl , gr) =
  let (s′ , rs , xs) = res-expr s es gs ; (l′ , rl , xl) = res-expr l el gl ; (r′ , rr , xr) = res-expr r er gr
  in _ , r-destruct rs rl rr , x-destruct xs xl xr
res-expr (re-annot e) (e-annot ee) (rf , g) = let (e′ , re′ , xe) = res-expr e ee g in _ , r-annot re′ , x-annot rf xe
res-expr (re-binop a b) (e-binop ea eb) (ga , gb) =
  let (a′ , ra , xa) = res-expr a ea ga ; (b′ , rb , xb) = res-expr b eb gb in _ , r-binop ra rb , x-binop xa xb
res-expr (re-unop e) (e-neg ee) g = let (e′ , re′ , xe) = res-expr e ee g in _ , r-neg re′ , x-neg xe
res-expr re-unit e-unit g = _ , r-unit , x-unit
res-expr re-int e-int g = _ , r-int , x-int
res-expr re-float e-float g = _ , r-float , x-float

------------------------------------------------------------------------
-- The declarations
------------------------------------------------------------------------

open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Once.Spec.Signature using (Signature)
open import Once.Parser.Module.Core using (Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkImport; Import)
open import Once.Parser.Module.Resolve using (signaturesWithOwner; ownerOf)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
import Once.Spec.Surface.Program as SPr

private
  owner-just : ∀ (i : Import) → Σ[ o ∈ List String ] ownerOf i ≡ just o
  owner-just (mkImport p (just _)) = _ , refl
  owner-just (mkImport p nothing)  = _ , refl

-- The resolved declarations: the Spec's, related to the compiler's.
module Decls (Σ : Signature) where
  open import Once.Adequacy.SpecFront.Align Σ ps using (DR; dr-nil; dr-tsig; dr-def; dr-sig; dr-import; dr-alias; ImportedSig)

  private
    -- an import's signatures are owned by it
    owned : ∀ (o : List String) (ds : List Decl) → All ImportedSig (signaturesWithOwner (just o) ds)
    owned o [] = []
    owned o (DSignature x _ T ∷ ds) = (x , o , T , refl) ∷ owned o ds
    owned o (DTypeSig _ _ ∷ ds) = owned o ds
    owned o (DFunDef _ _ ∷ ds) = owned o ds
    owned o (DTypeAlias _ _ _ ∷ ds) = owned o ds
    owned o (DImport _ ∷ ds) = owned o ds

  -- the definitions' resolved bodies are good (the resolver's check)
  res-decls : ∀ {mm um am dsU dsR ds′} → LR.ResolvesDecls mm ps um am dsU dsR → Pointwise DEmb dsU ds′
            → Σ[ dsR′ ∈ List S.Decl ] SPr.ResolvesDecls (env um am) ds′ dsR′ × DR dsR′ dsR
  res-decls LR.rds-nil [] = [] , SPr.rd-nil , dr-nil
  res-decls (LR.rds-cons LR.nim-fundef (LR.rd-fundef rb g) rds) (d-fundef em ∷ pw) =
    let (e′ , re′ , rx) = res-expr rb em g ; (ds′ , rd , dr) = res-decls rds pw
    in _ , SPr.rd-def re′ rd , dr-def rx dr
  res-decls (LR.rds-cons LR.nim-typesig LR.rd-typesig rds) (d-typesig ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-tsig rd , dr-tsig dr
  res-decls (LR.rds-cons LR.nim-sig LR.rd-signature rds) (d-signature ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-sig rd , dr-sig dr
  res-decls (LR.rds-cons LR.nim-alias LR.rd-typealias rds) (d-alias ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw in _ , SPr.rd-other SPr.nf-alias rd , dr-alias dr
  res-decls (LR.rds-import {imp = imp} {impDs = impDs} fa rds) (d-import ∷ pw) =
    let (ds′ , rd , dr) = res-decls rds pw ; (o , eo) = owner-just imp
    in _ , SPr.rd-other SPr.nf-import rd
       , dr-import (subst-own eo (owned o impDs)) dr
    where
      subst-own : ∀ {o : List String} {mo} → mo ≡ just o → All ImportedSig (signaturesWithOwner (just o) impDs)
                → All ImportedSig (signaturesWithOwner mo impDs)
      subst-own refl a = a

------------------------------------------------------------------------
-- The tables
------------------------------------------------------------------------

open import Once.Parser.Module.Core using (Module; mkModule)
import Data.List
import Data.Maybe
open import Once.Parser.Module.Resolve using (ModuleMap; collectAliases; collectUnaliased; sigNames; lookupModule)
open import Once.Adequacy.ResolveBridge using (lookupMod-complete)
open import Relation.Binary.PropositionalEquality using (trans; cong₂; subst)

-- The module maps: the same paths, each module's declarations as written in
-- both grammars.
ModRel : ModuleMap → SR.ModuleMap → Set
ModRel = Pointwise (λ q q′ → (proj₁ q ≡ proj₁ q′) × Pointwise DEmb (Module.decls (proj₂ q)) (S.Module.decls (proj₂ q′)))

private
  -- a module the compiler finds, the Spec finds at the same path
  find : ∀ {mm mm′ p ds} → ModRel mm mm′ → LR.FirstAt p (mkModule ds) mm
       → Σ[ ds′ ∈ List S.Decl ] SR.FirstAt p (S.mkModule ds′) mm′ × Pointwise DEmb ds ds′
  find ((refl , pw) ∷ _) LR.fa-here = _ , SR.fa-here , pw
  find ((refl , _) ∷ mr) (LR.fa-there ne fa) = let (ds′ , fa′ , pw) = find mr fa in ds′ , SR.fa-there ne fa′ , pw

  -- its exported names
  names-eq : ∀ {ds ds′} → Pointwise DEmb ds ds′ → sigNames ds ≡ SR.exports ds′
  names-eq [] = refl
  names-eq (d-typesig ∷ pw)   = names-eq pw
  names-eq (d-fundef _ ∷ pw)  = names-eq pw
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
aliases-eq (d-fundef _ ∷ pw)  = aliases-eq pw
aliases-eq (d-signature ∷ pw) = aliases-eq pw
aliases-eq (d-alias ∷ pw)     = aliases-eq pw
aliases-eq (d-import {a = just a} ∷ pw) = cong (_ ∷_) (aliases-eq pw)
aliases-eq (d-import {a = nothing} ∷ pw) = aliases-eq pw

-- The unaliased imports: every module an import names is found (the
-- compiler's resolution looked it up).
unaliased-of : ∀ {mm mm′ um am dsU dsR ds′} → ModRel mm mm′ → LR.ResolvesDecls mm ps um am dsU dsR → Pointwise DEmb dsU ds′
             → SR.Unaliased mm′ ds′ (collectUnaliased mm dsU)
unaliased-of mr LR.rds-nil [] = SR.un-nil
unaliased-of mr (LR.rds-cons LR.nim-fundef _ rds) (d-fundef _ ∷ pw) = SR.un-other SR.nu-def (unaliased-of mr rds pw)
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
