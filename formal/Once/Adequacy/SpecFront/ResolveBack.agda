-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ResolveBack — the Spec's resolution of a body is
-- the compiler's (plan 0.121 `complete`; the converse of `Resolve`).
--
-- The two resolutions take the same decisions over the same tables and
-- write every name alike (D330). Given a body as written in both grammars
-- (`Emb`), the Spec's resolution of it, and the body as written (no
-- resolved name, `SpecGrammar.Written`), the compiler resolves it too, to
-- an expression `RX`-related to the Spec's, and the result passes the
-- resolver's check (`GoodRefs`): the Spec names `main` nowhere, and a name
-- an import gives has a path of at least one part (`PathsNE`), so it is no
-- own name (`res-expr←`). The tables are the compiler's (`unaliased-eq`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.ResolveBack where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Once.Spec.Name using (CanonicalName; canonical; gen)
open import Once.Internal.Syntax as O using (RawExpr)
import Once.Spec.Surface.Syntax as S
import Once.Internal.Resolution as LR
import Once.Spec.Surface.Resolution as SR
open import Once.Internal.Resolution
  using (UnaliasedMap; AliasMap; ResolvesExpr; re-var; re-this; re-qual; re-qual-path; re-res; re-app; re-lam; re-let;
         re-pair; re-destruct; re-annot; re-binop; re-unop; re-unit; re-int; re-float; rv-binder; rv-gen; rv-import; rv-own)
open import Once.Spec.Surface.Resolution
  using (Env; env; Resolves; rn-gen; rn-import; rn-own; r-local; r-name; r-this; r-qual; r-qual-path; r-res; r-app; r-lam;
         r-let; r-pair; r-destruct; r-unit; r-int; r-float; r-annot; r-binop; r-neg)
open import Once.Internal.ResolvedRefs using (GoodName; GoodRefs)
open import Once.Parser.Module.Core using (Module; mkModule; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport; mkImport)
open import Once.Parser.Module.Resolve using (ModuleMap; collectUnaliased; collectAliases; lookupModule)
open import Once.Adequacy.ResolveBridge using (lookupMod-complete)
open import Once.Adequacy.SpecGrammar.Expr using (Emb; e-var; e-qual; e-res; e-app; e-lam; e-let; e-pair; e-destruct; e-unit;
  e-int; e-float; e-annot; e-binop; e-neg)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
open import Once.Adequacy.SpecGrammar.Written using (Written)
open import Once.Adequacy.SpecFront.Expr
  using (RX; x-local; x-res; x-app; x-lam; x-let; x-pair; x-destruct; x-unit; x-int; x-float; x-annot; x-binop; x-neg)
open import Once.Adequacy.SpecFront.ModRel using (ModRel)
open import Once.Adequacy.SpecFront.Resolve using (names-eq; map-path)

------------------------------------------------------------------------
-- The tables
------------------------------------------------------------------------

-- Every path in a table has a part.
PathsNE : List (String × List String) → Set
PathsNE = All (λ q → proj₂ q ≢ [])

private
  fa← : ∀ {K V : Set} {x : K} {v : V} {t} → SR.FirstAt x v t → LR.FirstAt x v t
  fa← SR.fa-here         = LR.fa-here
  fa← (SR.fa-there ne f) = LR.fa-there ne (fa← f)

  ex← : ∀ {p p′} → SR.Expands p p′ → LR.ExpandsTo p p′
  ex← SR.ex-nil       = LR.ex-nil
  ex← SR.ex-I         = LR.ex-I
  ex← (SR.ex-other n) = LR.ex-other n

  at-ne : ∀ {x p t} → PathsNE t → SR.FirstAt x p t → p ≢ []
  at-ne (n ∷ _) SR.fa-here        = n
  at-ne (_ ∷ a) (SR.fa-there _ f) = at-ne a f

  ex-ne : ∀ {p p′} → SR.Expands p p′ → p ≢ [] → p′ ≢ []
  ex-ne SR.ex-nil       n = n
  ex-ne SR.ex-I         n ()
  ex-ne (SR.ex-other _) n ()

  -- a name of two or more parts is no own name
  good-long : ∀ (p : List String) x → p ≢ [] → GoodName (canonical (p ++ x ∷ []))
  good-long []           x n = ⊥-elim (n refl)
  good-long (_ ∷ [])     x n ()
  good-long (_ ∷ _ ∷ _)  x n ()

  good-gen : ∀ x → GoodName (gen x)
  good-gen x ()

  good-path : ∀ a x → GoodName (canonical (a ∷ x ∷ []))
  good-path a x ()

  good-own : ∀ {x} → x ≢ "main" → GoodName (canonical (x ∷ []))
  good-own xm refl = xm

  x-good : ∀ {bound c} → GoodName c → RX bound (O.RResolved c) (S.RResolved c)
  x-good g = x-res (λ e → g e refl)

-- A module the Spec finds is one the compiler finds, written alike.
find← : ∀ {mm mm′ p ds′} → ModRel mm mm′ → SR.FirstAt p (S.mkModule ds′) mm′
      → Σ[ ds ∈ List Decl ] LR.FirstAt p (mkModule ds) mm × Pointwise DEmb ds ds′
find← ((refl , pw) ∷ _) SR.fa-here = _ , LR.fa-here , pw
find← ((refl , _) ∷ mr) (SR.fa-there ne fa) = let (ds , fa′ , pw) = find← mr fa in ds , LR.fa-there ne fa′ , pw

-- The Spec's unaliased imports are the compiler's.
unaliased-eq : ∀ {mm mm′ dsU ds′ u} → ModRel mm mm′ → Pointwise DEmb dsU ds′ → SR.Unaliased mm′ ds′ u
             → u ≡ collectUnaliased mm dsU
unaliased-eq mr [] SR.un-nil = refl
unaliased-eq {mm} mr (d-import {p = p} {a = nothing} ∷ pw) (SR.un-import {ds′ = ds″} fa un)
  with find← mr fa
... | dsc , fa′ , pw′ with lookupModule mm p | lookupMod-complete mm p (mkModule dsc) fa′
...   | .(just (mkModule dsc)) | refl =
  cong₂ _++_ (sym (trans (cong (Data.List.map (λ n → (n , p))) (names-eq pw′)) (map-path p (SR.exports ds″))))
             (unaliased-eq mr pw un)
unaliased-eq mr (d-import {a = just _} ∷ pw) (SR.un-other SR.nu-aliased un) = unaliased-eq mr pw un
unaliased-eq mr (d-typesig ∷ pw)   (SR.un-other SR.nu-tsig un)  = unaliased-eq mr pw un
unaliased-eq mr (d-fundef _ ∷ pw)  (SR.un-other SR.nu-def un)   = unaliased-eq mr pw un
unaliased-eq mr (d-signature ∷ pw) (SR.un-other SR.nu-sig un)   = unaliased-eq mr pw un
unaliased-eq mr (d-alias ∷ pw)     (SR.un-other SR.nu-alias un) = unaliased-eq mr pw un

------------------------------------------------------------------------
-- An expression
------------------------------------------------------------------------

res-expr← : ∀ {um am bound eU e′ eS} → PathsNE um → PathsNE am
          → Resolves (env um am) bound e′ eS → Emb eU e′ → Written e′
          → Σ[ eC ∈ RawExpr ] ResolvesExpr um am bound eU eC × RX bound eC eS × GoodRefs eC
res-expr← nu na (r-local m) e-var w = _ , re-var (rv-binder m) , x-local m , tt
res-expr← nu na (r-name nb (rn-gen gw)) e-var w = _ , re-var (rv-gen nb gw) , x-good (good-gen _) , good-gen _
res-expr← nu na (r-name nb (rn-import {x = x} {p} {p′} ngw fa ex)) e-var w =
  let g = good-long p′ x (ex-ne ex (at-ne nu fa))
  in _ , re-var (rv-import nb ngw (fa← fa) (ex← ex)) , x-good g , g
res-expr← nu na (r-name nb (rn-own ngw ab xm)) e-var w = _ , re-var (rv-own nb ngw ab) , x-good (good-own xm) , good-own xm
res-expr← nu na (r-this xm) e-qual w = _ , re-this , x-good (good-own xm) , good-own xm
res-expr← nu na (r-qual {x = x} {p′ = p′} na′ fa ex) e-qual w =
  let g = good-long p′ x (ex-ne ex (at-ne na fa))
  in _ , re-qual na′ (fa← fa) (ex← ex) , x-good g , g
res-expr← nu na (r-qual-path {x = x} {a} na′ ab) e-qual w = _ , re-qual-path na′ ab , x-good (good-path a x) , good-path a x
res-expr← nu na r-res e-res ()
res-expr← nu na (r-app rf ra) (e-app ef ea) (wf , wa) =
  let (f , df , xf , gf) = res-expr← nu na rf ef wf ; (a , da , xa , ga) = res-expr← nu na ra ea wa
  in _ , re-app df da , x-app xf xa , gf , ga
res-expr← nu na (r-lam rb) (e-lam eb) w =
  let (b , db , xb , gb) = res-expr← nu na rb eb w in _ , re-lam db , x-lam xb , gb
res-expr← nu na (r-let re rb) (e-let ee eb) (we , wb) =
  let (e , de , xe , ge) = res-expr← nu na re ee we ; (b , db , xb , gb) = res-expr← nu na rb eb wb
  in _ , re-let de db , x-let xe xb , ge , gb
res-expr← nu na (r-pair ra rb) (e-pair ea eb) (wa , wb) =
  let (a , da , xa , ga) = res-expr← nu na ra ea wa ; (b , db , xb , gb) = res-expr← nu na rb eb wb
  in _ , re-pair da db , x-pair xa xb , ga , gb
res-expr← nu na (r-destruct rs rl rr) (e-destruct es el er) (ws , wl , wr) =
  let (s , ds , xs , gs) = res-expr← nu na rs es ws ; (l , dl , xl , gl) = res-expr← nu na rl el wl
      (r , dr , xr , gr) = res-expr← nu na rr er wr
  in _ , re-destruct ds dl dr , x-destruct xs xl xr , gs , gl , gr
res-expr← nu na (r-annot re) (e-annot rf ee) w =
  let (e , de , xe , ge) = res-expr← nu na re ee w in _ , re-annot de , x-annot rf xe , rf , ge
res-expr← nu na (r-binop ra rb) (e-binop ea eb) (wa , wb) =
  let (a , da , xa , ga) = res-expr← nu na ra ea wa ; (b , db , xb , gb) = res-expr← nu na rb eb wb
  in _ , re-binop da db , x-binop xa xb , ga , gb
res-expr← nu na (r-neg re) (e-neg ee) w =
  let (e , de , xe , ge) = res-expr← nu na re ee w in _ , re-unop de , x-neg xe , ge
res-expr← nu na r-unit e-unit w = _ , re-unit , x-unit , tt
res-expr← nu na r-int e-int w = _ , re-int , x-int , tt
res-expr← nu na r-float e-float w = _ , re-float , x-float , tt

------------------------------------------------------------------------
-- The declarations
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Parser.Module.Core using (Import)
open import Once.Parser.Module.Resolve using (signaturesWithOwner; ownerOf)
open import Once.Adequacy.SpecGrammar.Written using (DeclWritten)
import Once.Spec.Surface.Program as SPr
import Once.Adequacy.SpecFront.Resolve

module Decls (Σ : Signature) where
  open import Once.Adequacy.SpecFront.Align Σ using (DR; dr-nil; dr-tsig; dr-def; dr-sig; dr-import; dr-alias; ImportedSig)
  open Once.Adequacy.SpecFront.Resolve.Decls Σ using (owned)

  private
    owned-at : ∀ (i : Import) ds → All ImportedSig (signaturesWithOwner (ownerOf i) ds)
    owned-at (mkImport p (just _)) ds = owned _ ds
    owned-at (mkImport p nothing)  ds = owned _ ds

  -- every import's module is found (the Spec's signature found it)
  res-decls← : ∀ {mm mm′ um am dsU ds′ dsR′ Σᵢ} → ModRel mm mm′ → PathsNE um → PathsNE am
             → SPr.ResolvesDecls (env um am) ds′ dsR′ → Pointwise DEmb dsU ds′ → All DeclWritten ds′
             → SPr.Imported mm′ ds′ Σᵢ
             → Σ[ dsR ∈ List Decl ] LR.ResolvesDecls mm um am dsU dsR × DR dsR′ dsR
  res-decls← mr nu na SPr.rd-nil [] [] SPr.im-nil = [] , LR.rds-nil , dr-nil
  res-decls← mr nu na (SPr.rd-def re rd) (d-fundef em ∷ pw) (w ∷ ws) (SPr.im-other SPr.ni-def im) =
    let (e , de , xe , g) = res-expr← nu na re em w ; (ds , rds , dr) = res-decls← mr nu na rd pw ws im
    in _ , LR.rds-cons LR.nim-fundef (LR.rd-fundef de g) rds , dr-def xe dr
  res-decls← mr nu na (SPr.rd-other SPr.nf-tsig rd) (d-typesig ∷ pw) (_ ∷ ws) (SPr.im-other SPr.ni-tsig im) =
    let (ds , rds , dr) = res-decls← mr nu na rd pw ws im in _ , LR.rds-cons LR.nim-typesig LR.rd-typesig rds , dr-tsig dr
  res-decls← mr nu na (SPr.rd-other SPr.nf-sig rd) (d-signature ∷ pw) (_ ∷ ws) (SPr.im-other SPr.ni-sig im) =
    let (ds , rds , dr) = res-decls← mr nu na rd pw ws im in _ , LR.rds-cons LR.nim-sig LR.rd-signature rds , dr-sig dr
  res-decls← mr nu na (SPr.rd-other SPr.nf-alias rd) (d-alias ∷ pw) (_ ∷ ws) (SPr.im-other SPr.ni-alias im) =
    let (ds , rds , dr) = res-decls← mr nu na rd pw ws im in _ , LR.rds-cons LR.nim-alias LR.rd-typealias rds , dr-alias dr
  res-decls← mr nu na (SPr.rd-other SPr.nf-import rd) (d-import {p = p} {a = a} ∷ pw) (_ ∷ ws) (SPr.im-import fa _ _ im) =
    let (dsc , fa′ , _) = find← mr fa ; (ds , rds , dr) = res-decls← mr nu na rd pw ws im
    in _ , LR.rds-import fa′ rds , dr-import (owned-at (mkImport p a) dsc) dr
