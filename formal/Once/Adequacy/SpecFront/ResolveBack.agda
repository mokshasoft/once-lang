-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ResolveBack — the Spec's resolution of a body is
-- the compiler's (plan 0.121 `complete`; the converse of `Resolve`).
--
-- The two resolutions take the same decisions over the same tables and
-- write every name alike (D330). Given a body (the compiler's expressions are
-- the Spec's), the Spec's resolution of it, and the body as written (no
-- resolved name, `SpecGrammar.Written`), the compiler resolves it too, to
-- an expression `RX`-related to the Spec's, and the result passes the
-- resolver's check (`GoodRefs`): the Spec names `main` nowhere, and a name
-- an import gives has a path of at least one part (`PathsNE`), so it is no
-- own name (`res-expr←`). The tables are the compiler's (`unaliased-eq`).
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.ResolveBack where

import Once.Spec.Surface.Syntax as O

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Once.Spec.Name using (CanonicalName; canonical; gen)
open import Once.Spec.Surface.Syntax using (Expr)
import Once.Spec.Surface.Syntax as S
import Once.Parser.Relation.Resolution as LR
import Once.Spec.Surface.Resolution as SR
open import Once.Parser.Relation.Resolution
  using (UnaliasedMap; AliasMap; ResolvesExpr; re-var; re-this; re-qual; re-qual-path; re-res; re-app; re-lam; re-let;
         re-pair; re-destruct; re-annot; re-binop; re-unop; re-unit; re-int; re-float; rv-binder; rv-gen; rv-import; rv-own)
open import Once.Spec.Surface.Resolution
  using (Env; env; Resolves; rn-gen; rn-import; rn-own; r-local; r-name; r-this; r-qual; r-qual-path; r-res; r-app; r-lam;
         r-let; r-pair; r-destruct; r-unit; r-int; r-float; r-annot; r-binop; r-neg)
open import Once.ResolvedRefs using (GoodName; GoodRefs)
open import Once.Spec.Surface.Syntax using (Module; mkModule; Decl; DTypeSig; DFunDef; DSignature; DTypeAlias; DImport)
open import Once.Spec.Surface.Syntax using (mkImport)
open import Once.Parser.Module.Resolve using (ModuleMap; collectUnaliased; collectAliases; lookupModule)
open import Once.Adequacy.ResolveBridge using (lookupMod-complete)
open import Once.Adequacy.SpecGrammar.Written using (Written)
open import Once.Adequacy.SpecFront.Expr
  using (RX; x-local; x-res; x-app; x-lam; x-let; x-pair; x-destruct; x-unit; x-int; x-float; x-annot; x-binop; x-neg)
open import Once.Adequacy.SpecFront.Resolve using (names-eq; map-path)

------------------------------------------------------------------------
-- The tables
------------------------------------------------------------------------

-- Every path in a table has a part.
PathsNE : List (String × List String) → Set
PathsNE = All (λ q → proj₂ q ≢ [])

private

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

-- The Spec's unaliased imports are the compiler's.
unaliased-eq : ∀ {mm dsU u} → SR.Unaliased mm dsU u → u ≡ collectUnaliased mm dsU
unaliased-eq SR.un-nil = refl
unaliased-eq {mm} (SR.un-import {p = p} {ds′ = ds″} fa un)
  with lookupModule mm p | lookupMod-complete mm p (mkModule ds″) fa
... | .(just (mkModule ds″)) | refl =
  cong₂ _++_ (sym (trans (cong (Data.List.map (λ n → (n , p))) (names-eq ds″)) (map-path p (SR.exports ds″))))
             (unaliased-eq un)
unaliased-eq (SR.un-other SR.nu-aliased un) = unaliased-eq un
unaliased-eq (SR.un-other SR.nu-tsig un)    = unaliased-eq un
unaliased-eq (SR.un-other SR.nu-def un)     = unaliased-eq un
unaliased-eq (SR.un-other SR.nu-sig un)     = unaliased-eq un
unaliased-eq (SR.un-other SR.nu-alias un)   = unaliased-eq un

------------------------------------------------------------------------
-- An expression
------------------------------------------------------------------------

res-expr← : ∀ {um am bound eU eS} → PathsNE um → PathsNE am
          → Resolves (env um am) bound eU eS → Written eU
          → Σ[ eC ∈ Expr ] ResolvesExpr um am bound eU eC × RX bound eC eS × GoodRefs eC
res-expr← nu na (r-local m) w = _ , re-var (rv-binder m) , x-local m , tt
res-expr← nu na (r-name nb (rn-gen gw)) w = _ , re-var (rv-gen nb gw) , x-good (good-gen _) , good-gen _
res-expr← nu na (r-name nb (rn-import {x = x} {p} {p′} ngw fa ex)) w =
  let g = good-long p′ x (ex-ne ex (at-ne nu fa))
  in _ , re-var (rv-import nb ngw fa ex) , x-good g , g
res-expr← nu na (r-name nb (rn-own ngw ab xm)) w = _ , re-var (rv-own nb ngw ab) , x-good (good-own xm) , good-own xm
res-expr← nu na (r-this xm) w = _ , re-this , x-good (good-own xm) , good-own xm
res-expr← nu na (r-qual {x = x} {p′ = p′} na′ fa ex) w =
  let g = good-long p′ x (ex-ne ex (at-ne na fa))
  in _ , re-qual na′ fa ex , x-good g , g
res-expr← nu na (r-qual-path {x = x} {a} na′ ab) w = _ , re-qual-path na′ ab , x-good (good-path a x) , good-path a x
res-expr← nu na r-res ()
res-expr← nu na (r-app rf ra) (wf , wa) =
  let (f , df , xf , gf) = res-expr← nu na rf wf ; (a , da , xa , ga) = res-expr← nu na ra wa
  in _ , re-app df da , x-app xf xa , gf , ga
res-expr← nu na (r-lam rb) w =
  let (b , db , xb , gb) = res-expr← nu na rb w in _ , re-lam db , x-lam xb , gb
res-expr← nu na (r-let re rb) (we , wb) =
  let (e , de , xe , ge) = res-expr← nu na re we ; (b , db , xb , gb) = res-expr← nu na rb wb
  in _ , re-let de db , x-let xe xb , ge , gb
res-expr← nu na (r-pair ra rb) (wa , wb) =
  let (a , da , xa , ga) = res-expr← nu na ra wa ; (b , db , xb , gb) = res-expr← nu na rb wb
  in _ , re-pair da db , x-pair xa xb , ga , gb
res-expr← nu na (r-destruct rs rl rr) (ws , wl , wr) =
  let (s , ds , xs , gs) = res-expr← nu na rs ws ; (l , dl , xl , gl) = res-expr← nu na rl wl
      (r , dr , xr , gr) = res-expr← nu na rr wr
  in _ , re-destruct ds dl dr , x-destruct xs xl xr , gs , gl , gr
res-expr← nu na (r-annot re) w =
  let (e , de , xe , ge) = res-expr← nu na re w in _ , re-annot de , x-annot xe , ge
res-expr← nu na (r-binop ra rb) (wa , wb) =
  let (a , da , xa , ga) = res-expr← nu na ra wa ; (b , db , xb , gb) = res-expr← nu na rb wb
  in _ , re-binop da db , x-binop xa xb , ga , gb
res-expr← nu na (r-neg re) w =
  let (e , de , xe , ge) = res-expr← nu na re w in _ , re-unop de , x-neg xe , ge
res-expr← nu na r-unit w = _ , re-unit , x-unit , tt
res-expr← nu na r-int w = _ , re-int , x-int , tt
res-expr← nu na r-float w = _ , re-float , x-float , tt

------------------------------------------------------------------------
-- The declarations
------------------------------------------------------------------------

open import Once.Spec.Signature using (Signature)
open import Once.Spec.Surface.Syntax using (Import)
open import Once.Adequacy.SpecGrammar.Written using (DeclWritten)
import Once.Spec.Surface.Program as SPr
import Once.Adequacy.SpecFront.Resolve

module Decls (Σ : Signature) where
  open import Once.Adequacy.SpecFront.Align Σ using (DR; dr-nil; dr-tsig; dr-def; dr-sig; dr-import; dr-alias)

  -- every import's module is found (the Spec's signature found it)
  res-decls← : ∀ {mm um am dsU dsR′ Σᵢ} → PathsNE um → PathsNE am
             → SPr.ResolvesDecls (env um am) dsU dsR′ → All DeclWritten dsU
             → SPr.Imported mm dsU Σᵢ
             → Σ[ dsR ∈ List Decl ] LR.ResolvesDecls mm um am dsU dsR × DR dsR′ dsR
  res-decls← nu na SPr.rd-nil [] SPr.im-nil = [] , LR.rds-nil , dr-nil
  res-decls← nu na (SPr.rd-def re rd) (w ∷ ws) (SPr.im-other SPr.ni-def im) =
    let (e , de , xe , g) = res-expr← nu na re w ; (ds , rds , dr) = res-decls← nu na rd ws im
    in _ , LR.rds-cons SPr.ni-def (LR.rd-fundef de g) rds , dr-def xe dr
  res-decls← nu na (SPr.rd-other SPr.nf-tsig rd) (_ ∷ ws) (SPr.im-other SPr.ni-tsig im) =
    let (ds , rds , dr) = res-decls← nu na rd ws im in _ , LR.rds-cons SPr.ni-tsig LR.rd-typesig rds , dr-tsig dr
  res-decls← nu na (SPr.rd-other SPr.nf-sig rd) (_ ∷ ws) (SPr.im-other SPr.ni-sig im) =
    let (ds , rds , dr) = res-decls← nu na rd ws im in _ , LR.rds-cons SPr.ni-sig LR.rd-signature rds , dr-sig dr
  res-decls← nu na (SPr.rd-other SPr.nf-alias rd) (_ ∷ ws) (SPr.im-other SPr.ni-alias im) =
    let (ds , rds , dr) = res-decls← nu na rd ws im in _ , LR.rds-cons SPr.ni-alias LR.rd-typealias rds , dr-alias dr
  res-decls← nu na (SPr.rd-other SPr.nf-import rd) (_ ∷ ws) (SPr.im-import fa _ _ im) =
    let (ds , rds , dr) = res-decls← nu na rd ws im
    in _ , LR.rds-import fa rds , dr-import dr
