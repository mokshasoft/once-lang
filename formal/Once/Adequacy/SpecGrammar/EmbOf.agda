-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.EmbOf — what the compiler parses, the Spec can
-- write (plan 0.121 §3.6, F1).
--
-- `Decl.parses→` reads a compiler parse as the Spec's, given the parsed
-- declarations' Spec images (`DEmb`). Every parse has them: the grammar
-- builds only expressions the Spec's syntax has (no `RAna`, the one
-- compiler-only form, which no rule produces) and only owner-less
-- signatures (`parses-emb`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.EmbOf where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Lang.Syntax using (RawExpr; RVar; RApp; RBinOp; RLam; RLet; RPair; RDestruct; RAnnot; RUnaryOp; OpNeg)
import Once.Spec.Surface.Syntax as S
open import Once.Parser.ExprRelation as E
open import Once.Adequacy.SpecGrammar.Expr
  using (Emb; e-var; e-qual; e-app; e-lam; e-let; e-pair; e-destruct; e-unit; e-int; e-float; e-annot; e-binop; e-neg)
open import Once.Adequacy.SpecGrammar.TypeRF using (type-rf)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import; emb-wrap)
open import Once.Parser.Module.Core using (Decl; DImport; mkImport)
import Once.Parser.Module.Core
import Once.Lang.Grammar.Decl as LD
import Once.Lang.Grammar.Import as LI
import Once.Lang.Grammar.TypeAlias as LT
import Once.Lang.Grammar.Signature as LS
import Once.Lang.Grammar.FunDef as LF
import Once.Lang.Grammar.OpDecl as LO
import Once.Lang.Parsing as LP

-- An expression's Spec image.
Has : RawExpr → Set
Has e = Σ[ e′ ∈ S.Expr ] Emb e e′

private
  app : ∀ {f a} → Has f → Has a → Has (RApp f a)
  app (_ , ef) (_ , ea) = _ , e-app ef ea

  bin : ∀ {op a b} → Has a → Has b → Has (RBinOp op a b)
  bin (_ , ea) (_ , eb) = _ , e-binop ea eb

mutual
  h-expr : ∀ {toks e rest} → ParsesExpr toks e rest → Has e
  h-expr (pe-mk d) = h-comp d

  h-comp : ∀ {toks e rest} → ParsesComp toks e rest → Has e
  h-comp (pc-mk dc dt) = h-ctail dt (h-cmp dc)

  h-ctail : ∀ {l toks e rest} → ParsesCompTail l toks e rest → Has l → Has e
  h-ctail (pct-done _) h = h
  h-ctail (pct-dot dc dt) h = h-ctail dt (app (app (_ , e-var) h) (h-cmp dc))

  h-cmp : ∀ {toks e rest} → ParsesCmp toks e rest → Has e
  h-cmp (pcm-noop da _) = h-add da
  h-cmp (pcm-lt dl dr) = bin (h-add dl) (h-add dr)
  h-cmp (pcm-le dl dr) = bin (h-add dl) (h-add dr)
  h-cmp (pcm-gt dl dr) = bin (h-add dl) (h-add dr)
  h-cmp (pcm-ge dl dr) = bin (h-add dl) (h-add dr)
  h-cmp (pcm-eq dl dr) = bin (h-add dl) (h-add dr)
  h-cmp (pcm-ne dl dr) = bin (h-add dl) (h-add dr)

  h-add : ∀ {toks e rest} → ParsesAdd toks e rest → Has e
  h-add (pa-mk dm dt) = h-atail dt (h-mul dm)

  h-atail : ∀ {l toks e rest} → ParsesAddTail l toks e rest → Has l → Has e
  h-atail (pat-done _) h = h
  h-atail (pat-plus dm dt) h = h-atail dt (bin h (h-mul dm))
  h-atail (pat-minus dm dt) h = h-atail dt (bin h (h-mul dm))

  h-mul : ∀ {toks e rest} → ParsesMul toks e rest → Has e
  h-mul (pm-mk du dt) = h-mtail dt (h-unary du)

  h-mtail : ∀ {l toks e rest} → ParsesMulTail l toks e rest → Has l → Has e
  h-mtail (pmt-done _) h = h
  h-mtail (pmt-star du dt) h = h-mtail dt (bin h (h-unary du))
  h-mtail (pmt-slash du dt) h = h-mtail dt (bin h (h-unary du))
  h-mtail (pmt-percent du dt) h = h-mtail dt (bin h (h-unary du))

  h-unary : ∀ {toks e rest} → ParsesUnary toks e rest → Has e
  h-unary (pu-neg du) = let (_ , ee) = h-unary du in _ , e-neg ee
  h-unary (pu-app da) = h-app da

  h-app : ∀ {toks e rest} → ParsesApp toks e rest → Has e
  h-app (papp-mk da dt) = h-aptail dt (h-atom da)

  h-aptail : ∀ {l toks e rest} → ParsesAppTail l toks e rest → Has l → Has e
  h-aptail (papp-done _) h = h
  h-aptail (papp-arg _ da dt) h = h-aptail dt (app h (h-atom da))

  h-atom : ∀ {toks e rest} → ParsesAtomExpr toks e rest → Has e
  h-atom pae-unit = _ , e-unit
  h-atom pae-int = _ , e-int
  h-atom pae-float = _ , e-float
  h-atom (pae-var _ _) = _ , e-var
  h-atom (pae-qual _) = _ , e-qual
  h-atom (pae-paren de dc) = h-pcont dc (h-expr de)
  h-atom (pae-lambda dl) = h-lam dl
  h-atom (pae-let (plet-single dv (plin db))) =
    let (_ , ev) = h-expr dv ; (_ , eb) = h-expr db in _ , e-let ev eb
  h-atom (pae-destruct (pd-mk ds (pdof (pdb dl (prb dr))))) =
    let (_ , es) = h-expr ds ; (_ , el) = h-expr dl ; (_ , er) = h-expr dr in _ , e-destruct es el er
  h-atom (pae-paren-op dop) = h-op dop

  h-lam : ∀ {toks e rest} → ParsesLamParams toks e rest → Has e
  h-lam (plp-body de) = h-expr de
  h-lam (plp-arg dl) = let (_ , eb) = h-lam dl in _ , e-lam eb

  h-pcont : ∀ {e toks eo rest} → ParsesParenCont e toks eo rest → Has e → Has eo
  h-pcont ppc-close h = h
  h-pcont (ppc-pair de ppt-close) (_ , ea) = let (_ , eb) = h-expr de in _ , e-pair ea eb
  h-pcont (ppc-annot dT) (_ , ee) = _ , e-annot (type-rf dT) ee

  h-op : ∀ {acc toks e rest} → ParsesOpExpr acc toks e rest → Has e
  h-op poe-close = _ , e-var
  h-op (poe-dot d) = h-op d
  h-op (poe-plus d) = h-op d
  h-op (poe-minus d) = h-op d
  h-op (poe-star d) = h-op d
  h-op (poe-slash d) = h-op d
  h-op (poe-percent d) = h-op d
  h-op (poe-lt d) = h-op d
  h-op (poe-gt d) = h-op d
  h-op (poe-pipe d) = h-op d
  h-op (poe-amp d) = h-op d
  h-op (poe-at d) = h-op d

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

HasD : Decl → Set
HasD d = Σ[ d′ ∈ S.Decl ] DEmb d d′

private
  h-fundef : ∀ {name toks d rest} → LF.ParsesFunDef name toks d rest → HasD d
  h-fundef (LF.pfd-mk {params = ps} _ (LF.pfb-mk _ de)) = let (_ , eb) = h-expr de in _ , d-fundef (emb-wrap ps eb)

  h-alias : ∀ {name ps toks d rest} → LT.ParsesTypeAlias name ps toks d rest → HasD d
  h-alias (LT.gta-eq-r _ _ _) = _ , d-alias
  h-alias (LT.gta-word-r d) = h-alias d

  h-import : ∀ {toks d rest} → LI.ParsesImport toks d rest → HasD d
  h-import (LI.pi-mk _ LI.pia-alias-r) = _ , d-import
  h-import (LI.pi-mk _ (LI.pia-neq-r _)) = _ , d-import
  h-import (LI.pi-mk _ (LI.pia-nonword-r _)) = _ , d-import

h-decl : ∀ {toks d rest} → LD.ParsesDecl toks d rest → HasD d
h-decl (LD.pd-import di) = h-import di
h-decl (LD.pd-typealias (LT.pta-mk da)) = h-alias da
h-decl (LD.pd-signature (LS.psig-mk _ _)) = _ , d-signature
h-decl (LD.pd-typesig _ _ _ _ _ _) = _ , d-typesig
h-decl (LD.pd-fundef _ _ _ _ dF) = h-fundef dF
h-decl (LD.pd-opdecl (LO.pod-mk _ (LO.poa-sig _ _))) = _ , d-typesig
h-decl (LD.pd-opdecl (LO.pod-mk _ (LO.poa-fun _ dF))) = h-fundef dF

h-decls : ∀ {toks ds rest} → LP.ParsesDecls toks ds rest → Σ[ ds′ ∈ List S.Decl ] Pointwise DEmb ds ds′
h-decls (LP.pds-noskip _) = [] , []
h-decls (LP.pds-stop _ _) = [] , []
h-decls (LP.pds-cons _ d ds) = let (d′ , ed) = h-decl d ; (ds′ , eds) = h-decls ds in d′ ∷ ds′ , ed ∷ eds

-- A text the compiler parses: its declarations' Spec images.
parses-emb : ∀ {text m} → LP.ParsesText text m
           → Σ[ ds′ ∈ List S.Decl ] Pointwise DEmb (Once.Parser.Module.Core.Module.decls m) ds′
parses-emb (_ , _ , _ , dd , _) = h-decls dd
