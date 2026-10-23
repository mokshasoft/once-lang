-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.EmbOf — what the compiler parses, the Spec can
-- write (plan 0.121 §3.6, F1).
--
-- `Decl.parses→` reads a compiler parse as the Spec's, given the parsed
-- declarations' Spec images (`DEmb`). Every parse has them: its expressions
-- are the Spec's, and its signatures owner-less (`parses-emb`).
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.EmbOf where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Once.Spec.Surface.Syntax as S
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-signature; d-alias; d-import; fundef-emb)
open import Once.Parser.Module.Core using (Decl; DImport; mkImport)
import Once.Parser.Module.Core
import Once.Internal.Grammar.Decl as LD
import Once.Internal.Grammar.Import as LI
import Once.Internal.Grammar.TypeAlias as LT
import Once.Internal.Grammar.Signature as LS
import Once.Internal.Grammar.FunDef as LF
import Once.Internal.Grammar.OpDecl as LO
import Once.Internal.Parsing as LP

------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------

HasD : Decl → Set
HasD d = Σ[ d′ ∈ S.Decl ] DEmb d d′

private
  h-fundef : ∀ {name toks d rest} → LF.ParsesFunDef name toks d rest → HasD d
  h-fundef (LF.pfd-mk {params = ps} _ (LF.pfb-mk {body = b} _ _)) = _ , fundef-emb ps b

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
