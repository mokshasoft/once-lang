-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.TypedBack — a module the Spec types, the compiler
-- resolves and types (plan 0.121 `complete`; the converse of `Denote`).
--
-- From the Spec's denotation of a module — its signature, resolution, walk,
-- names — the compiler's: the resolution (`ResolveBack`), the extractor's
-- entries (`ExtractOk`), and the typed telescope with a valid `main`: the FFI
-- entries (`Prefix.prefix←`), then the definitions, built alongside the
-- Spec's walk (`WalkBack`) in the scope the sound direction uses (`Denote`):
-- the signature's table past the FFI entries, its keys word names (R13).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecFront.TypedBack (fmt : TargetNum) where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; map; tabulate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-tabulate⁺; ∈-map⁻)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
import Data.List.Relation.Unary.AllPairs
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (Signature; WellFormed; _∶_)
import Once.Spec.Core.Syntax as SC
import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Program as SPr
import Once.Spec.Surface.Resolution as SR
import Once.Spec.Core.Program as CoreProgram
import Once.Internal.Core.PolyTy as LP
import Once.Internal.Core.Telescope as TL
import Once.Parser as Parser
open import Once.Parser.Module.Core using (Decl; mkModule; DImport; mkImport)
open import Once.Parser.Module.Resolve using (ModuleMap; collectUnaliased; collectAliases; lookupModule; sigNames)
import Once.Internal.Resolution as LR
import Once.Internal.Module as LM
open import Once.Internal.Module using (ModTele; emptyScope; scope; entrySig; MainsEffUU; MainIn)
open import Once.Internal.Core.Translate using (SigSig; s-ffi; SigCF)
open import Once.Adequacy.SpecInterp using (toISig)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb; d-typesig; d-fundef; d-signature; d-alias; d-import)
open import Once.Adequacy.SpecGrammar.Written using (DeclWritten)
open import Once.Adequacy.SpecCore.Schema using (defsS)
open import Once.Adequacy.SpecFront.ModRel using (ModRel)
open import Once.Adequacy.SpecFront.Extract using (FFIFacts; nonSigs-none)
open import Once.Adequacy.SpecFront.ExtractBack using (walk-adj; dr-adj)
open import Once.Adequacy.SpecFront.ExtractOk using (Extracted; extract-ok)
open import Once.Adequacy.SpecFront.GuardBack using (defNamesS; walk-tab)
open import Once.Adequacy.SpecFront.ResolveBack using (PathsNE; unaliased-eq; module Decls)
import Once.Adequacy.SpecFront.Resolve as Res
open import Once.Adequacy.SpecFront.SigFacts using (keys; keys-distinct; h-sig-of)
open import Once.Adequacy.SpecFront.Start using (distinct-rest; nosig-rest; fresh-start; not-sig)
open import Once.Adequacy.SpecFront.Polys using (polyNames; poly-names; kinds-of; defs-of)
open import Once.Adequacy.SpecFront.Prefix using (prefix←)
open import Once.Adequacy.SpecFront.Words using (ModsW; DeclW; signature-words; key-word; r13-at)
import Once.Adequacy.SpecFront.Align as Al
import Once.Adequacy.SpecFront.WalkBack as WB
import Once.Adequacy.SpecFront.WalkMain as WM
import Once.Adequacy.SpecFront.WalkState as WS
import Once.Adequacy.SpecFront.Walk
import Once.Compile
import Once.Spec.Name
import Once.Internal.Core.Translate

------------------------------------------------------------------------
-- The import tables' paths
------------------------------------------------------------------------

private
  paths-map : ∀ (p : List String) (ns : List String) → p ≢ [] → PathsNE (map (λ n → (n , p)) ns)
  paths-map p []       ne = []
  paths-map p (n ∷ ns) ne = ne ∷ paths-map p ns ne

  paths-++ : ∀ {xs ys} → PathsNE xs → PathsNE ys → PathsNE (xs ++ ys)
  paths-++ []       q = q
  paths-++ (p ∷ ps) q = p ∷ paths-++ ps q

-- (mirrors `collectUnaliased`'s `with`)
um-ne : ∀ (mm : ModuleMap) {dsU ds′} → Pointwise DEmb dsU ds′ → All DeclW ds′ → PathsNE (collectUnaliased mm dsU)
um-ne mm [] [] = []
um-ne mm (d-typesig ∷ pw)  (_ ∷ ws) = um-ne mm pw ws
um-ne mm (d-fundef _ ∷ pw) (_ ∷ ws) = um-ne mm pw ws
um-ne mm (d-signature ∷ pw) (_ ∷ ws) = um-ne mm pw ws
um-ne mm (d-alias ∷ pw)    (_ ∷ ws) = um-ne mm pw ws
um-ne mm (d-import {p = p} {a = just _} ∷ pw) (_ ∷ ws) = um-ne mm pw ws
um-ne mm (d-import {p = p} {a = nothing} ∷ pw) ((_ , ne) ∷ ws) with lookupModule mm p
... | just (mkModule impDs) = paths-++ (paths-map p (sigNames impDs) ne) (um-ne mm pw ws)
... | nothing               = um-ne mm pw ws

am-ne : ∀ {dsU ds′} → Pointwise DEmb dsU ds′ → All DeclW ds′ → PathsNE (collectAliases dsU)
am-ne [] [] = []
am-ne (d-typesig ∷ pw)  (_ ∷ ws) = am-ne pw ws
am-ne (d-fundef _ ∷ pw) (_ ∷ ws) = am-ne pw ws
am-ne (d-signature ∷ pw) (_ ∷ ws) = am-ne pw ws
am-ne (d-alias ∷ pw)    (_ ∷ ws) = am-ne pw ws
am-ne (d-import {a = just _} ∷ pw)  ((_ , ne) ∷ ws) = ne ∷ am-ne pw ws
am-ne (d-import {a = nothing} ∷ pw) (_ ∷ ws)        = am-ne pw ws

------------------------------------------------------------------------
-- `main` is one of the walk's definitions
------------------------------------------------------------------------

private
  ʳ++-mem : ∀ {A : Set} (xs : List A) {acc x} → x ∈ (xs ʳ++ acc) → x ∈ xs ⊎ x ∈ acc
  ʳ++-mem []       m = inj₂ m
  ʳ++-mem (y ∷ xs) m = shift (ʳ++-mem xs m)
    where
      shift : ∀ {x} → _ ⊎ x ∈ (y ∷ _) → x ∈ (y ∷ xs) ⊎ _
      shift (inj₁ m′)         = inj₁ (there m′)
      shift (inj₂ (here e))   = inj₁ (here e)
      shift (inj₂ (there m′)) = inj₂ m′

main-defined : ∀ {Σ ds s″} {S″ : SC.Defs s″} {nm″ : Fin s″ → CanonicalName} {tl″} {S₀ : _} {nm₀ : Fin 0 → CanonicalName} {tl₀}
             → SPr.Walk Σ S₀ nm₀ tl₀ ds S″ nm″ tl″ → ∀ i → nm″ i ≡ canonical ("main" ∷ []) → "main" ∈ defNamesS ds
main-defined {ds = ds} {nm″ = nm″} w i e = at (ʳ++-mem (map own (defNamesS ds)) (subst (_ ∈_) (walk-tab w) (subst (_∈ tabulate nm″) e (∈-tabulate⁺ i))))
  where
    own : String → CanonicalName
    own x = canonical (x ∷ [])
    at : _ ⊎ canonical ("main" ∷ []) ∈ [] → "main" ∈ defNamesS ds
    at (inj₁ m) = let (y , y∈ , ey) = ∈-map⁻ own m in subst (_∈ defNamesS ds) (sym (canon-inj ey)) y∈
      where
        canon-inj : ∀ {x y : String} → canonical (x ∷ []) ≡ canonical (y ∷ []) → x ≡ y
        canon-inj refl = refl
    at (inj₂ ())

------------------------------------------------------------------------
-- The signature table, in the scope's order
------------------------------------------------------------------------

private
  -- the FFI entries' table, reversed onto a recorded one
  sigsig-of : ∀ {Fs} fs {acc} → All FFIFacts fs → (∀ {d} → d ∈ entrySig fs → d ∈ Fs) → SigSig Fs acc → SigSig Fs (entrySig fs ʳ++ acc)
  sigsig-of [] [] _ ss = ss
  sigsig-of (Parser.e-fun (Parser.mkFunInfo x _ _ _) ∷ fs) ((refl , ty , refl , c , h , g) ∷ fa) inF ss =
    sigsig-of fs fa (λ m → inF (there m)) (s-ffi h g (inF (here refl)) ss)
  sigsig-of (Parser.e-poly _ ∷ fs) (() ∷ fa) inF ss

  all-pre : ∀ {A : Set} {P : A → Set} xs {ys} → All P (xs ++ ys) → All P xs
  all-pre []       _        = []
  all-pre (x ∷ xs) (q ∷ qs) = q ∷ all-pre xs qs

  ap-pre : ∀ {A : Set} (xs : List A) {ys} → AllPairs _≢_ (xs ++ ys) → AllPairs _≢_ xs
  ap-pre []       _ = Data.List.Relation.Unary.AllPairs.[]
  ap-pre (x ∷ xs) (a Data.List.Relation.Unary.AllPairs.∷ u) = all-pre xs a Data.List.Relation.Unary.AllPairs.∷ ap-pre xs u


------------------------------------------------------------------------
-- The compiler's typing
------------------------------------------------------------------------

-- What the compiler makes of a module the Spec types.
record TypedC (mm : ModuleMap) (dsU : List Decl) : Set where
  field
    dsR : List Decl
    rds : LR.ResolvesDecls mm (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR
    mt  : LM.ModuleTyped (mkModule dsR)
    hvm : LM.HasValidMain (mkModule dsR) mt

private
  typed-at : ∀ m (ef : String ⊎ List Parser.Entry) {es} → ef ≡ inj₂ es → (mt : ModTele emptyScope es) → MainsEffUU mt → MainIn mt
           → Σ[ mt′ ∈ LM.ModuleTyped-ef m ef ] LM.HasValidMain-ef m ef mt′
  typed-at m .(inj₂ _) refl mt ms mi = mt , ms , mi

typed← : ∀ {mm mm′ dsU ds′ Σ p}
       → ModsW mm′ → All DeclW ds′ → All DeclWritten ds′
       → ModRel mm mm′ → Pointwise DEmb dsU ds′
       → SPr.Denotes mm′ (S.mkModule ds′) Σ p
       → TypedC mm dsU
typed← {mm} {mm′} {dsU} {ds′} {Σ} {p} wm wd wr mr pw D = record { dsR = dsR ; rds = rds ; mt = proj₁ th ; hvm = proj₂ th }
  where
    open SPr.Denotes D
    module P = CoreProgram.Program p
    sig = signature
    Σ₀ = proj₁ sig
    Σᵢ = proj₁ (proj₂ sig)
    im = proj₁ (proj₂ (proj₂ (proj₂ sig)))
    -- the resolution, the compiler's
    rd′ : SPr.ResolvesDecls (SR.env (collectUnaliased mm dsU) (collectAliases dsU)) ds′ resolved
    rd′ = subst₂ (λ u a → SPr.ResolvesDecls (SR.env u a) ds′ resolved) (unaliased-eq mr pw unaliases) (sym (Res.aliases-eq pw)) resolves
    r← = Decls.res-decls← Σ mr (um-ne mm pw wd) (am-ne pw wd) rd′ pw wr (subst (SPr.Imported mm′ ds′) refl im)
    dsR = proj₁ r←
    rds = proj₁ (proj₂ r←)
    dr = proj₂ (proj₂ r←)
    -- the extractor's entries
    al = Parser.extractAliases (mkModule dsR)
    X = extract-ok al wm wd mr rds pw rd′ dr sig P.wf sig-distinct walk distinct def-not-sig
    fs = Extracted.fs X
    es′ = Extracted.esN X
    tf = Extracted.table X
    guard = Extracted.distinct X
    -- the scope past the FFI entries, as `Denote` has it
    kw = signature-words wm wd sig
    ukeys : AllPairs _≢_ (keys (entrySig fs))
    ukeys = keys-distinct fs (ap-pre (map Parser.entryNameOf fs) (subst (AllPairs _≢_) (map-++ Parser.entryNameOf fs es′) guard))
    sg = entrySig fs ʳ++ []
    ps = polyNames es′
    h-sig = λ {m} Δ {c} {t} (_ : Once.Spec.Name.NotGenerator c) (M : (c ∶ t) Data.List.Membership.Propositional.∈ Σ)
            → h-sig-of Σ fs tf ukeys (Extracted.facts X) {m} Δ M
    h-own = λ {x} {t} (x∈ : x ∈ ps) M → not-sig Σ fs es′ tf guard {x} {t} (poly-names es′ x∈) M
    h-psig = λ {x} (x∈ : x ∈ ps) → All.lookup (nosig-rest fs es′ guard) (poly-names es′ x∈)
    module W = WB Σ (r13-at {Σ} kw) fmt ps sg h-sig h-own h-psig (key-word kw)
    module Wk = Once.Adequacy.SpecFront.Walk Σ (r13-at {Σ} kw) fmt ps sg h-sig h-own h-psig (key-word kw)
    ss : SigSig (toISig Σ) sg
    ss = sigsig-of fs (Extracted.facts X) (λ m → subst (_ ∈_) (sym tf) m) SigSig.[]
    guard′ = distinct-rest fs es′ guard
    eok : Wk.EntriesOK (scope sg Once.Compile.emptyFunCtx []) es′
    eok = record { distinct = guard′ ; fresh = fresh-start es′ ; nosig = nosig-rest fs es′ guard
                 ; kinds = kinds-of es′ guard′ (defs-of (nonSigs-none dsR) (Extracted.defs X)) }
    rel₀ : W.Rel SC.[] (defsS (LP.[] {Fs = toISig Σ}))
    rel₀ = record { ρ⇒ = λ () ; ren⇒ = λ () ; ρ⇐ = λ () ; ren⇐ = λ () }
    align = Al.align-of Σ dr (dr-adj Σ dr (walk-adj walk)) (Extracted.defs X)
    -- the end's `main` is the entry
    H : ∀ i → names i ≡ canonical ("main" ∷ []) → CoreProgram.Entry Σ (P.sig SC.!! i)
    H i e = subst (λ j → CoreProgram.Entry Σ (P.sig SC.!! j)) (sym (distinct (trans e (sym entry)))) P.isMain
    w← = W.walk← TL.[] ss Once.Internal.Core.Translate.ImpSig.[] Once.Internal.Core.Translate.TeleSig.[] (λ ()) _ rel₀ walk align
                 (WS.winv-empty Σ ps) eok
    pf = prefix← {sc = emptyScope} fs (Extracted.facts X) (proj₁ w←)
    th = typed-at (mkModule dsR) _ (Extracted.extracted X) (proj₁ pf)
                  (proj₁ (proj₂ pf) (proj₁ (proj₂ w←) (WM.walk-mains Σ walk H)))
                  (proj₂ (proj₂ pf) (proj₂ (proj₂ w←) (WM.walk-main Σ walk (main-defined walk P.main entry) H)))
