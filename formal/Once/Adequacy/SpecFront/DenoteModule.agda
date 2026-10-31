-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.DenoteModule — a module the compiler types
-- denotes, in the Spec, a library (plan 0.133).
--
-- From the compiler's reading of a module — its declarations as written
-- (`dsU`, the Spec's), resolved (`dsR`), extracted into entries and typed as
-- a telescope (`ModTele`), every definition named `main` usable as the entry
-- (`MainsEffUU`) — the Spec's `ModuleDenotes`: the signature (`SigOf`), the
-- resolution (`Resolve`), the walk (`Walk`, from the FFI declarations' scope,
-- `Prefix`/`Start`), its names (`EndNames`, `SigFacts`), each `main` an
-- entry (`EndNames.mains-end`). A program's denotation (`Denote`) is this,
-- and its entry. No target is involved: a library is not run.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.DenoteModule where

open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Spec.Signature using (Signature; _∶_)
open import Once.Core.Decl using (toISig)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; _++_; _ʳ++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (true; false)
open import Data.String using (String)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Once.Spec.Name using (CanonicalName; canonical)
open import Once.Spec.Signature using (WellFormed)
import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Program as SPr
import Once.Spec.Surface.Resolution as SR
import Once.Spec.Core.Program as CoreProgram
import Once.Spec.Core.Syntax as SC
import Once.Core.Telescope as TL
import Once.Parser as Parser
open import Once.Spec.Surface.Syntax using (Decl; mkModule)
import Once.Parser.Module.Core as Core
open import Once.Parser.Module.Resolve using (ModuleMap; collectUnaliased; collectAliases; importedOf)
import Once.Parser.Relation.Resolution as LR
open import Once.Module using (ModTele; MainIn; MainsEffUU; emptyScope; entrySig)
open import Once.Core.Translate using ([])
open import Once.Adequacy.ModuleProgram using (toProgram; names₀; Names)
import Data.Empty
open import Once.Postulates using (extensionality)
import Once.Spec.Core.Syntax
import Data.List.Relation.Unary.All
import Once.TypeCheck.Scope
import Once.Spec.Name
import Once.Adequacy.SpecFront.Polys
open import Once.Adequacy.ModuleLaws using (teleSig≡entrySig)
import Once.Adequacy.NameClash as NC
import Once.Adequacy.SpecCore.Program as PG
open import Once.Adequacy.SpecFront.Extract using (XAlign; extract-align; nonSigs-none)
import Once.Adequacy.SpecFront.Resolve as Res
import Once.Adequacy.SpecFront.SigOf as SigOf
open import Once.Adequacy.SpecFront.SigFacts using (keys; rname; keys-distinct; uniq-of; one-name; h-sig-of; sig-in)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List using (map)
open import Once.Adequacy.SpecFront.SigWF using (wf-of)
open import Once.Adequacy.SpecFront.Prefix using (Past; past; prefix; ffi-facts; main-entry)
open import Once.Adequacy.SpecFront.Start using (names; distinct-rest; nosig-rest; fresh-start; not-sig)
open import Once.Adequacy.SpecFront.Polys using (Adj; adj-of; polyNames; poly-names; kinds-of; defs-of; poly-not-fun)
import Once.Adequacy.SpecFront.Align as Al
import Once.Adequacy.SpecFront.WalkState as WS
import Once.Adequacy.SpecFront.Walk as Wk
import Once.Adequacy.SpecFront.End as En
import Once.Adequacy.SpecFront.EndNames as EN
open import Once.Adequacy.SpecFront.Words using (DeclW; ModsW; KeysW; signature-words; key-word)

------------------------------------------------------------------------
-- The extractor's result, taken apart
------------------------------------------------------------------------

private
  then-ok : ∀ (s : String Data.Sum.⊎ ⊤) r {es} → Parser.thenExtract s r ≡ inj₂ es → (s ≡ inj₂ tt) × (r ≡ inj₂ es)
  then-ok (inj₂ tt) r e = refl , e
  then-ok (inj₁ _) r ()

  guard-ok : ∀ r {es} → Parser.guardDistinct r ≡ inj₂ es → r ≡ inj₂ es
  guard-ok (inj₁ _) ()
  guard-ok (inj₂ es) e = dist-ok _ e
    where
      dist-ok : ∀ b {m es′} → Parser.distinctOrErr b m (inj₂ es) ≡ inj₂ es′ → inj₂ es ≡ inj₂ es′
      dist-ok true  e′ = e′
      dist-ok false ()

------------------------------------------------------------------------
-- The denotation
------------------------------------------------------------------------

-- The compiler's typed telescope, past its FFI declarations, walked to its
-- end: the parts both denotations read (a library's and a program's).
module Parts {mm : SR.ModuleMap} {dsU dsR : List S.Decl}
  (wm : ModsW mm) (wd : All DeclW dsU)
  (rds : LR.ResolvesDecls mm (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR)
  (adj : Adj dsR)
  (fs es′ : List Parser.Entry) (mt : ModTele emptyScope (fs ++ es′))
  (guard : AllPairs _≢_ (names (fs ++ es′))) (xn : XAlign (Parser.nonSigs dsR) es′)
  (ffiE : All Once.Adequacy.SpecFront.Extract.FFIEntry fs)
  (sigk : All Once.Adequacy.SpecFront.Extract.FFIFacts fs → Σ[ Σₛ ∈ Signature ] SPr.SignatureOf mm dsU Σₛ
            × (toISig Σₛ ≡ entrySig fs) × (entrySig (fs ++ es′) ≡ entrySig fs))
  where
  facts = ffi-facts fs ffiE mt
  Σₛ = proj₁ (sigk facts)
  sig = proj₁ (proj₂ (sigk facts))
  tf = proj₁ (proj₂ (proj₂ (sigk facts)))
  te = proj₂ (proj₂ (proj₂ (sigk facts)))
  wf = wf-of Σₛ fs tf facts
  kw = signature-words wm wd sig
  uniq = uniq-of Σₛ (fs ++ es′) (trans tf (sym te)) guard
  eqT : Once.Module.teleSig mt ≡ toISig Σₛ
  eqT = trans (teleSig≡entrySig mt) (trans te (sym tf))
  P = prefix Σₛ {S = SC.[]} fs ffiE CoreProgram.[] [] [] [] (names₀ Σₛ) mt (λ m → sig-in Σₛ (key-word kw) (subst (_ ∈_) eqT m))
  sg = entrySig fs ʳ++ []
  ukeys : AllPairs _≢_ (keys (entrySig fs))
  ukeys = subst (λ l → AllPairs _≢_ (keys l)) te (keys-distinct (fs ++ es′) guard)
  guard′ = distinct-rest fs es′ guard
  ps = polyNames es′
  h-sig = λ {m} {c} {t} (_ : Once.Spec.Name.NotGenerator c) M → h-sig-of Σₛ fs tf ukeys facts {m} {c} {t} M
  -- a telescope entry is no FFI declaration (the extractor's guard)
  h-psig : ∀ {x} → x ∈ ps → Once.TypeCheck.Scope.lookupImport sg x ≡ nothing
  h-psig x∈ = Data.List.Relation.Unary.All.lookup (nosig-rest fs es′ guard) (poly-names es′ x∈)
  h-own : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σₛ)
  h-own {x} x∈ps M = not-sig Σₛ fs es′ tf guard (poly-names es′ x∈ps) M
  rd = Res.Decls.res-decls Σₛ rds
  dsR′ = proj₁ rd
  align = Al.align-of Σₛ (proj₂ (proj₂ rd)) adj xn
  module W = Wk Σₛ ps sg h-sig h-own h-psig (key-word kw)
  eok : W.EntriesOK (Once.Module.scope sg [] []) es′
  eok = record
    { distinct = guard′ ; fresh = fresh-start es′ ; nosig = nosig-rest fs es′ guard
    ; kinds = kinds-of es′ guard′ (defs-of (nonSigs-none dsR) xn) }
  ks = W.EntriesOK.kinds eok
  e = En.endOf Σₛ ps CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) ks
  w = W.walk CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) align (WS.winv-empty Σₛ ps) eok

  lib : CoreProgram.Library Σₛ
  lib = record { wf = wf ; defs = En.End.tl e }

  fin0 : Fin 0 → Data.Empty.⊥
  fin0 ()
  -- (two namings of no definitions, by P1)
  fin0-ext : ∀ {g : Fin 0 → CanonicalName} → Names.nm (names₀ Σₛ) ≡ g
  fin0-ext = extensionality (λ ())
  not-def : ∀ dd {t} → ¬ ((En.End.nm e dd ∶ t) ∈ Σₛ)
  not-def dd M = pick (EN.named-end Σₛ ps CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) ks {L = []} (λ ()) dd) M
    where
      pick : ∀ {c t} → Σ[ x ∈ String ] (c ≡ canonical (x ∷ [])) × (x ∈ [] ⊎ x ∈ names es′) → ¬ ((c ∶ t) ∈ Σₛ)
      pick (x , ex , inj₁ ()) M′
      pick (x , ex , inj₂ mx) M′ = not-sig Σₛ fs es′ tf guard mx (subst (λ c → (c ∶ _) ∈ Σₛ) ex M′)

  -- The library the module denotes: every definition named `main` is an
  -- entry, for every one the compiler typed is (`MainsEffUU`).
  denotesᴹ : MainsEffUU mt → SPr.ModuleDenotes mm (S.mkModule dsU) Σₛ lib
  denotesᴹ ms = record
    { signature = sig
    ; unaliased = collectUnaliased mm dsU
    ; unaliases = Res.unaliased-of rds
    ; resolved  = dsR′
    ; resolves  = subst (λ a → SPr.ResolvesDecls (SR.env (collectUnaliased mm dsU) a) dsU dsR′) (Res.aliases-eq dsU)
                        (proj₁ (proj₂ rd))
    ; names     = En.End.nm e
    ; walk      = subst (λ n → SPr.Walk Σₛ SC.[] n CoreProgram.[] dsR′ (En.End.S e) (En.End.nm e) (En.End.tl e)) fin0-ext w
    ; distinct  = EN.distinct-end Σₛ ps CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) ks
                    (λ {x} → Data.Empty.⊥-elim (fin0 x)) guard′ (Data.List.Relation.Unary.All.tabulate (λ _ ()))
    ; sig-distinct = one-name Σₛ uniq
    ; def-not-sig  = λ dd M → not-def dd M
    ; mains     = EN.mains-end Σₛ ps CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) ks
                    (λ d → Data.Empty.⊥-elim (fin0 d)) (Past.mains P ms)
    }

-- The extractor's result, split at its FFI declarations, and what `Parts`
-- needs of it.
module Split {mm dsU dsR es} (wm : ModsW mm) (wd : All DeclW dsU)
  (rds : LR.ResolvesDecls mm (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR)
  (ef : Parser.extractFunctions (Core.resolved (mkModule dsR) (importedOf mm dsU)) ≡ inj₂ es) where
  r₀ = Parser.thenExtract (Parser.sigsAdjacent dsR nothing) (Parser.extractFunctions-go (Parser.sigsFirst dsR (importedOf mm dsU)) nothing)
  sa = Parser.sigsAdjacent dsR nothing
  rg = Parser.extractFunctions-go (Parser.sigsFirst dsR (importedOf mm dsU)) nothing
  adjE = proj₁ (then-ok sa rg (guard-ok r₀ ef))
  goE  = proj₂ (then-ok sa rg (guard-ok r₀ ef))
  guard = NC.guard-entries r₀ ef
  sp = SigOf.signature-of rds (extract-align (Parser.sigsFirst dsR (importedOf mm dsU)) goE)
  fs = proj₁ sp
  es′ = proj₁ (proj₂ sp)
  ees = proj₁ (proj₂ (proj₂ sp))
  xn = proj₁ (proj₂ (proj₂ (proj₂ sp)))
  ffiE = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ sp))))
  sigk = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ sp))))
  adj = adj-of dsR adjE

-- What the Spec's module denotes: a library, the compiler's telescope.
record ModuleDenoted (mm : SR.ModuleMap) (ds : List S.Decl) {es} (mt : ModTele emptyScope es) : Set where
  field
    Σₛ      : Signature
    wf      : WellFormed Σₛ
    uniq    : Unique (map rname Σₛ)
    {size}  : ℕ
    {sig}   : SC.Defs size
    tele    : CoreProgram.Tele Σₛ sig
    denotes : SPr.ModuleDenotes mm (S.mkModule ds) Σₛ (record { wf = wf ; defs = tele })

denoteᴹ : ∀ {mm dsU dsR es}
        → ModsW mm → All DeclW dsU
        → LR.ResolvesDecls mm (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR
        → Parser.extractFunctions (Core.resolved (mkModule dsR) (importedOf mm dsU)) ≡ inj₂ es
        → (mt : ModTele emptyScope es) → MainsEffUU mt → ModuleDenoted mm dsU mt
denoteᴹ {mm} {dsU} {dsR} {es} wm wd rds ef mt ms =
  go SP.fs SP.es′ SP.ees mt ms SP.guard SP.xn SP.ffiE SP.sigk
  where
    module SP = Split wm wd rds ef
    go : ∀ fs es′ {es} → es ≡ fs ++ es′ → (mt : ModTele emptyScope es) → MainsEffUU mt
       → AllPairs _≢_ (names es) → XAlign (Parser.nonSigs dsR) es′ → All Once.Adequacy.SpecFront.Extract.FFIEntry fs
       → (All Once.Adequacy.SpecFront.Extract.FFIFacts fs → Σ[ Σₛ ∈ Signature ] SPr.SignatureOf mm dsU Σₛ
            × (toISig Σₛ ≡ entrySig fs) × (entrySig es ≡ entrySig fs))
       → ModuleDenoted mm dsU mt
    go fs es′ refl mt ms guard xn ffiE sigk =
      record { Σₛ = Pt.Σₛ ; wf = Pt.wf ; uniq = Pt.uniq ; tele = En.End.tl Pt.e ; denotes = Pt.denotesᴹ ms }
      where module Pt = Parts wm wd rds SP.adj fs es′ mt guard xn ffiE sigk

