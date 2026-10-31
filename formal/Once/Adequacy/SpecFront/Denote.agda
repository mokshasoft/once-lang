-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Denote — a module the compiler types denotes, in
-- the Spec, the program the compiler builds (plan 0.121 §3.6, F6).
--
-- From the compiler's reading of a module — its declarations as written
-- (`dsU`, the Spec's), resolved (`dsR`), extracted
-- into entries and typed as a telescope (`ModTele`) with a `main` — the
-- Spec's `Denotes`: the signature (`SigOf`), the resolution (`Resolve`), the
-- walk (`Walk`, from the FFI declarations' scope, `Prefix`/`Start`), its
-- names (`EndNames`, `SigFacts`) — the library, `DenoteModule` — and its
-- entry (`End`); the program is the
-- compiler's core program translated (`programS`), the one `toProgram`
-- builds (`built`). A generator the compiler finds by its rendered name is
-- the Spec declaration of that name, for Σ's names are word names (`Words`,
-- R13).
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

module Once.Adequacy.SpecFront.Denote (fmt : TargetNum) where

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

open import Once.Adequacy.SpecFront.DenoteModule using (module Parts; module Split)

-- What the Spec's module denotes, and that it is the compiler's program.
record Denoted (mm : SR.ModuleMap) (ds : List S.Decl) {es} (mt : ModTele emptyScope es) (mi : MainIn mt) : Set where
  field
    Σₛ      : Signature
    wf      : WellFormed Σₛ
    uniq    : Unique (map rname Σₛ)
    keysW   : KeysW Σₛ
    sig-eq  : Once.Module.teleSig mt ≡ toISig Σₛ
    -- the compiler's core program, built over Σ's table
    {size}  : ℕ
    {sig}   : SC.Defs size
    tele    : CoreProgram.Tele Σₛ sig
    entry   : Fin size
    isMain  : CoreProgram.Entry Σₛ (sig SC.!! entry)
    built   : toProgram Σₛ {S = SC.[]} CoreProgram.[] [] [] [] (names₀ Σₛ) mt mi
                (λ m → sig-in Σₛ (key-word keysW) (subst (_ ∈_) sig-eq m))
              ≡ TL.program tele entry isMain
    -- …which the module denotes
    denotes : SPr.Denotes mm (S.mkModule ds) Σₛ (PG.programS Σₛ fmt wf (TL.program tele entry isMain))

denote : ∀ {mm dsU dsR es}
       → ModsW mm → All DeclW dsU
       → LR.ResolvesDecls mm (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR
       → Parser.extractFunctions (Core.resolved (mkModule dsR) (importedOf mm dsU)) ≡ inj₂ es
       → (mt : ModTele emptyScope es) → MainsEffUU mt → (mi : MainIn mt) → Denoted mm dsU mt mi
denote {mm} {dsU} {dsR} {es} wm wd rds ef mt ms mi =
  go SP.fs SP.es′ SP.ees mt ms mi SP.guard SP.xn SP.ffiE SP.sigk
  where
    module SP = Split wm wd rds ef
    go : ∀ fs es′ {es} → es ≡ fs ++ es′ → (mt : ModTele emptyScope es) → MainsEffUU mt → (mi : MainIn mt)
       → AllPairs _≢_ (names es) → XAlign (Parser.nonSigs dsR) es′ → All Once.Adequacy.SpecFront.Extract.FFIEntry fs
       → (All Once.Adequacy.SpecFront.Extract.FFIFacts fs → Σ[ Σₛ ∈ Signature ] SPr.SignatureOf mm dsU Σₛ
            × (toISig Σₛ ≡ entrySig fs) × (entrySig es ≡ entrySig fs))
       → Denoted mm dsU mt mi
    go fs es′ refl mt ms mi guard xn ffiE sigk = record
      { Σₛ = Σₛ ; wf = wf ; uniq = uniq ; keysW = kw ; sig-eq = eqT
      ; tele = En.End.tl e ; entry = d ; isMain = me ; built = trans (proj₂ (Past.same P mi)) eqP
      ; denotes = record { library = denotesᴹ ms ; entry = proj₂ (proj₂ (proj₂ pe)) } }
      where
        open Parts wm wd rds SP.adj fs es′ mt guard xn ffiE sigk
        pe = En.prog-end Σₛ ps CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) (proj₁ (Past.same P mi)) (Past.u′ P) ks
        d = proj₁ pe
        me = proj₁ (proj₂ pe)
        eqP = proj₁ (proj₂ (proj₂ pe))
