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
-- names (`EndNames`, `SigFacts`), its entry (`End`); the program is the
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
import Once.Internal.Core.Telescope as TL
import Once.Parser as Parser
open import Once.Spec.Surface.Syntax using (Decl; mkModule)
import Once.Parser.Module.Core as Core
open import Once.Parser.Module.Resolve using (ModuleMap; collectUnaliased; collectAliases; importedOf)
import Once.Internal.Resolution as LR
open import Once.Module using (ModTele; MainIn; emptyScope; entrySig)
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
       → (mt : ModTele emptyScope es) (mi : MainIn mt) → Denoted mm dsU mt mi
denote {mm} {dsU} {dsR} {es} wm wd rds ef mt mi =
  go fs es′ ees mt mi guard xn ffiE sigk
  where
    r₀ = Parser.thenExtract (Parser.sigsAdjacent dsR nothing) (Parser.extractFunctions-go (Parser.sigsFirst dsR (importedOf mm dsU)) nothing)
    adjE = proj₁ (then-ok _ _ (guard-ok r₀ ef))
    goE  = proj₂ (then-ok _ _ (guard-ok r₀ ef))
    guard = NC.guard-entries r₀ ef
    sp = SigOf.signature-of rds (extract-align (Parser.sigsFirst dsR (importedOf mm dsU)) goE)
    fs = proj₁ sp
    es′ = proj₁ (proj₂ sp)
    ees = proj₁ (proj₂ (proj₂ sp))
    xn = proj₁ (proj₂ (proj₂ (proj₂ sp)))
    ffiE = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ sp))))
    sigk = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ sp))))
    adj = adj-of dsR adjE

    go : ∀ fs es′ {es} → es ≡ fs ++ es′ → (mt : ModTele emptyScope es) (mi : MainIn mt)
       → AllPairs _≢_ (names es) → XAlign (Parser.nonSigs dsR) es′ → All Once.Adequacy.SpecFront.Extract.FFIEntry fs
       → (All Once.Adequacy.SpecFront.Extract.FFIFacts fs → Σ[ Σₛ ∈ Signature ] SPr.SignatureOf mm dsU Σₛ
            × (toISig Σₛ ≡ entrySig fs) × (entrySig es ≡ entrySig fs))
       → Denoted mm dsU mt mi
    go fs es′ refl mt mi guard xn ffiE sigk = record
      { Σₛ = Σₛ ; wf = wf ; uniq = uniq-of Σₛ (fs ++ es′) (trans tf (sym te)) guard ; keysW = kw ; sig-eq = eqT
      ; tele = En.End.tl e ; entry = d ; isMain = me ; built = trans (Past.same P) eqP ; denotes = den }
      where
        facts = ffi-facts fs ffiE mt
        Σₛ = proj₁ (sigk facts)
        sig = proj₁ (proj₂ (sigk facts))
        tf = proj₁ (proj₂ (proj₂ (sigk facts)))
        te = proj₂ (proj₂ (proj₂ (sigk facts)))
        wf = wf-of Σₛ fs tf facts
        kw = signature-words wm wd sig
        eqT : Once.Module.teleSig mt ≡ toISig Σₛ
        eqT = trans (teleSig≡entrySig mt) (trans te (sym tf))
        P = prefix Σₛ {S = SC.[]} fs ffiE CoreProgram.[] [] [] [] (names₀ Σₛ) mt mi (λ m → sig-in Σₛ (key-word kw) (subst (_ ∈_) eqT m))
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
        pe = En.prog-end Σₛ ps CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) (Past.mi′ P) (Past.u′ P) ks
        d = proj₁ pe
        me = proj₁ (proj₂ pe)
        eqP = proj₁ (proj₂ (proj₂ pe))
        p = PG.programS Σₛ fmt wf (TL.program (En.End.tl e) d me)
        w = W.walk CoreProgram.[] (Past.ss′ P) [] [] (names₀ Σₛ) (Past.mt′ P) align (WS.winv-empty Σₛ ps) eok
        den : SPr.Denotes mm (S.mkModule dsU) Σₛ p
        den = record
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
          ; sig-distinct = one-name Σₛ (uniq-of Σₛ (fs ++ es′) (trans tf (sym te)) guard)
          ; def-not-sig  = λ dd M → not-def dd M
          ; entry     = proj₂ (proj₂ (proj₂ pe))
          }
          where
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
