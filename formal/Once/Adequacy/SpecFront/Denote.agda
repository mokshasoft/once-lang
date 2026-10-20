-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Denote — a module the compiler types denotes, in
-- the Spec, the program the compiler builds (plan 0.121 §3.6, F6).
--
-- From the compiler's reading of a module — its declarations as written
-- (`dsU`, related to the Spec's `ds′` by `DEmb`), resolved (`dsR`), extracted
-- into entries and typed as a telescope (`ModTele`) with a `main` — the
-- Spec's `Denotes`: the signature (`SigOf`), the resolution (`Resolve`), the
-- walk (`Walk`, from the FFI declarations' scope, `Prefix`/`Start`), its
-- names (`EndNames`, `SigFacts`), its entry (`End`); the program is the
-- compiler's core program translated (`programS`), the one `toProgram`
-- builds (`same`).
--
-- One parameter is still owed (plan 0.121 R13): a generator the compiler
-- finds by its RENDERED name is the Spec declaration of that name.
------------------------------------------------------------------------

open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Once.Spec.Numerics using (TargetNum)
open import Once.Spec.Signature using (Signature; _∶_)
open import Once.Lang.Name using (showCanonical)
open import Once.Adequacy.SpecInterp using (toISig)
open import Once.Adequacy.SpecCore.Poly using (declS)

module Once.Adequacy.SpecFront.Denote
  (fmt : TargetNum)
  -- R13: a generator found by its rendered name is Σ's declaration of that name
  (sigop-R13 : ∀ (Σ : Signature) {c A} → (showCanonical c , A) ∈ toISig Σ → (c ∶ declS A) ∈ Σ)
  where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using ([]; _∷_; _++_; _ʳ++_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
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
import Once.Lang.Core.PolyTy as LP
import Once.Lang.Core.Telescope as TL
import Once.Parser as Parser
open import Once.Parser.Module.Core using (Decl; mkModule)
open import Once.Parser.Module.Resolve using (ModuleMap; polyDefNames; collectUnaliased; collectAliases)
import Once.Lang.Resolution as LR
open import Once.Lang.Module using (ModTele; MainIn; emptyScope; entrySig)
open import Once.Lang.Core.Translate using (toProgram; [])
import Once.Lang.Core.Translate
import Data.Empty
open import Once.Postulates using (extensionality)
import Once.Spec.Core.Syntax
import Data.List.Relation.Unary.All
import Once.Spec.Name
import Once.Adequacy.SpecFront.Polys
open import Once.Adequacy.ModuleLaws using (teleSig≡entrySig)
import Once.Adequacy.NameClash as NC
open import Once.Adequacy.SpecGrammar.Decl using (DEmb)
open import Once.Adequacy.SpecCore.Schema using (defsS)
import Once.Adequacy.SpecCore.Program as PG
open import Once.Adequacy.SpecFront.ModRel using (ModRel)
open import Once.Adequacy.SpecFront.Extract using (XAlign; extract-align; nonSigs-none)
import Once.Adequacy.SpecFront.Resolve as Res
import Once.Adequacy.SpecFront.SigOf as SigOf
open import Once.Adequacy.SpecFront.SigFacts using (keys; keys-distinct; uniq-of; one-name; h-sig-of)
open import Once.Adequacy.SpecFront.SigWF using (wf-of)
open import Once.Adequacy.SpecFront.Prefix using (Past; past; prefix; ffi-facts)
open import Once.Adequacy.SpecFront.Start using (names; distinct-rest; nosig-rest; fresh-start; not-sig)
open import Once.Adequacy.SpecFront.Polys using (Adj; adj-of; pdn-res; pdn-xa; polyNames; poly-names; kinds-of; defs-of)
import Once.Adequacy.SpecFront.Align as Al
import Once.Adequacy.SpecFront.WalkState as WS
import Once.Adequacy.SpecFront.Walk as Wk
import Once.Adequacy.SpecFront.End as En
import Once.Adequacy.SpecFront.EndNames as EN

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
      dist-ok : ∀ b {es′} → Parser.distinctOrErr b (inj₂ es) ≡ inj₂ es′ → inj₂ es ≡ inj₂ es′
      dist-ok true  e′ = e′
      dist-ok false ()

------------------------------------------------------------------------
-- The denotation
------------------------------------------------------------------------

private
  noCF : ∀ {Fs} → Once.Lang.Core.Translate.SigCF (LP.[] {Fs = Fs})
  noCF ()

  noNames : Fin 0 → CanonicalName
  noNames ()

-- What the Spec's module denotes, and that it is the compiler's program.
record Denoted (mm′ : SR.ModuleMap) (ds′ : List S.Decl) {es} (mt : ModTele emptyScope es) (mi : MainIn mt) : Set where
  field
    Σₛ      : Signature
    wf      : WellFormed Σₛ
    sig-eq  : Once.Lang.Module.teleSig mt ≡ toISig Σₛ
    program : CoreProgram.Program Σₛ
    denotes : SPr.Denotes mm′ (S.mkModule ds′) Σₛ program
    same    : program ≡ PG.programS Σₛ (sigop-R13 Σₛ) fmt wf
                          (toProgram {S = LP.[] {Fs = toISig Σₛ}} TL.[] [] [] [] noCF mt mi (λ m → subst (_ ∈_) sig-eq m))

denote : ∀ {mm mm′ dsU dsR ds′ es}
       → ModRel mm mm′ → ¬ ("main" ∈ polyDefNames dsU)
       → LR.ResolvesDecls mm (polyDefNames dsU) (collectUnaliased mm dsU) (collectAliases dsU) dsU dsR
       → Pointwise DEmb dsU ds′
       → Parser.extractFunctions (Parser.extractAliases (mkModule dsR)) (mkModule dsR) ≡ inj₂ es
       → (mt : ModTele emptyScope es) (mi : MainIn mt) → Denoted mm′ ds′ mt mi
denote {mm} {mm′} {dsU} {dsR} {ds′} {es} mr main∉ rds pw ef mt mi =
  go fs es′ ees mt mi guard xn ffiE sigk
  where
    ps = polyDefNames dsU
    al = Parser.extractAliases (mkModule dsR)
    r₀ = Parser.thenExtract (Parser.sigsAdjacent dsR nothing) (Parser.extractFunctions-go al (Parser.sigsFirst dsR) nothing)
    adjE = proj₁ (then-ok _ _ (guard-ok r₀ ef))
    goE  = proj₂ (then-ok _ _ (guard-ok r₀ ef))
    guard = NC.guard-entries r₀ ef
    sp = SigOf.signature-of ps mr rds pw (extract-align al (Parser.sigsFirst dsR) goE)
    fs = proj₁ sp
    es′ = proj₁ (proj₂ sp)
    ees = proj₁ (proj₂ (proj₂ sp))
    xn = proj₁ (proj₂ (proj₂ (proj₂ sp)))
    ffiE = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ sp))))
    sigk = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ sp))))
    adj = adj-of dsR adjE

    go : ∀ fs es′ {es} → es ≡ fs ++ es′ → (mt : ModTele emptyScope es) (mi : MainIn mt)
       → AllPairs _≢_ (names es) → XAlign al (Parser.nonSigs dsR) es′ → All Once.Adequacy.SpecFront.Extract.FFIEntry fs
       → (All Once.Adequacy.SpecFront.Extract.FFIFacts fs → Σ[ Σₛ ∈ Signature ] SPr.SignatureOf mm′ ds′ Σₛ
            × (toISig Σₛ ≡ entrySig fs) × (entrySig es ≡ entrySig fs))
       → Denoted mm′ ds′ mt mi
    go fs es′ refl mt mi guard xn ffiE sigk = record
      { Σₛ = Σₛ ; wf = wf ; sig-eq = eqT ; program = p ; denotes = den
      ; same = cong (PG.programS Σₛ (sigop-R13 Σₛ) fmt wf) (sym (trans (Past.same P) eqP)) }
      where
        facts = ffi-facts fs ffiE mt
        Σₛ = proj₁ (sigk facts)
        sig = proj₁ (proj₂ (sigk facts))
        tf = proj₁ (proj₂ (proj₂ (sigk facts)))
        te = proj₂ (proj₂ (proj₂ (sigk facts)))
        wf = wf-of Σₛ fs tf facts
        eqT : Once.Lang.Module.teleSig mt ≡ toISig Σₛ
        eqT = trans (teleSig≡entrySig mt) (trans te (sym tf))
        P = prefix {S = LP.[] {Fs = toISig Σₛ}} fs ffiE TL.[] [] [] [] noCF mt mi (λ m → subst (_ ∈_) eqT m)
        sg = entrySig fs ʳ++ []
        ukeys : AllPairs _≢_ (keys (entrySig fs))
        ukeys = subst (λ l → AllPairs _≢_ (keys l)) te (keys-distinct (fs ++ es′) guard)
        guard′ = distinct-rest fs es′ guard
        pdn-eq : ps ≡ polyNames es′
        pdn-eq = trans (pdn-res rds adj) (pdn-xa adj xn)
        h-sig = λ {m} Δ {c} {t} (_ : Once.Spec.Name.NotGenerator c) M → h-sig-of Σₛ fs tf ukeys facts {m} Δ {c} {t} M
        h-own : ∀ {x t} → x ∈ ps → ¬ ((canonical (x ∷ []) ∶ t) ∈ Σₛ)
        h-own {x} x∈ps M = not-sig Σₛ fs es′ tf guard (poly-names es′ (subst (x ∈_) pdn-eq x∈ps)) M
        rd = Res.Decls.res-decls ps main∉ Σₛ rds pw
        dsR′ = proj₁ rd
        align = Al.align-of Σₛ ps (proj₂ (proj₂ rd)) adj xn
        module W = Wk Σₛ (sigop-R13 Σₛ) fmt ps sg h-sig h-own
        eok : W.EntriesOK (Once.Lang.Module.scope sg [] []) es′
        eok = record
          { distinct = guard′ ; fresh = fresh-start es′ ; nosig = nosig-rest fs es′ guard
          ; kinds = subst (λ q → All (Once.Adequacy.SpecFront.Polys.EntryKind q) es′) (sym pdn-eq)
                          (kinds-of es′ guard′ (defs-of (nonSigs-none dsR) xn)) }
        ks = W.EntriesOK.kinds eok
        e = En.endOf Σₛ ps TL.[] (Past.ss′ P) [] [] noCF noNames (Past.mt′ P) ks
        pe = En.prog-end Σₛ ps TL.[] (Past.ss′ P) [] [] noCF noNames (Past.mt′ P) (Past.mi′ P) (Past.u′ P) ks
        d = proj₁ pe
        me = proj₁ (proj₂ pe)
        eqP = proj₁ (proj₂ (proj₂ pe))
        p = PG.programS Σₛ (sigop-R13 Σₛ) fmt wf (TL.program (En.End.tl e) d me)
        w = W.walk TL.[] (Past.ss′ P) [] [] noCF noNames (Past.mt′ P) align (WS.winv-empty Σₛ ps) eok
        den : SPr.Denotes mm′ (S.mkModule ds′) Σₛ p
        den = record
          { signature = sig
          ; unaliased = collectUnaliased mm dsU
          ; unaliases = Res.unaliased-of ps main∉ mr rds pw
          ; resolved  = dsR′
          ; resolves  = subst (λ a → SPr.ResolvesDecls (SR.env (collectUnaliased mm dsU) a) ds′ dsR′) (Res.aliases-eq ps main∉ pw)
                              (proj₁ (proj₂ rd))
          ; names     = En.End.nm e
          ; walk      = subst (λ n → SPr.Walk Σₛ (defsS (LP.[] {Fs = toISig Σₛ})) n (PG.teleS Σₛ (sigop-R13 Σₛ) fmt TL.[]) dsR′
                                         (defsS (En.End.S e)) (En.End.nm e) (PG.teleS Σₛ (sigop-R13 Σₛ) fmt (En.End.tl e))) fin0-ext w
          ; distinct  = EN.distinct-end Σₛ ps TL.[] (Past.ss′ P) [] [] noCF noNames (Past.mt′ P) ks
                          (λ {x} → Data.Empty.⊥-elim (fin0 x)) guard′ (Data.List.Relation.Unary.All.tabulate (λ _ ()))
          ; sig-distinct = one-name Σₛ (uniq-of Σₛ (fs ++ es′) (trans tf (sym te)) guard)
          ; def-not-sig  = λ dd M → not-def dd M
          ; entry     = proj₂ (proj₂ (proj₂ pe))
          }
          where
            fin0 : Fin 0 → Data.Empty.⊥
            fin0 ()
            -- (two namings of no definitions, by P1)
            fin0-ext : ∀ {g : Fin 0 → CanonicalName} → noNames ≡ g
            fin0-ext = extensionality (λ ())
            not-def : ∀ dd {t} → ¬ ((En.End.nm e dd ∶ t) ∈ Σₛ)
            not-def dd M = pick (EN.named-end Σₛ ps TL.[] (Past.ss′ P) [] [] noCF noNames (Past.mt′ P) ks {L = []} (λ ()) dd) M
              where
                pick : ∀ {c t} → Σ[ x ∈ String ] (c ≡ canonical (x ∷ [])) × (x ∈ [] ⊎ x ∈ names es′) → ¬ ((c ∶ t) ∈ Σₛ)
                pick (x , ex , inj₁ ()) M′
                pick (x , ex , inj₂ mx) M′ = not-sig Σₛ fs es′ tf guard mx (subst (λ c → (c ∶ _) ∈ Σₛ) ex M′)
