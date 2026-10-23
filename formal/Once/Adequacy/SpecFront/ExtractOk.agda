-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ExtractOk — the extractor succeeds on a module the
-- Spec reads (plan 0.121 `complete`; the converse of `Denote`'s use of the
-- extractor).
--
-- The FFI declarations' entries (`SigOfBack`) come first, then the
-- definitions' (`ExtractBack.xalign-of`, for the Spec's walk keeps each
-- type signature before its definition), and the guard admits them all
-- (`GuardBack`): the entries hold Σ's rendered names and the walk's
-- definitions' names, each list apart, and apart from each other.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.ExtractOk where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Function using (Injective)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature; WellFormed; OneName; _∶_)
import Once.Spec.Surface.Program as SPr
import Once.Internal.Resolution as LR
import Once.Parser as Parser
open import Once.Parser using (Entry; entryNameOf)
open import Once.Parser.Module.Core using (Decl; mkModule)
open import Once.Internal.Module using (entrySig)
open import Once.Internal.Core.Decl using (toISig)
open import Once.Adequacy.SpecGrammar.Decl using (DEmb)
open import Once.Adequacy.SpecFront.ModRel using (ModRel)
open import Once.Adequacy.SpecFront.Extract using (XAlign; xa-nil; xa-pass; xa-sig; xa-isig; IsSig; is-sig; own-sigs; imported-sigs; nonSigs-none; ffi-of; FFIFacts)
open import Once.Adequacy.SpecFront.ExtractBack using (align-extract; adj-ok; walk-adj; dr-adj; nonSigs-adj; xalign-of)
open import Once.Adequacy.SpecFront.SigOf using (own-res)
open import Once.Adequacy.SpecFront.SigOfBack using (xa-++; sigs-table-++; toISig-++; wf-++; own-part←; imp-part←; all-++)
open import Once.Adequacy.SpecFront.SigFacts using (keys; rname; toISig-keys)
open import Once.Adequacy.SpecFront.Words using (ModsW; DeclW; signature-idents; signature-words; key-word)
open import Once.Adequacy.SpecFront.GuardBack
  using (names; guard←; rnames-distinct; def-not-key; defNamesS; walk-distinct; walk-named; res-names; def-names;
         xa-names; nonSigs-names; dr-names)
open import Once.Adequacy.SpecFront.Align using (DR)

private
  -- the FFI declarations' entries are named by their table
  sig-names : ∀ {sigs fs} → All IsSig sigs → XAlign sigs fs → names fs ≡ keys (entrySig fs)
  sig-names []           xa-nil        = refl
  sig-names (is-sig ∷ a) (xa-pass () _)
  sig-names (is-sig ∷ a) (xa-sig _ x)  = cong (_ ∷_) (sig-names a x)
  sig-names (is-sig ∷ a) (xa-isig _ x) = cong (_ ∷_) (sig-names a x)

  zip : ∀ {A : Set} {P Q R : A → Set} → (∀ {x} → P x → Q x → R x) → ∀ {xs} → All P xs → All Q xs → All R xs
  zip f []       []       = []
  zip f (p ∷ ps) (q ∷ qs) = f p q ∷ zip f ps qs

  ap-++ : ∀ {A : Set} (xs : List A) {ys} → AllPairs _≢_ xs → AllPairs _≢_ ys → All (λ x → All (x ≢_) ys) xs
        → AllPairs _≢_ (xs ++ ys)
  ap-++ []       _                                     v _        = v
  ap-++ (x ∷ xs) (Data.List.Relation.Unary.AllPairs._∷_ a u) v (d ∷ ds) =
    Data.List.Relation.Unary.AllPairs._∷_ (AllP.++⁺ a d) (ap-++ xs u v ds)
    where import Data.List.Relation.Unary.AllPairs

-- What the extractor makes of the module: the FFI declarations' entries,
-- then the definitions'.
record Extracted (dsR : List Decl) (Σ : Signature) : Set where
  field
    fs esN    : List Entry
    extracted : Parser.extractFunctions (mkModule dsR) ≡ inj₂ (fs ++ esN)
    sigs      : XAlign (Parser.ownSigs dsR ++ Parser.importedSigs dsR) fs
    defs      : XAlign (Parser.nonSigs dsR) esN
    table     : toISig Σ ≡ entrySig fs
    facts     : All FFIFacts fs
    distinct  : AllPairs _≢_ (names (fs ++ esN))

extract-ok : ∀ {mm mm′ um am dsU dsR ds′ dsR′ Σ E s′} {S′ : _} {nm′ : Fin s′ → CanonicalName} {tl′}
               {S₀ : _} {nm₀ : Fin 0 → CanonicalName} {tl₀}
           → ModsW mm′ → All DeclW ds′ → ModRel mm mm′ → LR.ResolvesDecls mm um am dsU dsR → Pointwise DEmb dsU ds′
           → SPr.ResolvesDecls E ds′ dsR′ → DR Σ dsR′ dsR
           → SPr.SignatureOf mm′ ds′ Σ → WellFormed Σ → OneName Σ
           → SPr.Walk Σ S₀ nm₀ tl₀ dsR′ S′ nm′ tl′ → Injective _≡_ _≡_ nm′ → (∀ i {t} → ¬ ((nm′ i ∶ t) ∈ Σ))
           → Extracted dsR Σ
extract-ok {dsR = dsR} {dsR′ = dsR′} {Σ = Σ} wm wd mr rds pw rd dr sig@(Σ₀ , Σᵢ , so , im , refl) wf one w inj ns =
  record
    { fs = fs ; esN = esN
    ; extracted = trans (cong₂ (λ a r → Parser.guardDistinct (Parser.thenExtract a r)) (adj-ok adj) (align-extract xw))
                        (guard← fs esN (ffi-of isF xs) (proj₁ xn) distinct (subst (All _) (sym eN) vN))
    ; sigs = xs ; defs = xN ; table = table ; facts = all-++ (proj₂ (proj₂ (proj₂ p₀))) (proj₂ (proj₂ (proj₂ pᵢ))) ; distinct = distinct }
  where
    w₀ = proj₁ (wf-++ Σ₀ wf)
    wᵢ = proj₂ (wf-++ Σ₀ wf)
    p₀ = own-part← pw so w₀
    pᵢ = imp-part← mr rds pw im wᵢ
    fs₀ = proj₁ p₀
    fsᵢ = proj₁ pᵢ
    x₀ : XAlign (Parser.ownSigs dsR) fs₀
    x₀ = subst (λ l → XAlign l fs₀) (sym (own-res rds)) (proj₁ (proj₂ p₀))
    xᵢ = proj₁ (proj₂ pᵢ)
    adj = dr-adj Σ dr (walk-adj w)
    pN = xalign-of (nonSigs-adj adj) (nonSigs-none dsR)
    esN = proj₁ pN
    xN = proj₂ pN
    fs = fs₀ ++ fsᵢ
    xs = xa-++ x₀ xᵢ
    xw : XAlign (Parser.sigsFirst dsR) (fs ++ esN)
    xw = subst (XAlign (Parser.sigsFirst dsR)) (sym (++-assoc fs₀ fsᵢ esN)) (xa-++ x₀ (xa-++ xᵢ xN))
    isF = AllP.++⁺ (own-sigs dsR) (imported-sigs dsR)
    table : toISig Σ ≡ entrySig fs
    table = trans (toISig-++ Σ₀ Σᵢ)
                  (trans (cong₂ _++_ (proj₁ (proj₂ (proj₂ p₀))) (proj₁ (proj₂ (proj₂ pᵢ)))) (sym (sigs-table-++ (own-sigs dsR) x₀ fsᵢ)))
    -- the names
    L = defNamesS dsR′
    xn = xa-names xN (nonSigs-none dsR)
    eN : names esN ≡ L
    eN = trans (proj₂ xn) (trans (nonSigs-names dsR) (dr-names Σ dr))
    eF : names fs ≡ map rname Σ
    eF = trans (sig-names isF xs) (trans (cong keys (sym table)) (toISig-keys Σ))
    vN = subst (All _) (sym (res-names rd)) (def-names wd)
    ki = signature-idents wm wd sig
    kw = signature-words wm wd sig
    cross : All (λ k → All (k ≢_) L) (map rname Σ)
    cross = AllP.map⁺ (All.tabulate (λ m → zip (def-not-key m (All.lookup ki m) (key-word kw m)) vN (walk-named w ns)))
    distinct : AllPairs _≢_ (names (fs ++ esN))
    distinct = subst (AllPairs _≢_) (sym (trans (map-++ entryNameOf fs esN) (cong₂ _++_ eF eN)))
                     (ap-++ (map rname Σ) (rnames-distinct kw one) (walk-distinct w inj) cross)
