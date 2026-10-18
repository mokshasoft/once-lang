-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecGrammar.SigTypes — a signature's type: the compiler's
-- schema grammar (`Once.Parser.Generic.PolyInst`) is the Spec's
-- (`SigType`), schemas read across by `toPoly`.
------------------------------------------------------------------------

module Once.Adequacy.SpecGrammar.SigTypes where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import Once.Spec.Surface.Lexing using (Token; TWord)
open import Once.Spec.Surface.Grammar using (TypeAlg; module SigType; TypeVar; tvar; lowerWord)
import Once.Spec.Surface.Syntax as SS
import Once.Parser.Token as P
open import Once.Parser.CharClass using (isLowerWord)
open import Once.Parser.Generic.PolyInst using (PolyAlg; TVarRel; ParsesPolyType)
import Once.Parser.Generic.PolyInst as PI
open import Once.Adequacy.SpecGrammar.Tokens using (forget; step)
open import Once.Adequacy.SpecGrammar.Conv using (toPoly; toPolyF)
open import Once.Adequacy.SpecGrammar.GenTypes using (Hom; module Bridge)

private
  F : List P.Token → List Token
  F = map forget

  lower-go : ∀ s cs → toList s ≡ cs → isLowerWord s ≡ lowerWord s
  lower-go s []      e rewrite e = refl
  lower-go s (c ∷ _) e rewrite e = refl

lower-eq : ∀ s → isLowerWord s ≡ lowerWord s
lower-eq s = lower-go s (toList s) refl

-- The Spec's algebra of written schemas (`Once.Spec.Surface.Grammar`'s,
-- which is private there).
writtenS : (List Token → SS.PolyType → List Token → Set) → TypeAlg SS.PolyType SS.PolyFunctor
writtenS X = record
  { aUnit = SS.PUnit ; aVoid = SS.PVoid ; aInt = SS.PInt ; aFloat = SS.PFloat
  ; aProd = SS._P*_ ; aSum = SS._P+_ ; aEff = SS.PEff ; aAct = SS.PAct
  ; aArrow = λ q A B → A SS.P⇒[ q ] B ; aMu = SS.Pμ ; aNu = λ π F → SS.Pν F π
  ; fK = SS.PK ; fId = SS.PId ; fSum = SS._P⊕_ ; fProd = SS._P⊗_
  ; Extra = X }

private
  var← : ∀ {ts a′ r′} → TypeVar ts a′ r′ → ∀ toks → F toks ≡ ts
       → Σ[ a ∈ _ ] Σ[ rest ∈ List P.Token ] (TVarRel toks a rest × toPoly a ≡ a′ × F rest ≡ r′)
  var← (tvar {x} lw) toks e =
    step (λ y → Σ[ a ∈ _ ] Σ[ rest ∈ List P.Token ] (TVarRel y a rest × toPoly a ≡ SS.PTVar x × F rest ≡ _)) refl e
      (λ {toks′} e′ → _ , toks′ , PI.tvar (trans (lower-eq x) lw) , refl , e′)

homPoly : Hom PolyAlg (writtenS TypeVar) toPoly toPolyF
homPoly = record
  { h-unit = refl ; h-void = refl ; h-int = refl ; h-float = refl
  ; h-prod = λ _ _ → refl ; h-sum = λ _ _ → refl ; h-eff = λ _ _ → refl ; h-act = λ _ _ → refl
  ; h-arrow = λ _ _ _ → refl
  ; h-mu = λ _ → refl ; h-nu = λ _ → refl ; h-nuact = λ _ → refl
  ; hF-k = λ _ → refl ; hF-id = refl ; hF-sum = λ _ _ → refl ; hF-prod = λ _ _ → refl
  ; extra→ = λ { (PI.tvar {name} lw) → tvar (trans (sym (lower-eq name)) lw) }
  ; extra← = var←
  }

private
  module B = Bridge PolyAlg (writtenS TypeVar) toPoly toPolyF homPoly

sig→ : ∀ {toks A rest} → ParsesPolyType toks A rest → SigType.ParsesType (F toks) (toPoly A) (F rest)
sig→ = B.type→

sig← : ∀ {ts A′ r′} → SigType.ParsesType ts A′ r′ → ∀ toks → F toks ≡ ts
     → Σ[ A ∈ _ ] Σ[ rest ∈ List P.Token ] (ParsesPolyType toks A rest × toPoly A ≡ A′ × F rest ≡ r′)
sig← = B.type←
