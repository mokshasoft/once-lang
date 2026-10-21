-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Modules — the modules a source may import, read by
-- the compiler and by the Spec (plan 0.121 §3.6, F1).
--
-- The compiler parses each module text (`SpecSource.parseModules`); each
-- parse is the Spec's (`EmbOf.parses-emb`, `Decl.parses→`), so the Spec's
-- module map parses the same texts at the same paths (`ParsesModules`) and
-- is related to the compiler's declaration by declaration (`ModRel`).
-- Conversely (`modules-of←`), each text the Spec parses the compiler parses
-- (`Decl.parses←`, `parseStrict-complete`), into a related map.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Modules where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Parser using (parseStrict)
open import Once.Parser.Module.Core using (Module)
open import Once.Parser.Module.Resolve using (ModuleMap)
import Once.Spec.Surface.Syntax as S
import Once.Spec.Surface.Resolution as SR
open import Once.Spec.Source using (ParsesModules)
open import Once.Adequacy.SpecSource using (parseModules)
open import Once.Adequacy.FrontEndBridge using (parseStrict-sound; parseStrict-complete)
open import Once.Adequacy.SpecGrammar.Decl using (parses→; parses←)
import Once.Spec.Source as SP
import Once.Denotation.Behavior as B
open import Once.Adequacy.SpecSource using (toSource)
open import Once.Adequacy.SpecGrammar.EmbOf using (parses-emb)
open import Once.Adequacy.SpecFront.ModRel using (ModRel)

private
  bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} → (m >>= f) ≡ just b → Σ[ a ∈ A ] (m ≡ just a) × (f a ≡ just b)
  bind-just (just a) f eq = a , refl , eq

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  bind-eq : ∀ {A B : Set} {m : Maybe A} {a} (f : A → Maybe B) → m ≡ just a → (m >>= f) ≡ f a
  bind-eq f refl = refl

-- (mirrors `parseModules`' `with`)
modules-of : ∀ (ms : List (List String × String)) {mm} → parseModules ms ≡ just mm
           → Σ[ mm′ ∈ SR.ModuleMap ] ParsesModules ms mm′ × ModRel mm mm′
modules-of [] refl = [] , [] , []
modules-of ((p , txt) ∷ ms) eq with parseStrict txt in ps
... | inj₂ m =
  let (mm₀ , e₀ , e₁) = bind-just (parseModules ms) _ eq
      (mm′ , pms , mr) = modules-of ms e₀
      pt = parseStrict-sound txt m ps
      (ds′ , em) = parses-emb {txt} pt
  in cons (just-inj e₁) ((refl , parses→ {txt} pt em) ∷ pms) ((refl , em) ∷ mr)
  where
    cons : ∀ {mm mm₁ x mm′} → ((p , m) ∷ mm₁) ≡ mm → ParsesModules ((p , txt) ∷ ms) (x ∷ mm′) → ModRel ((p , m) ∷ mm₁) (x ∷ mm′)
         → Σ[ mm″ ∈ SR.ModuleMap ] ParsesModules ((p , txt) ∷ ms) mm″ × ModRel mm mm″
    cons refl pms mr = _ , pms , mr

-- (mirrors `parseModules`' `with`)
modules-of← : ∀ (ms : List (List String × String)) {mm′} → ParsesModules ms mm′
            → Σ[ mm ∈ ModuleMap ] (parseModules ms ≡ just mm) × ModRel mm mm′
modules-of← [] [] = [] , refl , []
modules-of← ((p , txt) ∷ ms) ((refl , pt) ∷ pms) with parses← {txt} pt
... | m , lt , em rewrite parseStrict-complete txt m lt =
  let (mm , e , mr) = modules-of← ms pms
  in (p , m) ∷ mm , bind-eq (λ mm₁ → just ((p , m) ∷ mm₁)) e , (refl , em) ∷ mr

-- The compiler reads a source the Spec parses.
source-of← : ∀ (src : SP.Source) {mm′} → ParsesModules (SP.Source.modules src) mm′
           → Σ[ mm ∈ ModuleMap ] (toSource src ≡ just (B.mkSource mm (SP.Source.text src))) × ModRel mm mm′
source-of← src pms =
  let (mm , e , mr) = modules-of← (SP.Source.modules src) pms
  in mm , bind-eq (λ mm₁ → just (B.mkSource mm₁ (SP.Source.text src))) e , mr
