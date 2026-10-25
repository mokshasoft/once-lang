-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Modules — the modules a source may import, read by
-- the compiler and by the Spec (plan 0.121 §3.6, F1).
--
-- The compiler parses each module text (`SpecSource.parseModules`); each
-- parse is the Spec's (`Decl.parses→`), so the Spec's module map parses the
-- same texts at the same paths (`ParsesModules`): it is the compiler's map.
-- Conversely (`modules-of←`), each text the Spec parses the compiler parses
-- (`Decl.parses←`, `parseStrict-complete`), into the same map.
------------------------------------------------------------------------

module Once.Adequacy.SpecFront.Modules where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Once.Parser using (parseStrict)
open import Once.Spec.Surface.Syntax using (Module)
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

private
  bind-just : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) {b} → (m >>= f) ≡ just b → Σ[ a ∈ A ] (m ≡ just a) × (f a ≡ just b)
  bind-just (just a) f eq = a , refl , eq

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

  bind-eq : ∀ {A B : Set} {m : Maybe A} {a} (f : A → Maybe B) → m ≡ just a → (m >>= f) ≡ f a
  bind-eq f refl = refl

-- (mirrors `parseModules`' `with`)
modules-of : ∀ (ms : List (List String × String)) {mm} → parseModules ms ≡ just mm → ParsesModules ms mm
modules-of [] refl = []
modules-of ((p , txt) ∷ ms) eq with parseStrict txt in ps
... | inj₂ m =
  let (mm₀ , e₀ , e₁) = bind-just (parseModules ms) _ eq
  in cons (just-inj e₁) ((refl , parses→ {txt} (parseStrict-sound txt m ps)) ∷ modules-of ms e₀)
  where
    cons : ∀ {mm mm₁} → ((p , m) ∷ mm₁) ≡ mm → ParsesModules ((p , txt) ∷ ms) ((p , m) ∷ mm₁) → ParsesModules ((p , txt) ∷ ms) mm
    cons refl pms = pms

modules-of← : ∀ (ms : List (List String × String)) {mm} → ParsesModules ms mm → parseModules ms ≡ just mm
modules-of← [] [] = refl
modules-of← ((p , txt) ∷ ms) {(_ , m) ∷ mm} ((refl , pt) ∷ pms) rewrite parseStrict-complete txt m (parses← {txt} pt) =
  bind-eq (λ mm₁ → just ((p , m) ∷ mm₁)) (modules-of← ms pms)

-- The compiler reads a source the Spec parses.
source-of← : ∀ (src : SP.Source) {mm} → ParsesModules (SP.Source.modules src) mm
           → toSource src ≡ just (B.mkSource mm (SP.Source.text src))
source-of← src pms = bind-eq (λ mm₁ → just (B.mkSource mm₁ (SP.Source.text src))) (modules-of← (SP.Source.modules src) pms)
