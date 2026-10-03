-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.EntriesValid — every name a module may DEFINE is an
-- identifier: the extractor's guard, read back. A name that is not one (a
-- qualified `alias.name`, a resolved path, the empty name) can therefore only
-- be an FFI declaration's (plan 0.105: an import of the interpretation
-- signatures the program is compiled against).
------------------------------------------------------------------------

module Once.Adequacy.EntriesValid where

open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Sum using (inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import Once.Compile as C
open C.FunInfo using (funName; funIsPrimitive)
import Once.Parser
open import Once.Parser using (validIdentB; validCharsB; allIdentContinue)
open import Data.Bool using (_∧_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Char using (Char)
open import Data.String using (toList) renaming (_++_ to _++ˢ_)
open import Data.String.Unsafe using (toList-++)
open import Data.List using (_++_)
open import Relation.Binary.PropositionalEquality using (cong)
import Once.Parser.Module.Core as P
import Once.Adequacy.NameClash as NC

MonoValid : C.Entry → Set
MonoValid (C.e-fun fi)   = funIsPrimitive fi ≡ false → validIdentB (funName fi) ≡ true
MonoValid (C.e-poly pfi) = ⊤

valid-of : ∀ (es : List C.Entry) → Once.Parser.allValidIdentB (Once.Parser.emittedNames (Once.Parser.funsOf es)) ≡ true
         → All MonoValid es
valid-of []                   eq = []
valid-of (C.e-poly pfi ∷ es) eq = tt ∷ valid-of es eq
valid-of (C.e-fun fi ∷ es)   eq with funIsPrimitive fi in ep
... | true  = (λ p → case trans (sym ep) p of λ ()) ∷ valid-of es eq
... | false = (λ _ → NC.∧-elimˡ eq) ∷ valid-of es (NC.∧-elimʳ eq)

valid-mod : ∀ (m : P.Module) {es} → C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → All MonoValid es
valid-mod (P.mkModule ds) {es} eq = valid-of es (NC.∧-elimʳ (NC.guard-true (C.extractFunctions-go (C.extractAliases (P.mkModule ds)) ds C.nothing) eq))

private
  cont-dot : ∀ (cs ds : List Char) → allIdentContinue (cs ++ '.' ∷ ds) ≡ false
  cont-dot []       ds = refl
  cont-dot (c ∷ cs) ds = trans (cong (_ ∧_) (cont-dot cs ds)) (∧-zeroʳ _)

  chars-dot : ∀ (cs ds : List Char) → validCharsB (cs ++ '.' ∷ ds) ≡ false
  chars-dot []       ds = refl
  chars-dot (c ∷ cs) ds = trans (cong (_ ∧_) (cont-dot cs ds)) (∧-zeroʳ _)

-- A dotted name is not an identifier.
dot-invalid : ∀ (a b : String) → validIdentB (a ++ˢ "." ++ˢ b) ≡ false
dot-invalid a b =
  trans (cong validCharsB (trans (toList-++ a ("." ++ˢ b)) (cong (toList a ++_) (toList-++ "." b))))
        (chars-dot (toList a) (toList b))
