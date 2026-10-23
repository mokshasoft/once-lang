-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.ScopeNames — what the compiler's scope finds is the
-- Spec's definition of that name (plan 0.121 §3.6, F6).
--
-- The compiler's telescope walk records, for every definition in scope, the
-- core entry it is (`Translate.ImpSig`/`TeleSig`); the Spec's walk names
-- every entry (`nm`). The two agree when each recorded entry is named the
-- definition's name (`ImpNamed`/`TeleNamed`); then the entry a lookup finds is
-- named the name looked up (`h-imp-of`, `h-poly-of`) — the front-end bridge's
-- scope facts about names.
--
-- (The lookups are the compiler's, written with `with`; these follow them.)
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
import Once.Spec.Core.Syntax as LP

module Once.Adequacy.SpecFront.ScopeNames
  (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Data.String.Properties as StrProp

import Once.Compile as C
import Once.Parser as Parser
open Parser.PolyFunInfo using (pfunName)
open import Once.Spec.Name using (canonical)
open import Once.Internal.Typing.Scope using (lookupImport; lookupPolyPrefix)
open import Once.Internal.Core.Translate Σ using (ImpSig; TeleSig; []; i-def; t-def; impAt; telFind; monoSchema)
import Once.TypeCheck.View as TView

private
  module VS = TView Σ S

-- Every recorded monomorphic entry is named its definition's name.
ImpNamed : ∀ {imps} → ImpSig S imps → Set
ImpNamed []                       = ⊤
ImpNamed (i-def {x = x} d e is)   = (nm d ≡ canonical (x ∷ [])) × ImpNamed is

-- Every recorded telescope entry is named its definition's name.
TeleNamed : ∀ {ps} → TeleSig S ps → Set
TeleNamed []                      = ⊤
TeleNamed (t-def {p = p} d e ts)  = (nm d ≡ canonical (pfunName p ∷ [])) × TeleNamed ts

-- A monomorphic definition found by name: named so, and without type variables.
h-imp-of : ∀ {imps} (is : ImpSig S imps) → ImpNamed is → ∀ {x T} (lk : lookupImport imps x ≡ just T)
         → (nm (VS.ImportAt.entryOf (impAt is lk)) ≡ canonical (x ∷ []))
           × (LP.Schema.arity (S LP.!! VS.ImportAt.entryOf (impAt is lk)) ≡ 0)
h-imp-of [] _ ()
h-imp-of {(n , T₀) ∷ rest} (i-def d e is) (nd , ns) {x} lk with StrProp._≟_ n x
... | yes refl with just-injective lk
...   | refl = nd , cong LP.Schema.arity e
h-imp-of {(n , T₀) ∷ rest} (i-def d e is) (nd , ns) {x} lk | no _ = h-imp-of is ns lk

-- A telescope definition found by name: named so.
h-poly-of : ∀ {ps} (ts : TeleSig S ps) → TeleNamed ts → ∀ {x sc body prefix}
          → (lp : lookupPolyPrefix (C.buildPolyCtx ps) x ≡ just (sc , body , prefix))
          → nm (proj₁ (telFind ts lp)) ≡ canonical (x ∷ [])
h-poly-of [] _ ()
h-poly-of {p ∷ ps} (t-def d e ts) (nd , ns) {x} lp with StrProp._≟_ (pfunName p) x
... | yes refl with just-injective lp
...   | refl = nd
h-poly-of {p ∷ ps} (t-def d e ts) (nd , ns) {x} lp | no _ = h-poly-of ts ns lp
