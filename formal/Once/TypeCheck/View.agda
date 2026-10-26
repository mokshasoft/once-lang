-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.View — the checker's scope read through a table of
-- definitions (plan 0.103 phase 6b; plan 0.122 §2b-3).
--
-- A View resolves each name the checker's scope binds to what the Spec
-- reads: an imported name to an honest, ground FFI declaration of Σ (D231)
-- or one of the module's own definitions, and each telescope entry to its
-- index in the definitions table, whose schema is the entry's (`entryIs`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)

module Once.TypeCheck.View (Σ : Signature) {s : ℕ} (S : Defs s) where

open import Data.Fin using (Fin)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Once.Spec.Type using (Type; ∅ₖ)
open import Once.Spec.Signature using (_∶_)
open import Once.Spec.Core.Syntax using (schema; _!!_)
open import Once.Name using (showCanonical; WordName)
open import Once.Type.Honest using (HonestFFI)
open import Once.Type.Schema using (schemaOf)
open import Once.Core.Decl using (declS)
open import Once.TypeCheck.Scope using (NamedCtx; Imports; PolyCtx; lookupImport; lookupPolyPrefix)

-- An FFI declaration: honest (D231), and a declaration of Σ under its name.
record Declared (x : String) (T : Type) : Set where
  constructor declared
  field
    honest : HonestFFI T
    member : ∀ {c} → WordName c → showCanonical c ≡ x → (c ∶ declS T) ∈ Σ

-- One of the module's own monomorphic definitions: an entry of the table at
-- its (ground) type.
record ImportAt (x : String) (T : Type) : Set where
  constructor def
  field
    entryOf : Fin s
    mono    : S !! entryOf ≡ schema 0 ∅ₖ T

record View (imps : Imports) (sg : Imports) (polys : PolyCtx) : Set where
  field
    imported : ∀ {x T} → lookupImport imps x ≡ just T → ImportAt x T
    declares : ∀ {x T} → lookupImport sg x ≡ just T → Declared x T
    entry    : ∀ {x sc body prefix} → lookupPolyPrefix polys x ≡ just (sc , body , prefix) → Fin s
    entryIs  : ∀ {x sc body prefix} (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix))
             → S !! entry lp ≡ schemaOf sc
open View

Views : ∀ {m} → NamedCtx m → Set
Views ctx = View (NamedCtx.imports ctx) (NamedCtx.sig ctx) (NamedCtx.polys ctx)

-- An entry a View finds: a monomorphic definition's, or a telescope
-- definition's — the entries a reference the checker builds names, each with
-- the lookups the checker made first (a name is a declaration of the scope's
-- signature before a definition, a monomorphic definition before a
-- telescope one).
data InView {imps sg polys} (V : View imps sg polys) (d : Fin s) : Set where
  iv-imp  : ∀ {x T} → lookupImport sg x ≡ nothing
          → (lk : lookupImport imps x ≡ just T) → ImportAt.entryOf (imported V lk) ≡ d → InView V d
  iv-poly : ∀ {x sc body prefix} → lookupImport sg x ≡ nothing → lookupImport imps x ≡ nothing
          → (lp : lookupPolyPrefix polys x ≡ just (sc , body , prefix)) → entry V lp ≡ d → InView V d

