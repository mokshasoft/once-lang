-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.ResolverBridge — the NAMED resolver-correctness obligations
-- (Plan 0.51, scaffold stage).
--
-- The import resolver (`Once.Parser.Module.Resolve.resolveImports`) is now
-- INSIDE the verified front-end (`Once.Adequacy.SourceTrace.srcToModule`), so
-- the verified `compile` compiles the SAME resolved module the binary runs
-- ("certified == shipped"). But the apex's INDEPENDENT meaning is anchored on
-- the UN-RESOLVED parse (`gmoduleToModule (Source.srcModule src)`), so that
-- completeness is not resolver-vacuous (THE TRAP — see `_⊢R_` in
-- `Once.Adequacy.Compile`). Bridging the un-resolved anchor to the resolved
-- compilation is THIS module's three facts.
--
-- They are POSTULATES for now (the user-chosen scaffold stage): the resolver
-- IS structurally in the verified loop, the obligations are EXPLICIT and NAMED
-- (`make postulates` lists them), but not yet discharged. Each is the genuine
-- forcing a future arc must prove — a buggy resolver makes the corresponding
-- proof fail. Discharge requirements (per fact, below) center on an
-- IMPORT-AWARE declarative typing (`ModuleTypedWithImports`) so the source's
-- meaning-given-its-imports is stated without running the resolver, plus the
-- Plan-0.50 `m-named-resolved`/`realize-agrees` machinery for the trace fact.
--
-- For the IMPORT-FREE fragment (the resolver only canonicalizes own-module
-- `RVar → RResolved`, no inlined imports) all three reduce to that
-- canonicalization being type- and trace-preserving — fully provable; that is
-- the natural first discharge target.
------------------------------------------------------------------------

module Once.Adequacy.ResolverBridge where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Parser.Module.Core as P
open import Once.Parser.Module.Resolve using (ModuleMap; resolveImports)
open import Once.Grammar.ModuleConvert using (gmoduleToModule)
open import Once.Denotation.Behavior using (Source; Behavior)
open Source using (srcModule; srcImports)
open import Once.Adequacy.SourceTrace using (srcToModule; moduleToIR; ⟦_⟧IR)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC

postulate
  -- (1) FORWARD type-preservation — for COMPLETENESS. A declaratively
  --     well-typed UN-resolved module with a valid `main` resolves to a module
  --     that is ALSO well-typed with a valid `main`. This is the forcing on the
  --     completeness side: a resolver that maps a well-typed ref to an
  --     ill-typed `RResolved` (the stashed generator cut) makes this unprovable.
  --     Discharge: induction over the `⊢ᶜ` derivation, relating the un-resolved
  --     refs to their `canonExpr` images, against an import-aware declarative
  --     typing.
  resolver-preserves-typing :
    ∀ (mm : ModuleMap) (mU : P.Module) (mt : AS.ModuleTyped mU) →
    MC.HasValidMain-decl mU mt →
    Σ-syntax P.Module (λ mR →
      (resolveImports mm mU ≡ inj₂ mR)
      × Σ-syntax (AS.ModuleTyped mR) (λ mt' → MC.HasValidMain-decl mR mt'))

  -- (2) REVERSE type-recovery — for SOUNDNESS. If the front-end accepted (the
  --     RESOLVED module is well-typed) then the UN-resolved source was itself a
  --     typed program with a valid `main`, so the apex can produce a `tp` over
  --     the un-resolved module (keeping `_⊢R_` parse-based). For the import-free
  --     fragment this is an equivalence; with imports it needs the import-aware
  --     declarative typing to phrase "the source typed GIVEN its imports".
  resolver-reflects-typing :
    ∀ (src : Source) (mR : P.Module) →
    srcToModule src ≡ just mR → AS.ModuleTyped mR →
    Σ-syntax P.Module (λ mU →
      (gmoduleToModule (srcModule src) ≡ just mU)
      × Σ-syntax (AS.ModuleTyped mU) (λ mt → MC.HasValidMain-decl mU mt))

  -- (3) trace-preservation — for SOUNDNESS/TRACE. The resolved module's IR
  --     trace equals the un-resolved module's, so the compiled bytes' trace
  --     (against the resolved IR) equals the independent meaning (against the
  --     un-resolved main). This is resolver-preserves-SEMANTICS in trace form;
  --     discharge via the realize/`faithful` bridge over the canonicalized refs
  --     (Plan 0.50 `m-named-resolved` / `realize-agrees`).
  resolver-preserves-trace :
    ∀ (src : Source) (mR mU : P.Module) →
    srcToModule src ≡ just mR →
    gmoduleToModule (srcModule src) ≡ just mU →
    ∀ (n : ℕ) → ⟦ moduleToIR mR ⟧IR n ≡ ⟦ moduleToIR mU ⟧IR n
