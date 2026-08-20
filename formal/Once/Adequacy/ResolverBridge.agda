-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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
--
-- DISCHARGE ANALYSIS (2026-06-27, POC done — not blocked by Plan 0.50):
--   `bare x ≡ canonical [x]` and `showCanonical (canonical [x]) ≡ x` are
--   DEFINITIONAL (Once.CanonicalName), and `t-var-import`/`t-var-resolved`
--   (and `m-named`/`m-named-resolved`, Judgment.agda) carry the SAME
--   `lookupImport` premise (`x` vs `showCanonical cn = x`). So canonExpr's
--   `RVar x → RResolved (canonical [x])` maps cleanly with NO dependency on the
--   open `named-morph-strong*` postulates (those are the import/full-path case).
--   ⇒ the import-free discharge is available now; 0.51 is NOT gated on 0.50.
--
--   Proof shape (the integration cost):
--     (1)+(2) TYPING — `ModuleTyped` = the inductive `⊢ᶜ` judgment (AcceptSound:
--       "ONLY the judgment, no elaborator"). Discharge = a mutual induction over
--       the 4-judgment ⊢ᵢ/⊢ᵍ/⊢ᵐ/⊢ᶜ block (~48 rules; most CONGRUENCE). The var
--       rules map `t-var-import → t-var-resolved` / `m-named → m-named-resolved`
--       via the showCanonical identity; binders (t-lam/t-let/t-case) need a
--       threaded invariant `x ∈ canonExpr-bound ⟺ lookupLocal ctx x ≢ nothing`.
--       Plus the import-free split: case on `NoImports mU`, proven branch +
--       residual `*-imports` postulate (keeps the apex interface general).
--     (3) TRACE — routes through `moduleToIR`→`compileResolvedModule` (the
--       3445-line type-directed elaborator). Needs canonExpr-invariance of
--       compilation (heavier), OR leverage of existing compile-correctness.
--   Estimate: ~400-700 lines across typing+trace. A dedicated arc, not a grind.
------------------------------------------------------------------------

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.ResolverBridge (fmt : FloatFormat) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Once.Parser.Module.Core as P
open import Once.Parser.Module.Resolve using (ModuleMap; resolveImports)
open import Once.Adequacy.SourceTrace using (moduleToIR; ⟦_⟧IR)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.CanonModule as CMod
import Once.Adequacy.CanonReflectModule as CRMod
import Once.Adequacy.ResolverTrace fmt as RT
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)

-- (1) FORWARD type-preservation — for COMPLETENESS. A declaratively well-typed
--     UN-resolved module with a valid `main` resolves to a module that is ALSO
--     well-typed with a valid `main`. A resolver that maps a well-typed ref to an
--     ill-typed `RResolved` (the stashed generator cut) makes this unprovable.
--     Plan 0.51 Step 4: DISCHARGED for the import-free fragment by the top-down
--     `CMod.canon-preserves-typing`, which lifts the `⊢ᶜ` derivation per-function
--     via `Once.Adequacy.CanonPreserveMutual.canon-pres-ᶜ` (the import case routes
--     to a residual `*-imports` postulate, keeping the apex interface general).
resolver-preserves-typing :
  ∀ (mm : ModuleMap) (mU : P.Module) (mt : AS.ModuleTyped mU) →
  MC.HasValidMain-decl mU mt →
  Σ-syntax P.Module (λ mR →
    (resolveImports mm mU ≡ inj₂ mR)
    × Σ-syntax (AS.ModuleTyped mR) (λ mt' → MC.HasValidMain-decl mR mt'))
resolver-preserves-typing = CMod.canon-preserves-typing

-- (2) REVERSE type-recovery — for SOUNDNESS. If the front-end accepted (the
--     RESOLVED module `mR` is well-typed WITH a valid main) and `mU` resolves to
--     `mR`, then `mU` was itself a typed program with a valid `main`, so the apex
--     can produce a `tp` over the UN-resolved module (keeping `_⊢R_`
--     front-end-based, not resolver-based). The `HasValidMain mR` input is
--     threaded from the call site (derived via `MC.moduleToIR-sound`): it is NOT
--     derivable from `ModuleTyped mR` alone, so the earlier `ModuleTyped mR`-only
--     postulate shape was unprovable. The import-free fragment is discharged in
--     `CanonReflectModule`; the import case stays a residual `*-imports`
--     postulate there (mirroring `preserves-typing`).
resolver-reflects-typing :
  ∀ (mm : ModuleMap) (mU mR : P.Module) →
  resolveImports mm mU ≡ inj₂ mR → (mt : AS.ModuleTyped mR) → MC.HasValidMain-decl mR mt →
  Σ-syntax (AS.ModuleTyped mU) (λ mt' → MC.HasValidMain-decl mU mt')
resolver-reflects-typing = CRMod.resolver-reflects-typing

-- (3) trace-preservation — for SOUNDNESS/TRACE. The resolved module's IR trace
--     equals the un-resolved module's, so the compiled bytes' trace (against the
--     resolved IR) equals the independent meaning (against the un-resolved main).
--     Routes through the DENOTATION (sd-bridge for both + a cross-resolution
--     residual); see `Once.Adequacy.ResolverTrace`. The typing of mU + the
--     compilability of mR are threaded from the call site (both available there).
resolver-preserves-trace :
  ∀ (mm : ModuleMap) (mU mR : P.Module) →
  resolveImports mm mU ≡ inj₂ mR →
  (mt-U : AS.ModuleTyped mU) → MC.HasValidMain-decl mU mt-U →
  ∀ {ir-R : IR ⌊ Unit ⌋ ⌊ Unit ⌋} → moduleToIR mR ≡ just ir-R →
  ∀ (n : ℕ) → ⟦ moduleToIR mR ⟧IR fmt n ≡ ⟦ moduleToIR mU ⟧IR fmt n
resolver-preserves-trace = RT.resolver-preserves-trace
