-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.ResolverTrace — Plan 0.51 / 3b: resolver-preserves-trace.
--
-- `⟦ moduleToIR mR ⟧IR ≡ ⟦ moduleToIR mU ⟧IR`: the RESOLVED module's compiled IR
-- trace equals the UN-resolved module's. The IRs differ syntactically (`RVar x`
-- vs `RResolved (canonical [x])` take different `checkElab` clauses), so this is
-- NOT a `cong` — it routes through the DENOTATION:
--
--   ⟦moduleToIR mR⟧IR  =(sd-bridge mR)=  runMainˢ(mainRealized mR)
--                      =(resolved-main-agrees)=  runMainˢ(mainRealized mU)
--                      =(sym sd-bridge mU)=  ⟦moduleToIR mU⟧IR
--
-- TOP-DOWN NOTE (mirrors 3a): the resolver preserves typing, so a compilable mR
-- is typed (`moduleToIR-typed`/`-sound`); but `resolver-preserves-trace` cannot be
-- proven from the resolve-step ALONE without that typing. The typing of mU
-- (`mt`/`hvm`) and the compilability of mR (`moduleToIR mR ≡ just ir`) are
-- threaded from the call site (both available there).
--
-- `ir-trace≡runMain` is `Compile.sd-bridge`'s body, rebuilt here (its components
-- are importable; `sd-bridge` itself is private to `Compile`). `resolved-main-
-- agrees` is the genuine cross-resolution residual (the resolved/un-resolved
-- mains denote the same trace), to be discharged via `resolveExpr-faithful` +
-- `realize-invariant`.
------------------------------------------------------------------------

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.ResolverTrace (fmt : FloatFormat) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Sum using (inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit)
import Once.Parser.Module.Core as P
open import Once.Parser.Module.Resolve using (ModuleMap; resolveImports)
open import Once.Adequacy.SourceTrace using (moduleToIR; ⟦_⟧IR)
open import Once.Adequacy.AcceptSound using (ModuleTyped; moduleToIR-typed)
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MainExtract fmt as ME
import Once.Adequacy.MainRealizeAgrees fmt as MRA

------------------------------------------------------------------------
-- The IR-trace ↔ realized-main bridge (= Compile.sd-bridge's body).
------------------------------------------------------------------------

ir-trace≡runMain : ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : MC.HasValidMain-decl m mt) (n : ℕ)
  → ⟦ moduleToIR m ⟧IR fmt n ≡ ME.runMainˢ (proj₂ (MC.mainRealized m mt hvm)) n
ir-trace≡runMain m mt hvm n =
  trans (trans (cong (λ x → ⟦ x ⟧IR fmt n) (proj₂ (MC.moduleToIR-complete m mt hvm)))
               (proj₂ (proj₂ (ME.source-meaningᴰ m
                 (proj₁ (MC.moduleToIR-complete m mt hvm))
                 (proj₂ (MC.moduleToIR-complete m mt hvm)))) n))
        (MRA.main-realize-agrees-proof m mt hvm
          (proj₁ (MC.moduleToIR-complete m mt hvm))
          (proj₂ (MC.moduleToIR-complete m mt hvm)) n)

------------------------------------------------------------------------
-- The cross-resolution residual: the resolved and un-resolved mains denote the
-- SAME trace. DISCHARGE via `resolveExpr-faithful` (resolver preserves SD
-- denotation) + `realize-invariant`, lifted to `main`.
------------------------------------------------------------------------

postulate
  resolved-main-agrees :
    ∀ (mm : ModuleMap) (mU mR : P.Module)
      (mt-R : ModuleTyped mR) (hvm-R : MC.HasValidMain-decl mR mt-R)
      (mt-U : ModuleTyped mU) (hvm-U : MC.HasValidMain-decl mU mt-U)
    → resolveImports mm mU ≡ inj₂ mR
    → ∀ (n : ℕ) → ME.runMainˢ (proj₂ (MC.mainRealized mR mt-R hvm-R)) n
                ≡ ME.runMainˢ (proj₂ (MC.mainRealized mU mt-U hvm-U)) n

------------------------------------------------------------------------
-- The spine. Typing of mU + compilability of mR are threaded from the call site.
------------------------------------------------------------------------

resolver-preserves-trace :
  ∀ (mm : ModuleMap) (mU mR : P.Module)
  → resolveImports mm mU ≡ inj₂ mR
  → (mt-U : ModuleTyped mU) → MC.HasValidMain-decl mU mt-U
  → ∀ {ir-R : IR ⌊ Unit ⌋ ⌊ Unit ⌋} → moduleToIR mR ≡ just ir-R
  → ∀ (n : ℕ) → ⟦ moduleToIR mR ⟧IR fmt n ≡ ⟦ moduleToIR mU ⟧IR fmt n
resolver-preserves-trace mm mU mR res-eq mt-U hvm-U mi-R n =
  let mt-R  = moduleToIR-typed mR mi-R
      hvm-R = MC.moduleToIR-sound mR mt-R mi-R
  in trans (ir-trace≡runMain mR mt-R hvm-R n)
           (trans (resolved-main-agrees mm mU mR mt-R hvm-R mt-U hvm-U res-eq n)
                  (sym (ir-trace≡runMain mU mt-U hvm-U n)))
