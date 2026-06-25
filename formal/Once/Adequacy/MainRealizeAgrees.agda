-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.MainRealizeAgrees — discharge of `Compile.main-realize-agrees`
-- (Plan 0.49 row-3 / Plan 0.50 apex connection).
--
-- This is the COMPOSITION that connects `RealizeBridge.realize-agrees` to the
-- apex. `Compile.main-realize-agrees` was an INDEPENDENT postulate "morally true
-- by realize-agrees + resolveExpr-faithfulness" — a cut link that left
-- `realize-agrees` dangling off the apex. Here we actually compose it:
--
--   runMainˢ seR n  ≡  runMainˢ (realize deriv) n            -- the goal
--      └ ⟦seR⟧ =⟦resolveExpr se⟧ ─(A)─ ⟦se⟧ ─(realize-agrees)─ ⟦realize(check-sound ce)⟧ = ⟦realize deriv⟧
--
-- * gap (b) is CLOSED: `mainRealized`'s `deriv` IS `check-sound … ce`
--   (`AcceptSound`), = `realize-agrees`'s RHS exactly.
-- * The remaining gap is the COHERENCE hook `main-checkElab-coherence` below:
--   `source-meaningᴰ`'s `seR` and `mainRealized`'s `deriv` both factor through
--   ONE `checkElab` of `main`'s body. It bundles the strengthened extraction
--   (carry `ce`) and gap (A) `resolveExpr-faithfulness` (`⟦seR⟧≡⟦se⟧`). It is
--   the SINGLE remaining apex-path postulate this composition rests on (besides
--   `realize-agrees`'s own `{infer,check}-agreeV-todo`). To be discharged by
--   carrying the `checkElab` witness up through `Form`/`main-ir-form` and the
--   28-refl + `poly` `resolveExpr` faithfulness lemmas.
--
-- Wired into the apex: `Compile` imports this and defines
-- `main-realize-agrees = main-realize-agrees-proof` (the postulate is deleted).
------------------------------------------------------------------------

module Once.Adequacy.MainRealizeAgrees where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Data.List using (take)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.IR using (IR)
open import Once.Type using (Unit; Type)

import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Surface.Syntax as Srf using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)

open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate using (checkElab; InferElabResult; CheckElabResult; success)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Denotation.Realize using (realize)

open import Once.Adequacy.SourceTrace using (moduleToIR)
import Once.Adequacy.MainExtract as ME
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.ModuleComplete using (EffUU)
open import Once.Adequacy.AcceptSound as AS using (ModuleTyped)
import Once.Parser.Module.Core as P

-- THE proven agreement — the load-bearing composition uses this:
open import Once.Adequacy.RealizeBridge using (realize-agrees)

------------------------------------------------------------------------
-- The coherence hook (the one remaining apex-path postulate of this layer):
-- `main`'s source-meaning term `seR` and its realize term `realize deriv` both
-- factor through ONE `checkElab` of `main`'s body. Bundles the strengthened
-- main-extraction (carries `ce`) + gap (A) `resolveExpr-faithfulness`.
------------------------------------------------------------------------
postulate
  main-checkElab-coherence :
    ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : MC.HasValidMain-decl m mt)
      (ir : IR Unit Unit) (mi : moduleToIR m ≡ just ir)
    → Σ-syntax NamedCtx (λ cctx →
      Σ-syntax RawExpr (λ body →
      Σ-syntax (Usage (NamedCtx.size cctx)) (λ Ψ →
      Σ-syntax (Expr (NamedCtx.debruijn cctx) Ψ EffUU) (λ se →
      Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
      Σ-syntax (⟦ ⟦ NamedCtx.debruijn cctx ⟧ᶜ ⟧ᴰ) (λ dγ₀ →
      Σ-syntax (checkElab cctx body EffUU ≡ success Ψ se d f) (λ ce →
        ((n : ℕ) → SD.⟦ proj₁ (proj₂ (ME.source-meaningᴰ m ir mi)) ⟧ˢ tt n
                 ≡ SD.⟦ se ⟧ˢ dγ₀ n)
      × ((n : ℕ) → SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ tt n
                 ≡ SD.⟦ realize (check-sound cctx body EffUU ce) ⟧ˢ dγ₀ n)))))))))

------------------------------------------------------------------------
-- The composition. EXACT type of `Compile.main-realize-agrees`.
------------------------------------------------------------------------
main-realize-agrees-proof :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : MC.HasValidMain-decl m mt)
    (ir : IR Unit Unit) (mi : moduleToIR m ≡ just ir)
  → ∀ n → ME.runMainˢ (proj₁ (proj₂ (ME.source-meaningᴰ m ir mi))) n
          ≡ ME.runMainˢ (proj₂ (MC.mainRealized m mt hvm)) n
main-realize-agrees-proof m mt hvm ir mi n
  with main-checkElab-coherence m mt hvm ir mi
... | cctx , body , Ψ , se , d , f , dγ₀ , ce , seR≈se , rt≈deriv =
      cong (take n)
        (ME.bind-cong-trace
          (SD.⟦ proj₁ (proj₂ (ME.source-meaningᴰ m ir mi)) ⟧ˢ tt)
          (SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ tt)
          (λ clo → clo tt) n
          (trans (seR≈se n)
            (trans (realize-agrees cctx body EffUU ce dγ₀ n)
                   (sym (rt≈deriv n)))))
