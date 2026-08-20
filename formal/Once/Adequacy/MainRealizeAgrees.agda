-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Once.Float.Dyadic using (FloatFormat)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MainRealizeAgrees (fmt : FloatFormat) where

open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Data.List using (take; _∷_)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Type using (Unit; Type)

import Once.Denotation.SourceDenote as SD
open import Once.Denotation.TraceMonad using (T; _>>=T_; projTrace)
open import Once.Surface.Syntax as Srf using (Expr; Usage; ⟦_⟧ᶜ)
open import Once.Denotation.DenotTrace using (⟦_⟧ᴰ)

open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Elaborate
  using (checkElab; InferElabResult; CheckElabResult; success; PolyCtx; Imports;
         ctxWithImportsAndSelfAndPolys)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Denotation.Realize using (realize)

open import Once.Adequacy.SourceTrace using (moduleToIR)
import Once.Adequacy.MainExtract fmt as ME
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.ModuleComplete using (EffUU)
open import Once.Adequacy.AcceptSound as AS using (ModuleTyped)
import Once.Parser.Module.Core as P
import Once.Compile as C
import Once.Adequacy.MainForm fmt as MF

-- THE proven agreement — the load-bearing composition uses this:
open import Once.Adequacy.RealizeBridge fmt using (realize-agrees)

------------------------------------------------------------------------
-- The coherence hook, DECOMPOSED top-down into its three genuine constituents
-- (A/B/C). The hook itself is now PROVEN from them (below) — so A/B/C's TYPES
-- are pinned by that composition, not guessed.
--
-- (A) resolveExpr-faithfulness — the resolver preserves denotation. All
--     structural constructors (incl. effApp/cata/ana) are PROVEN by induction in
--     `Once.Adequacy.ResolveFaithful`; the only residuals are two NARROW
--     denotational postulates there (sigOp→closure rewrite, poly body-splice).
open import Once.Adequacy.ResolveFaithful fmt using (resolveExpr-faithful)

-- (B) realize denotational-invariance — ANY two `⊢ᶜ` derivations of the SAME
--     judgment realize to denotationally-equal terms. This is what lets the
--     compiled main (via `checkElab`/`check-sound`) agree with `realize` of
--     `mt`'s INDEPENDENT derivation, keeping the spec non-circular (no route-2).
--     The headline theorem (induction over derivations; reconciles the
--     `t-embed`-vs-specialized overlaps). Context-general.
-- Plan 0.55: factored into `Once.Adequacy.RealizeInvariant` (a base module) so
-- `MtIndep`/`mt-den-indep` can share it without an import cycle. UNCHANGED.
open import Once.Adequacy.RealizeInvariant fmt using (realize-invariant)

-- (C) the threading/extraction — `source-meaningᴰ`'s `seR` and `mainRealized`'s
--     `realize mtder` both factor through ONE `checkElab ce` of `main`'s body
--     (`seR` = `resolveExpr … se`, `mtder` is `mt`'s main derivation). PLUMBING:
--     to be discharged by strengthening `Form`/`main-ir-form` to carry `ce` +
--     the resolver args + the two endpoint identifications.
-- Plan 0.55: `main-extract` is now a DEFINITION (postulate deleted). The bundle-
-- rebased `main-ir-form` (`MainForm`) hands us the selected main node together
-- with the `FunBundle` `b`/`bme` whose `bundle-realize b bme` IS that node's
-- `realize (check-sound … ce)`. eq1 = `cong ⟦_⟧ˢ` of the Payload's `seR ≡
-- resolveExpr … se`; eq2 = `mt-den-indep` ∘ `realize-agree` ∘ the carried
-- `bundle-realize` witness. Casing `extractFunctions` (reduces `mainRealized` to
-- `mainRealized-go mt me`) and `compileAllFuns-go` (reduces `main-ir-form` to the
-- concrete bundle) makes `mt` and `b` share `polys`/`sigEffs`/`funs`.
main-extract :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : MC.HasValidMain-decl m mt)
    (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir)
  → Σ-syntax NamedCtx (λ cctx →
    Σ-syntax RawExpr (λ body →
    Σ-syntax (Usage (NamedCtx.size cctx)) (λ Ψ →
    Σ-syntax (Expr (NamedCtx.debruijn cctx) Ψ EffUU) (λ se →
    Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    Σ-syntax (⟦ ⟦ NamedCtx.debruijn cctx ⟧ᶜ ⟧ᴰ) (λ dγ₀ →
    Σ-syntax (cctx ⊢ᶜ body ∶ EffUU ⨾ Ψ) (λ mtder →
    Σ-syntax (checkElab cctx body EffUU ≡ success Ψ se d f) (λ ce →
    Σ-syntax PolyCtx (λ polys →
    Σ-syntax Imports (λ imps → Σ-syntax Imports (λ userFns → Σ-syntax ℕ (λ fresh →
      ((n : ℕ) → SD.⟦ proj₁ (proj₂ (ME.source-meaningᴰ m ir mi)) ⟧ˢ fmt tt n
               ≡ SD.⟦ resolveExpr polys imps userFns fresh se ⟧ˢ fmt dγ₀ n)
    × ((n : ℕ) → SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ fmt tt n
               ≡ SD.⟦ realize mtder ⟧ˢ fmt dγ₀ n))))))))))))))
main-extract m mt hvm ir mi =
  let (funs , polys , ef-eq , b , bme , mctx , mbody , mΨ , mse , md , mf , mce , ir≡ , rw) = MF.main-node-of m ir mi
  in    ctxWithImportsAndSelfAndPolys mctx (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) "main" EffUU
      , mbody , mΨ , mse , md , mf , tt
      , check-sound (ctxWithImportsAndSelfAndPolys mctx (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) "main" EffUU) mbody EffUU mce
      , mce , C.buildPolyCtx polys , (("main" , EffUU) ∷ mctx) , (("main" , EffUU) ∷ mctx) , 0
      , (λ n → refl)
      , (λ n → trans (MF.mainRealized-bundle m mt hvm b bme ef-eq n)
                     (cong (λ z → SD.⟦ proj₂ z ⟧ˢ fmt tt n) rw))

------------------------------------------------------------------------
-- The coherence hook, now PROVEN from A/B/C (the postulate is gone).
-- seR ≈ se  : ⟦seR⟧ =(C seR-syn)= ⟦resolveExpr se⟧ =(A)= ⟦se⟧
-- rt  ≈ deriv: ⟦rt⟧  =(C rt-syn)=  ⟦realize mtder⟧  =(B)= ⟦realize(check-sound ce)⟧
------------------------------------------------------------------------
main-checkElab-coherence :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : MC.HasValidMain-decl m mt)
    (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir)
  → Σ-syntax NamedCtx (λ cctx →
    Σ-syntax RawExpr (λ body →
    Σ-syntax (Usage (NamedCtx.size cctx)) (λ Ψ →
    Σ-syntax (Expr (NamedCtx.debruijn cctx) Ψ EffUU) (λ se →
    Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
    Σ-syntax (⟦ ⟦ NamedCtx.debruijn cctx ⟧ᶜ ⟧ᴰ) (λ dγ₀ →
    Σ-syntax (checkElab cctx body EffUU ≡ success Ψ se d f) (λ ce →
      ((n : ℕ) → SD.⟦ proj₁ (proj₂ (ME.source-meaningᴰ m ir mi)) ⟧ˢ fmt tt n
               ≡ SD.⟦ se ⟧ˢ fmt dγ₀ n)
    × ((n : ℕ) → SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ fmt tt n
               ≡ SD.⟦ realize (check-sound cctx body EffUU ce) ⟧ˢ fmt dγ₀ n)))))))))
main-checkElab-coherence m mt hvm ir mi
  with main-extract m mt hvm ir mi
... | cctx , body , Ψ , se , d , f , dγ₀ , mtder , ce , polys , imps , userFns , fresh , seR-syn , rt-syn =
      cctx , body , Ψ , se , d , f , dγ₀ , ce ,
      (λ n → trans (seR-syn n) (resolveExpr-faithful polys imps userFns fresh se dγ₀ n)) ,
      (λ n → trans (rt-syn n) (realize-invariant mtder (check-sound cctx body EffUU ce) dγ₀ n))

------------------------------------------------------------------------
-- The composition. EXACT type of `Compile.main-realize-agrees`.
------------------------------------------------------------------------
main-realize-agrees-proof :
  ∀ (m : P.Module) (mt : ModuleTyped m) (hvm : MC.HasValidMain-decl m mt)
    (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (mi : moduleToIR m ≡ just ir)
  → ∀ n → ME.runMainˢ (proj₁ (proj₂ (ME.source-meaningᴰ m ir mi))) n
          ≡ ME.runMainˢ (proj₂ (MC.mainRealized m mt hvm)) n
main-realize-agrees-proof m mt hvm ir mi n
  with main-checkElab-coherence m mt hvm ir mi
... | cctx , body , Ψ , se , d , f , dγ₀ , ce , seR≈se , rt≈deriv =
      cong (take n)
        (ME.bind-cong-trace
          (SD.⟦ proj₁ (proj₂ (ME.source-meaningᴰ m ir mi)) ⟧ˢ fmt tt)
          (SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ fmt tt)
          (λ clo → clo tt) n
          (trans (seR≈se n)
            (trans (realize-agrees cctx body EffUU ce dγ₀ n)
                   (sym (rt≈deriv n)))))
