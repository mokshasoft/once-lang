-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.Adequacy.MainForm — Plan 0.55: the BUNDLE-REBASED `main-ir-form`.
--
-- Same statement as `MainIRForm.main-ir-form` (`moduleToIR m ≡ just ir → Form
-- ir`), but the `Form`/`Payload` are derived FROM the per-function `FunBundle`
-- (`Once.Adequacy.FunBundle`) via the combined `bundle-main-node` extractor.
-- Because the Payload's `(ctx,body,se,ce)` ARE the bundle's selected main node,
-- the eq2 half of `main-extract` composes the already-proven `mt-den-indep` ∘
-- `realize-agree` ∘ (the Payload's carried `bundle-realize` witness) with NO
-- separate node-alignment lemma. The Form's outer shape is UNCHANGED, so
-- `MainExtract.source-meaningᴰ-aux` (which `_`-ignores the Payload) is untouched.
--
-- Lives ABOVE `FunBundle` (which imports `MainIRForm`), so no import cycle.
------------------------------------------------------------------------

module Once.Adequacy.MainForm where

open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx; NamedCtx)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndSelfAndPolys; resolveExpr; PolyCtx; success)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Denotation.Realize using (realize)
import Once.Compile as C
open import Once.Parser using (FunInfo)
open FunInfo

open import Once.Adequacy.SourceTrace using (findMain; moduleToIR; moduleToIR-aux)
open import Once.Adequacy.FunBundle as FB
  using (FunBundle; caf-go-bundle; bundle→compiled≡compiled; find-agree;
         bundle-find; bundle-find-exists; bundle-realize; BMainExists; bundle-main-node; MNodeAt)

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

------------------------------------------------------------------------
-- The bundle-derived Payload. Beyond the resolved surface term `seR` and the
-- checkElab witness `ce`, it carries the `FunBundle` `b` + its `BMainExists`
-- witness `bme`, plus the equation tying THIS `(ctx,body,ce)` to the bundle's
-- `bundle-realize b bme` result — so `main-extract` never needs to re-derive
-- the node.
------------------------------------------------------------------------

Payload : (Ψ : Usage 0) → Expr ∅ Ψ EffUU → Set
Payload Ψ seR =
  Σ-syntax C.FunCtx (λ ctx → Σ-syntax PolyCtx (λ polys → Σ-syntax SigEffectCtx (λ sigEffs →
  Σ-syntax RawExpr (λ body →
  Σ-syntax (Expr ∅ Ψ EffUU) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
  Σ-syntax (checkElab (ctxWithImportsAndSelfAndPolys ctx polys sigEffs "main" EffUU) body EffUU
             ≡ success Ψ se d f) (λ ce →
  Σ-syntax (List FunInfo) (λ funs →
  Σ-syntax (FunBundle polys sigEffs funs C.emptyFunCtx) (λ b →
  Σ-syntax (BMainExists b) (λ bme →
    (seR ≡ resolveExpr polys (("main" , EffUU) ∷ ctx) (("main" , EffUU) ∷ ctx) 0 se)
  × (bundle-realize b bme
       ≡ (Ψ , realize (check-sound (ctxWithImportsAndSelfAndPolys ctx polys sigEffs "main" EffUU)
                         body EffUU ce))))))))))))))

Form : IR Unit Unit → Set
Form ir = Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
            (ir ≡ C.wrapMainAsEntry (elaborate C.Heap seR)) × Payload Ψ seR))

------------------------------------------------------------------------
-- The core: from a `compileAllFuns-go` success + `findMain … ≡ just ir`,
-- build the bundle and read its main node.
------------------------------------------------------------------------

build-form : ∀ (polys : PolyCtx) (sigEffs : SigEffectCtx) (funs : List FunInfo)
  (compiled : List C.CompiledFun) (ir : IR Unit Unit) →
  C.compileAllFuns-go C.Heap false polys sigEffs funs C.emptyFunCtx ≡ inj₂ compiled →
  findMain compiled ≡ just ir → Form ir
build-form polys sigEffs funs compiled ir caf-eq mi =
  let b   = caf-go-bundle polys sigEffs funs C.emptyFunCtx caf-eq
      bf≡ : bundle-find b ≡ just ir
      bf≡ = trans (sym (find-agree b))
              (trans (cong findMain (bundle→compiled≡compiled polys sigEffs funs C.emptyFunCtx compiled caf-eq)) mi)
      bme = bundle-find-exists b bf≡
  in node b bf≡ bme (bundle-main-node b bme)
  where
    node : ∀ (b : FunBundle polys sigEffs funs C.emptyFunCtx)
             (bf≡ : bundle-find b ≡ just ir) (bme : BMainExists b) →
             FB.MNodeAt polys sigEffs (bundle-find b) (bundle-realize b bme) → Form ir
    node b bf≡ bme (mctx , mbody , mΨ , mse , md , mf , mce , find-wit , realize-wit) =
      mΨ , resolveExpr polys (("main" , EffUU) ∷ mctx) (("main" , EffUU) ∷ mctx) 0 mse
         , just-injective (trans (sym bf≡) find-wit)
         , mctx , polys , sigEffs , mbody , mse , md , mf , mce , funs , b , bme , refl , realize-wit

------------------------------------------------------------------------
-- Unfold `moduleToIR` to `compileAllFuns-go` (mirrors MainIRForm.mif-ef/mif-caf,
-- externally reducible: a caller casing the same scrutinees drives it in lockstep).
------------------------------------------------------------------------

main-ir-form : ∀ (m : C.Module) (ir : IR Unit Unit) →
  moduleToIR m ≡ just ir → Form ir

mif-caf : ∀ (m : C.Module) (ir : IR Unit Unit) (funs : List FunInfo) (polys : List C.PolyFunInfo)
  (cv : String ⊎ List C.CompiledFun) →
  C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx ≡ cv →
  moduleToIR-aux cv ≡ just ir → Form ir
mif-caf m ir funs polys (inj₁ err) caf-eq mi = case mi of λ ()
mif-caf m ir funs polys (inj₂ compiled) caf-eq mi =
  build-form (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m))
    funs compiled ir caf-eq mi

mif-ef : ∀ (m : C.Module) (ir : IR Unit Unit)
  (efv : String ⊎ (List FunInfo × List C.PolyFunInfo)) →
  moduleToIR-aux (C.compileResolvedModule-aux C.Heap false m efv) ≡ just ir → Form ir
mif-ef m ir (inj₁ err) mi = case mi of λ ()
mif-ef m ir (inj₂ (funs , polys)) mi =
  mif-caf m ir funs polys
    (C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx)
    refl mi

main-ir-form m ir mi = mif-ef m ir (C.extractFunctions (C.extractAliases m) m) mi
