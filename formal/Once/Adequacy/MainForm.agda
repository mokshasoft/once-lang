-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

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

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
module Once.Adequacy.MainForm (fmt : TargetNum) where


open import Once.Spec.Module using (AllFunsTyped; HasValidMain-decl; MainExists; ModuleMainEffUU-ef; ModuleMainExists-ef; ModuleTyped; ModuleTyped-ef)
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import Once.Denotation.SourceDenote as SD
open import Once.Type using (Type; Unit; _⇒[_]_; mk-kind; Many; eff)
open import Once.IR using (IR)
open import Once.IRTy using (⌊_⌋)
open import Once.Surface.Syntax using (Expr; ∅; Usage)
open import Once.Surface.Elaborate using (elaborate; elaborateFull)
open import Once.TypeCheck.Raw using (RawExpr)
open import Once.TypeCheck.Classify using (SigEffectCtx; NamedCtx)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndSelfAndPolys; PolyCtx; success)
open import Once.TypeCheck.ElaborateProofs using (resolveExpr)
open import Once.TypeCheck.Judgment using (_⊢ᶜ_∶_⨾_)
open import Once.TypeCheck.Soundness using (check-sound)
open import Once.Denotation.Phase using (env0)
open import Once.Denotation.Realize using (realize)
import Once.Compile as C
open import Once.Parser using (FunInfo)
open FunInfo

open import Once.Adequacy.SourceTrace using (findMain; moduleToIR; moduleToIR-aux)
open import Once.Adequacy.FunBundle as FB
  using (FunBundle; caf-go-bundle; bundle→compiled≡compiled; find-agree;
         bundle-find; bundle-find-exists; bundle-realize; BMainExists; bundle-main-node; MNodeAt;
         bundle→typed; bme→me; realize-agree)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
open import Once.Adequacy.MtIndep fmt using (mt-den-indep)

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

Form : IR ⌊ Unit ⌋ ⌊ Unit ⌋ → Set
Form ir = Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
            (ir ≡ C.wrapMainAsEntry (elaborateFull C.Heap seR)) × Payload Ψ seR))

------------------------------------------------------------------------
-- `MainNode`: the SHARED main-node extractor (independent of any typing
-- derivation `mt`). Both `main-ir-form` (its Payload) and `main-extract` (eq2)
-- PROJECT from the SAME `main-node-of m ir mi`, so their nodes coincide
-- DEFINITIONALLY — making `main-extract`'s eq1 a `refl`. It also carries the
-- `extractFunctions` witness `ef-eq`, so `main-extract` can transport the
-- typing derivation `mt` onto THIS node's bundle (`mainRealized-bundle`).
------------------------------------------------------------------------

MainNode : (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Set
MainNode m ir =
  Σ-syntax (List FunInfo) (λ funs → Σ-syntax (List C.PolyFunInfo) (λ polys →
  Σ-syntax (C.extractFunctions (C.extractAliases m) m ≡ inj₂ (funs , polys)) (λ ef-eq →
  Σ-syntax (FunBundle (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx) (λ b →
  Σ-syntax (BMainExists b) (λ bme →
  Σ-syntax C.FunCtx (λ mctx → Σ-syntax RawExpr (λ mbody →
  Σ-syntax (Usage 0) (λ mΨ → Σ-syntax (Expr ∅ mΨ EffUU) (λ mse → Σ-syntax ℕ (λ md → Σ-syntax ℕ (λ mf →
  Σ-syntax (checkElab (ctxWithImportsAndSelfAndPolys mctx (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) "main" EffUU)
             mbody EffUU ≡ success mΨ mse md mf) (λ mce →
    (ir ≡ C.wrapMainAsEntry (elaborateFull C.Heap
            (resolveExpr (C.buildPolyCtx polys) (("main" , EffUU) ∷ mctx) (("main" , EffUU) ∷ mctx) 0 mse)))
  × (bundle-realize b bme
       ≡ (mΨ , realize (check-sound (ctxWithImportsAndSelfAndPolys mctx (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) "main" EffUU)
                          mbody EffUU mce)))))))))))))))

build-node : ∀ (m : C.Module) (funs : List FunInfo) (polys : List C.PolyFunInfo)
  (compiled : List C.CompiledFun) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
  (caf-eq : C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx ≡ inj₂ compiled)
  (mi : findMain compiled ≡ just ir)
  (ef-eq : C.extractFunctions (C.extractAliases m) m ≡ inj₂ (funs , polys)) →
  MainNode m ir
build-node m funs polys compiled ir caf-eq mi ef-eq =
  let pc  = C.buildPolyCtx polys
      se' = C.collectSigEffects (C.Module.decls m)
      b   = caf-go-bundle pc se' funs C.emptyFunCtx caf-eq
      bf≡ : bundle-find b ≡ just ir
      bf≡ = trans (sym (find-agree b))
              (trans (cong findMain (bundle→compiled≡compiled pc se' funs C.emptyFunCtx compiled caf-eq)) mi)
      bme = bundle-find-exists b bf≡
  in node b bf≡ bme (bundle-main-node b bme)
  where
    node : ∀ (b : FunBundle (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx)
             (bf≡ : bundle-find b ≡ just ir) (bme : BMainExists b) →
             FB.MNodeAt (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) (bundle-find b) (bundle-realize b bme) →
             MainNode m ir
    node b bf≡ bme (mctx , mbody , mΨ , mse , md , mf , mce , find-wit , realize-wit) =
      funs , polys , ef-eq , b , bme , mctx , mbody , mΨ , mse , md , mf , mce
        , just-injective (trans (sym bf≡) find-wit) , realize-wit

------------------------------------------------------------------------
-- Unfold `moduleToIR` to `compileAllFuns-go` via explicit-scrutinee helpers
-- (so the `extractFunctions`/`compileAllFuns-go` casing carries the equations
-- and never leaves a bare `refl` blocking a caller's abstraction).
------------------------------------------------------------------------

main-node-of : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → MainNode m ir

mnf-caf : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (funs : List FunInfo) (polys : List C.PolyFunInfo)
  (cv : String ⊎ List C.CompiledFun) →
  C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx ≡ cv →
  moduleToIR-aux cv ≡ just ir →
  C.extractFunctions (C.extractAliases m) m ≡ inj₂ (funs , polys) → MainNode m ir
mnf-caf m ir funs polys (inj₁ err) caf-eq mi ef-eq = case mi of λ ()
mnf-caf m ir funs polys (inj₂ compiled) caf-eq mi ef-eq =
  build-node m funs polys compiled ir caf-eq mi ef-eq

mnf-ef : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
  (efv : String ⊎ (List FunInfo × List C.PolyFunInfo)) →
  C.extractFunctions (C.extractAliases m) m ≡ efv →
  moduleToIR-aux (C.compileResolvedModule-aux C.Heap false m efv) ≡ just ir → MainNode m ir
mnf-ef m ir (inj₁ err) ef-eq mi = case mi of λ ()
mnf-ef m ir (inj₂ (funs , polys)) ef-eq mi =
  mnf-caf m ir funs polys
    (C.compileAllFuns-go C.Heap false (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx)
    refl mi ef-eq

main-node-of m ir mi = mnf-ef m ir (C.extractFunctions (C.extractAliases m) m) refl mi

------------------------------------------------------------------------
-- `main-ir-form` — project `main-node-of` into a `Form` (Payload = the node).
------------------------------------------------------------------------

main-ir-form : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → Form ir
main-ir-form m ir mi = form (main-node-of m ir mi)
  where
    form : MainNode m ir → Form ir
    form (funs , polys , ef-eq , b , bme , mctx , mbody , mΨ , mse , md , mf , mce , ir≡ , rw) =
      mΨ , resolveExpr (C.buildPolyCtx polys) (("main" , EffUU) ∷ mctx) (("main" , EffUU) ∷ mctx) 0 mse
         , ir≡
         , mctx , C.buildPolyCtx polys , C.collectSigEffects (C.Module.decls m) , mbody , mse , md , mf , mce
         , funs , b , bme , refl , rw

------------------------------------------------------------------------
-- `mainRealized-bundle` — the eq2 core: transport `mt` (via `ef-eq`) onto the
-- node's bundle and compose `mt-den-indep` ∘ `realize-agree`.
------------------------------------------------------------------------

subst-app : ∀ {A : Set} {P : A → Set} {Q : Set} (f : (a : A) → P a → Q)
  {a a' : A} (eq : a ≡ a') (x : P a) → f a x ≡ f a' (subst P eq x)
subst-app f refl x = refl

mainRealized-bundle : ∀ (m : C.Module) (mt : ModuleTyped m) (hvm : HasValidMain-decl m mt)
  {funs : List FunInfo} {polys : List C.PolyFunInfo}
  (b : FunBundle (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx)
  (bme : BMainExists b)
  (ef-eq : C.extractFunctions (C.extractAliases m) m ≡ inj₂ (funs , polys)) →
  ∀ (n : ℕ) → SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ fmt (env0 {proj₁ (MC.mainRealized m mt hvm)} tt) n
            ≡ SD.⟦ proj₂ (bundle-realize b bme) ⟧ˢ fmt (env0 {proj₁ (bundle-realize b bme)} tt) n
mainRealized-bundle m mt hvm {funs} {polys} b bme ef-eq n =
  trans (cong (λ z → SD.⟦ proj₂ z ⟧ˢ fmt (env0 {proj₁ z} tt) n) (subst-app F ef-eq x))
    (trans (mt-den-indep mt' (bundle→typed b) me' (bme→me b bme) tt n)
           (cong (λ z → SD.⟦ proj₂ z ⟧ˢ fmt (env0 {proj₁ z} tt) n) (realize-agree b bme)))
  where
    Motive : (ef : String ⊎ (List FunInfo × List C.PolyFunInfo)) → Set
    Motive ef = Σ-syntax (ModuleTyped-ef m ef) (λ mtx →
                  ModuleMainEffUU-ef m ef mtx × ModuleMainExists-ef m ef mtx)
    F : (ef : String ⊎ (List FunInfo × List C.PolyFunInfo)) → Motive ef →
        Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
    F ef (mtx , amux , mex) = MC.mainRealized-ef m ef mtx amux mex
    x : Motive (C.extractFunctions (C.extractAliases m) m)
    x = mt , proj₁ hvm , proj₂ hvm
    x' : Motive (inj₂ (funs , polys))
    x' = subst Motive ef-eq x
    mt' : AllFunsTyped (C.buildPolyCtx polys) (C.collectSigEffects (C.Module.decls m)) funs C.emptyFunCtx
    mt' = proj₁ x'
    me' : MainExists mt'
    me' = proj₂ (proj₂ x')
