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


open import Once.Spec.Module using (ModTele; emptyScope; MainIn; HasValidMain; HasValidMain-ef; ModuleTyped; ModuleTyped-ef)
open import Data.Bool using (Bool; false; true)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
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
open import Once.TypeCheck.Classify using (NamedCtx)
open import Once.TypeCheck.Elaborate
  using (checkElab; ctxWithImportsAndPolys; PolyCtx; success)
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
  using (FunBundle; ce-bundle; bundle→compiled≡compiled; find-agree;
         bundle-find; bundle-find-exists; bundle-realize; BMainExists; bundle-main-node; MNodeAt;
         bundle→typed; bme→me; realize-agree)
import Once.Adequacy.AcceptSound as AS
import Once.Adequacy.ModuleComplete as MC
import Once.Adequacy.MtIndep as MI

EffUU : Type
EffUU = Unit ⇒[ mk-kind Many eff ] Unit

------------------------------------------------------------------------
-- The bundle-derived Payload. Beyond the resolved surface term `seR` and the
-- checkElab witness `ce`, it carries the `FunBundle` `b` + its `BMainExists`
-- witness `bme`, plus the equation tying THIS `(ctx,body,ce)` to the bundle's
-- `bundle-realize b bme` result — so `main-extract` never needs to re-derive
-- the node.
------------------------------------------------------------------------

-- D241 (plan 0.103 6c′): `main`'s compiled form, over the module telescope.
-- The payload's scope `msc` is `main`'s compile scope — its imports, the
-- telescope before it, and each entry's declaration imports.
Payload : (Ψ : Usage 0) → Expr ∅ Ψ EffUU → Set
Payload Ψ seR =
  Σ-syntax C.CScope (λ msc →
  Σ-syntax RawExpr (λ body →
  Σ-syntax (Expr ∅ Ψ EffUU) (λ se →
  Σ-syntax ℕ (λ d → Σ-syntax ℕ (λ f →
  Σ-syntax (checkElab (FB.ctxC msc) body EffUU ≡ success Ψ se d f) (λ ce →
  Σ-syntax (List C.Entry) (λ es →
  Σ-syntax (FunBundle C.emptyCScope es) (λ b →
  Σ-syntax (BMainExists b) (λ bme →
    (seR ≡ resolveExpr (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc) 0 se)
  × (bundle-realize b bme ≡ (Ψ , realize (check-sound (FB.ctxC msc) body EffUU ce))))))))))))

Form : IR ⌊ Unit ⌋ ⌊ Unit ⌋ → Set
Form ir = Σ-syntax (Usage 0) (λ Ψ → Σ-syntax (Expr ∅ Ψ EffUU) (λ seR →
            (ir ≡ C.wrapMainAsEntry (elaborateFull C.Heap seR)) × Payload Ψ seR))

MainNode : (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → Set
MainNode m ir =
  Σ-syntax (List C.Entry) (λ es →
  Σ-syntax (C.extractFunctions (C.extractAliases m) m ≡ inj₂ es) (λ ef-eq →
  Σ-syntax (FunBundle C.emptyCScope es) (λ b →
  Σ-syntax (BMainExists b) (λ bme →
  Σ-syntax C.CScope (λ msc → Σ-syntax RawExpr (λ mbody →
  Σ-syntax (Usage 0) (λ mΨ → Σ-syntax (Expr ∅ mΨ EffUU) (λ mse → Σ-syntax ℕ (λ md → Σ-syntax ℕ (λ mf →
  Σ-syntax (checkElab (FB.ctxC msc) mbody EffUU ≡ success mΨ mse md mf) (λ mce →
    (ir ≡ C.wrapMainAsEntry (elaborateFull C.Heap
            (resolveExpr (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc) 0 mse)))
  × (bundle-realize b bme ≡ (mΨ , realize (check-sound (FB.ctxC msc) mbody EffUU mce))))))))))))))

build-node : ∀ (m : C.Module) (es : List C.Entry) (compiled : List C.CompiledFun) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋)
  (ce-eq : C.compileEntries C.Heap false C.emptyCScope es ≡ inj₂ compiled)
  (mi : findMain compiled ≡ just ir)
  (ef-eq : C.extractFunctions (C.extractAliases m) m ≡ inj₂ es) →
  MainNode m ir
build-node m es compiled ir ce-eq mi ef-eq =
  let b   = ce-bundle C.emptyCScope es ce-eq
      bf≡ : bundle-find b ≡ just ir
      bf≡ = trans (sym (find-agree b))
              (trans (cong findMain (bundle→compiled≡compiled C.emptyCScope es compiled ce-eq)) mi)
      bme = bundle-find-exists b bf≡
  in node b bf≡ bme (bundle-main-node b bme)
  where
    node : ∀ (b : FunBundle C.emptyCScope es) (bf≡ : bundle-find b ≡ just ir) (bme : BMainExists b) →
             FB.MNodeAt (bundle-find b) (bundle-realize b bme) → MainNode m ir
    node b bf≡ bme (msc , mbody , mΨ , mse , md , mf , mce , find-wit , realize-wit) =
      es , ef-eq , b , bme , msc , mbody , mΨ , mse , md , mf , mce
        , just-injective (trans (sym bf≡) find-wit) , realize-wit

main-node-of : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → MainNode m ir
mnf-ce : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (es : List C.Entry) (cv : String ⊎ List C.CompiledFun) →
  C.compileEntries C.Heap false C.emptyCScope es ≡ cv → moduleToIR-aux cv ≡ just ir →
  C.extractFunctions (C.extractAliases m) m ≡ inj₂ es → MainNode m ir
mnf-ce m ir es (inj₁ err) ce-eq mi ef-eq = case mi of λ ()
mnf-ce m ir es (inj₂ compiled) ce-eq mi ef-eq = build-node m es compiled ir ce-eq mi ef-eq
mnf-ef : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) (efv : String ⊎ List C.Entry) →
  C.extractFunctions (C.extractAliases m) m ≡ efv →
  moduleToIR-aux (C.compileResolvedModule-aux C.Heap false m efv) ≡ just ir → MainNode m ir
mnf-ef m ir (inj₁ err) ef-eq mi = case mi of λ ()
mnf-ef m ir (inj₂ es) ef-eq mi = mnf-ce m ir es (C.compileEntries C.Heap false C.emptyCScope es) refl mi ef-eq
main-node-of m ir mi = mnf-ef m ir (C.extractFunctions (C.extractAliases m) m) refl mi

main-ir-form : ∀ (m : C.Module) (ir : IR ⌊ Unit ⌋ ⌊ Unit ⌋) → moduleToIR m ≡ just ir → Form ir
main-ir-form m ir mi = form (main-node-of m ir mi)
  where
    form : MainNode m ir → Form ir
    form (es , ef-eq , b , bme , msc , mbody , mΨ , mse , md , mf , mce , ir≡ , rw) =
      mΨ , resolveExpr (C.cpolys msc) (C.declImps (C.CScope.ctele msc)) (("main" , EffUU) ∷ C.CScope.cimps msc) 0 mse
         , ir≡
         , msc , mbody , mse , md , mf , mce , es , b , bme , refl , rw

subst-app : ∀ {A : Set} {P : A → Set} {Q : Set} (f : (a : A) → P a → Q)
  {a a' : A} (eq : a ≡ a') (x : P a) → f a x ≡ f a' (subst P eq x)
subst-app f refl x = refl

mainRealized-bundle : ∀ (σ : SD.DefsSem) (m : C.Module) (mt : ModuleTyped m) (hvm : HasValidMain m mt)
  {es : List C.Entry} (b : FunBundle C.emptyCScope es) (bme : BMainExists b)
  (ef-eq : C.extractFunctions (C.extractAliases m) m ≡ inj₂ es) →
  SD.⟦ proj₂ (MC.mainRealized m mt hvm) ⟧ˢ fmt σ (env0 {proj₁ (MC.mainRealized m mt hvm)} tt)
  ≡ SD.⟦ proj₂ (bundle-realize b bme) ⟧ˢ fmt σ (env0 {proj₁ (bundle-realize b bme)} tt)
mainRealized-bundle σ m mt hvm {es} b bme ef-eq =
  trans (cong (λ z → SD.⟦ proj₂ z ⟧ˢ fmt σ (env0 {proj₁ z} tt)) (subst-app F ef-eq x))
    (trans (MI.mt-den-indep fmt σ mt' (bundle→typed b) me' (bme→me b bme) tt)
           (cong (λ z → SD.⟦ proj₂ z ⟧ˢ fmt σ (env0 {proj₁ z} tt)) (realize-agree b bme)))
  where
    Motive : (ef : String ⊎ List C.Entry) → Set
    Motive ef = Σ-syntax (ModuleTyped-ef m ef) (λ mtx → HasValidMain-ef m ef mtx)
    F : (ef : String ⊎ List C.Entry) → Motive ef → Σ-syntax (Usage 0) (λ Ψ → Expr ∅ Ψ EffUU)
    F ef (mtx , hv) = MC.mainRealized-ef m ef mtx hv
    x : Motive (C.extractFunctions (C.extractAliases m) m)
    x = mt , hvm
    x' : Motive (inj₂ es)
    x' = subst Motive ef-eq x
    mt' : ModTele emptyScope es
    mt' = proj₁ x'
    me' : MainIn mt'
    me' = proj₂ (proj₂ x')
