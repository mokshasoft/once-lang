-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CataErased
--
-- Plan 0.52 M2: the FUNCTOR-TRANSPORT lemma isolating the erasure round-trip
-- for the `Cata` recursion scheme. After M2 the IR's `Cata` folds the ERASED
-- functor `⌈eraseF F⌉F` at carrier `⟦⌊A⌋⟧ᴰᴵ` (`evalᴰ (Cata …)` via `wf-⌈⌉`),
-- while the surface/meaning fold runs over `F` at `⟦A⟧ᴰ`. This module proves
-- they coincide once bridged by `liftFn` (grade-blind `cohᴰ` transport) and the
-- SET-level functor round-trip `tF-coh : translateF ⌈eraseF F⌉F ≡ translateF F`.
--
-- The single export `evalᴰ-Cata-erased` lets the relational fold congruences
-- (`CataBridge.cata-bridge`, `FaithfulLemmas.cataM-fold`) stay at the SAME functor
-- `F` and SAME carrier `⟦A⟧ᴰ` — their original proofs are reused unchanged,
-- with this lemma discharging the erasure round-trip up front.
--
-- Own module (minimal, distinct-suffix `⟦_⟧` imports) mirroring `CataFold`/
-- `CataRel`/`CataBridge`, to keep the transport proof clear of `⟦_⟧`-mixfix soup.
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.CataErased (fmt : TargetNum) (ρ : CallEnv) where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst-subst-sym; subst-sym-subst)

open import Once.Semantics.Functor using (SFunctor; SK; _S⊕_; _S⊗_; μS; cataS; ⟦_⟧SF)
open import Once.Denotation.TraceMonad using (T; fmapT; RelT′; rel-ret; rel-call; rel-halt)
open import Once.Denotation.TraceMonadLaws using (fmapT-id; RelT′-bind; RelT′-fmap; RelT′-≡; ≡-RelT′)
open import Once.IRTy using (IRTy; IRFunctor; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⟦_⟧TI; ⌈⟧TI-commute)
open import Once.Denotation.DenotTrace
  using (evalᴰ; cata-ev-algᴰ)
open import Once.Denotation.Meaning using (cata-ev-algᴰ-D; cata-sem)
open import Once.Semantics.Machine
  using (⟦_⟧F; coerce-μ-out; tF-coh)
open import Once.Word using (Carrier)
open import Once.Type using (Type; Functor; ⟦_⟧T; μ-type)
open import Once.Functor.Translate using (WellFormedF; translateF; ⟦_,_⟧-base; wf-K; wf-Id; wf-Sum; wf-Prod; IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
open import Once.Denotation.DenotTrace using (liftFn; sigOpT; module CallEnv)
open CallEnv using (ffiE)
open import Once.Denotation.ValueDomain using (injectᵇ; forgetᵇ; ⟦_⟧ᴰᴵ; ⟦_⟧ᴰ; cohᴰ; coerce-functor⁻¹-D; seqF)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (conB; baseA)
open import Once.IRTy using (eraseF; ⌊⟧T-commute)
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉; base-⌊⌋; base-⌈⌉)
open import Once.Semantics.Value Carrier Carrier using (coerce-base-to-full)
open import Once.Semantics.ValueIR Carrier Carrier using (base-coh)
open import Once.Adequacy.CataRel using (RelSF; cataS-rel)
open import Once.Postulates using (extensionality)
open import Data.Sum using (_⊎_)
import Once.Type as TT
import Once.IRTy as II
import Once.IR as IR

------------------------------------------------------------------------
-- Generic transport helpers (both by matching the equation to `refl`).
------------------------------------------------------------------------

-- Plan 0.105: `T` is the interaction tree, so two computations are equal when
-- their trees are, and a transport of the result type is a map of the leaves.
subst-T-fmap : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X) → subst T eq h ≡ fmapT (subst (λ z → z) eq) h
subst-T-fmap refl h = sym (fmapT-id h)

-- A transport that undoes the one inside a map cancels it.
subst-T-fmap-cancel : ∀ {X Y Z : Set} (eq : X ≡ Y) (f : Z → Y) (m : T Z)
  → subst T eq (fmapT (λ v → subst (λ z → z) (sym eq) (f v)) m) ≡ fmapT f m
subst-T-fmap-cancel refl f m = refl

subst-cong-μS : ∀ {G₁ G₂ : SFunctor} (eq : G₁ ≡ G₂) (x : μS G₁)
  → subst (λ z → z) (cong μS eq) x ≡ subst μS eq x
subst-cong-μS refl x = refl

-- A `cataS` fold over `G₂` equals the fold over an equal functor `G₁`, with the
-- algebra pre-composed by the (inverse) functor transport and the seed transported.
cataS-subst-functor : ∀ {G₁ G₂ : SFunctor} {A : Set}
    (eq : G₂ ≡ G₁) (alg : ⟦ G₂ ⟧SF A → A) (x : μS G₂)
  → cataS {G₂} alg x
    ≡ cataS {G₁} (λ y → alg (subst (λ G → ⟦ G ⟧SF A) (sym eq) y)) (subst μS eq x)
cataS-subst-functor refl alg x = refl

-- Naturality of `evalᴰ` under a DOMAIN transport: substituting the source
-- object of an IR morphism is the same as back-transporting its argument.
evalᴰ-subst-dom : ∀ {o₁ o₂ : IRTy} {B : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR o₁ B) (z : ⟦ o₂ ⟧ᴰᴵ)
  → evalᴰ fmt ρ (subst (λ o → IR.IR o B) eq m) z ≡ evalᴰ fmt ρ m (subst ⟦_⟧ᴰᴵ (sym eq) z)
evalᴰ-subst-dom refl m z = refl

-- D131: the same naturality with a PAIRED domain — the transport moves only
-- the second component; the environment slot is untouched.
evalᴰ-subst-dom-pair : ∀ {E o₁ o₂ : IRTy} {B : IRTy} (eq : o₁ ≡ o₂)
    (m : IR.IR (E II.* o₁) B) (env : ⟦ E ⟧ᴰᴵ) (z : ⟦ o₂ ⟧ᴰᴵ)
  → evalᴰ fmt ρ (subst (λ o → IR.IR (E II.* o) B) eq m) (env , z)
    ≡ evalᴰ fmt ρ m (env , subst ⟦_⟧ᴰᴵ (sym eq) z)
evalᴰ-subst-dom-pair refl m env z = refl

-- …and the pair transport splits componentwise, so `liftFn` at a paired
-- domain reaches the algebra with the environment already back-transported.
pairᴰ-subst⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A') (b : B')
  → subst (λ z → z) (sym (cong₂ (λ x y → x × y) p q)) (a , b)
    ≡ (subst (λ z → z) (sym p) a , subst (λ z → z) (sym q) b)
pairᴰ-subst⁻ refl refl a b = refl

-- The IR-carrier cata trace-algebra is DEFINITIONALLY the Type-carrier one
-- (`cata-ev-algᴰ-D`) over the embedded functor `⌈F⌉F`, fed the algebra
-- `evalᴰ alg` pre-composed with the `⌈⟧TI-commute` re-embedding. Collapses the
-- IR-vs-meaning fold asymmetry so both sides become uniform `cata-sem` folds.
-- D131: the environment rides along as a value; the collapse is still `refl`,
-- because the per-layer algebra is `evalᴰ alg` PARTIALLY APPLIED to it.
-- D179: the carrier is now `T ⟦C⟧ᴰ` and the budget rides in it, so the `ℕ`
-- parameter is gone from both sides. The collapse is still `refl`.
cata-ev-algᴰ-is-D : ∀ {F : IRFunctor} {E C : IRTy} (wf : II.WellFormedFI F)
    (alg : IR.IR (E II.* ⟦ F ⟧TI C) C) (env : ⟦ E ⟧ᴰᴵ)
    (fc : ⟦ ⌈ F ⌉F ⟧F (T ⟦ C ⟧ᴰᴵ))
  → cata-ev-algᴰ fmt ρ {F} {E} {C} wf alg env fc
    ≡ cata-ev-algᴰ-D {⌈ F ⌉F} {⌈ C ⌉} (wf-⌈⌉ wf)
        (λ z → evalᴰ fmt ρ alg (env , subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute F C)) z)) fc
cata-ev-algᴰ-is-D wf alg env fc = refl

------------------------------------------------------------------------
-- `subst`-push helpers: a functor transport `sym (cong₂ _S⊕_/_S⊗_ …)` over a
-- `⟦_⟧SF` layer distributes into the injection / projection (all by `refl`).
------------------------------------------------------------------------

subst-S⊕-inj₁ : ∀ {F₁ F₂ G₁ G₂ : SFunctor} {X : Set}
    (p : F₁ ≡ G₁) (q : F₂ ≡ G₂) (a : ⟦ G₁ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊕_ p q)) (inj₁ a)
    ≡ inj₁ (subst (λ H → ⟦ H ⟧SF X) (sym p) a)
subst-S⊕-inj₁ refl refl a = refl

subst-S⊕-inj₂ : ∀ {F₁ F₂ G₁ G₂ : SFunctor} {X : Set}
    (p : F₁ ≡ G₁) (q : F₂ ≡ G₂) (b : ⟦ G₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊕_ p q)) (inj₂ b)
    ≡ inj₂ (subst (λ H → ⟦ H ⟧SF X) (sym q) b)
subst-S⊕-inj₂ refl refl b = refl

subst-S⊗ : ∀ {F₁ F₂ G₁ G₂ : SFunctor} {X : Set}
    (p : F₁ ≡ G₁) (q : F₂ ≡ G₂) (a : ⟦ G₁ ⟧SF X) (b : ⟦ G₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong₂ _S⊗_ p q)) (a , b)
    ≡ (subst (λ H → ⟦ H ⟧SF X) (sym p) a , subst (λ H → ⟦ H ⟧SF X) (sym q) b)
subst-S⊗ refl refl a b = refl

------------------------------------------------------------------------
-- Value-level `subst`-push helpers for `layer-z` (all `refl`): a functor
-- transport distributes into `inj₁/inj₂/pair` through each interpretation.
------------------------------------------------------------------------

pushᴰᴵ-+₁ : ∀ {A B A' B' : IRTy} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ II._+_ p q)) (inj₁ a) ≡ inj₁ (subst ⟦_⟧ᴰᴵ (sym p) a)
pushᴰᴵ-+₁ refl refl a = refl

pushᴰᴵ-+₂ : ∀ {A B A' B' : IRTy} (p : A ≡ A') (q : B ≡ B') (b : ⟦ B' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ II._+_ p q)) (inj₂ b) ≡ inj₂ (subst ⟦_⟧ᴰᴵ (sym q) b)
pushᴰᴵ-+₂ refl refl b = refl

pushᴰᴵ-* : ∀ {A B A' B' : IRTy} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰᴵ) (b : ⟦ B' ⟧ᴰᴵ)
  → subst ⟦_⟧ᴰᴵ (sym (cong₂ II._*_ p q)) (a , b)
    ≡ (subst ⟦_⟧ᴰᴵ (sym p) a , subst ⟦_⟧ᴰᴵ (sym q) b)
pushᴰᴵ-* refl refl a b = refl

pushᴰ-+₁ : ∀ {A B A' B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰ)
  → subst ⟦_⟧ᴰ (sym (cong₂ TT._+_ p q)) (inj₁ a) ≡ inj₁ (subst ⟦_⟧ᴰ (sym p) a)
pushᴰ-+₁ refl refl a = refl

pushᴰ-+₂ : ∀ {A B A' B' : Type} (p : A ≡ A') (q : B ≡ B') (b : ⟦ B' ⟧ᴰ)
  → subst ⟦_⟧ᴰ (sym (cong₂ TT._+_ p q)) (inj₂ b) ≡ inj₂ (subst ⟦_⟧ᴰ (sym q) b)
pushᴰ-+₂ refl refl b = refl

pushᴰ-* : ∀ {A B A' B' : Type} (p : A ≡ A') (q : B ≡ B') (a : ⟦ A' ⟧ᴰ) (b : ⟦ B' ⟧ᴰ)
  → subst ⟦_⟧ᴰ (sym (cong₂ TT._*_ p q)) (a , b)
    ≡ (subst ⟦_⟧ᴰ (sym p) a , subst ⟦_⟧ᴰ (sym q) b)
pushᴰ-* refl refl a b = refl

push-⊎₁ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A')
  → subst (λ z → z) (sym (cong₂ _⊎_ p q)) (inj₁ a) ≡ inj₁ (subst (λ z → z) (sym p) a)
push-⊎₁ refl refl a = refl

push-⊎₂ : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B')
  → subst (λ z → z) (sym (cong₂ _⊎_ p q)) (inj₂ b) ≡ inj₂ (subst (λ z → z) (sym q) b)
push-⊎₂ refl refl b = refl

push-× : ∀ {A B A' B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A') (b : B')
  → subst (λ z → z) (sym (cong₂ _×_ p q)) (a , b)
    ≡ (subst (λ z → z) (sym p) a , subst (λ z → z) (sym q) b)
push-× refl refl a b = refl

------------------------------------------------------------------------
-- `subst-SK` push + `base-z`: the K-node base-constant coherence (induction on
-- `IsBaseType`; atomic bases `refl`, Prod/Sum push+recurse). Discharges the K
-- case of `layer-z`.
------------------------------------------------------------------------

subst-SK : ∀ {S₁ S₂ X : Set} (e : S₁ ≡ S₂) (a : S₂)
  → subst (λ H → ⟦ H ⟧SF X) (sym (cong SK e)) a ≡ subst (λ z → z) (sym e) a
subst-SK refl a = refl

-- The K-node base-constant coherence (induction on `IsBaseType`): master's
-- `base-z`, at `injectᵇ` (plan 0.113 A2; D258 removed Str/Buffer, D243 added
-- `rigid`, which has no value).
base-z : ∀ {A} (ib : IsBaseType A) (y : ⟦ Carrier , Carrier ⟧-base A)
  → injectᵇ (base-⌈⌉ (base-⌊⌋ ib)) (coerce-base-to-full (base-⌈⌉ (base-⌊⌋ ib)) (subst (λ z → z) (sym (base-coh A)) y))
    ≡ subst (λ z → z) (sym (cohᴰ A)) (injectᵇ ib (coerce-base-to-full ib y))
base-z base-Unit   y = refl
base-z base-Void   ()
base-z base-Int    y = refl
base-z base-Float  y = refl
base-z (base-Prod {A} {B} pA pB) (a , b)
  rewrite push-× (base-coh A) (base-coh B) a b
        | push-× (cohᴰ A) (cohᴰ B) (injectᵇ pA (coerce-base-to-full pA a)) (injectᵇ pB (coerce-base-to-full pB b))
  = cong₂ _,_ (base-z pA a) (base-z pB b)
base-z (base-Sum {A} {B} pA pB) (inj₁ a)
  rewrite push-⊎₁ (base-coh A) (base-coh B) a
        | push-⊎₁ (cohᴰ A) (cohᴰ B) (injectᵇ pA (coerce-base-to-full pA a))
  = cong inj₁ (base-z pA a)
base-z (base-Sum {A} {B} pA pB) (inj₂ b)
  rewrite push-⊎₂ (base-coh A) (base-coh B) b
        | push-⊎₂ (cohᴰ A) (cohᴰ B) (injectᵇ pB (coerce-base-to-full pB b))
  = cong inj₂ (base-z pB b)
base-z base-rigid ()

module _ {A' : Type} where

  -- D179: the fold's carrier is a COMPUTATION, so this relates two of them:
  -- equal traces and corresponding values, at every budget. The trace and
  -- value halves can no longer be proved separately — the two sides run their
  -- children at budgets computed from their own traces, so the budgets line up
  -- only once the traces are known equal. `RelT′` bundles them for that reason.
  RelC : T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ → T ⟦ A' ⟧ᴰ → Set
  RelC = RelT′ (λ l r → subst (λ z → z) (cohᴰ A') l ≡ r)

  -- D179: ONE lemma where there were two (`layer-events` for the trace half,
  -- `layer-z` for the value half). With a computation carrier they cannot be
  -- separated — see `RelC`. Proved below by induction on `WellFormedF` (plan 0.113 A2).
  LayerRel : ∀ {G : Functor} → WellFormedF G → ⟦ ⌈ eraseF G ⌉F ⟧F ⟦ ⌊ A' ⌋ ⟧ᴰᴵ → ⟦ G ⟧F ⟦ A' ⟧ᴰ → Set
  LayerRel {G} wfG l r =
      subst ⟦_⟧ᴰᴵ (sym (⌊⟧T-commute G A'))
        (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF G) ⌊ A' ⌋))
          (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l))
    ≡ subst (λ z → z) (sym (cohᴰ (⟦ G ⟧T A')))
        (coerce-functor⁻¹-D wfG A' r)

  -- Plan 0.113 A2: PROVED again (master proved `layer-events`/`layer-z`; D179
  -- merged them into this relation and left it a postulate). `seqF` is a
  -- traversal, so the computation-level relation reduces, functor case by case,
  -- to a VALUE step over arbitrary related values — master's `layer-z` cases,
  -- now stated for any `l`/`r` — through `RelT′-fmap` / `RelT′-bind`.
  RelT′-mono : ∀ {X Y : Set} {R S : X → Y → Set} → (∀ {x y} → R x y → S x y)
             → ∀ {m n} → RelT′ R m n → RelT′ S m n
  RelT′-mono f (rel-ret r)  = rel-ret (f r)
  RelT′-mono f (rel-call k) = rel-call (λ b → RelT′-mono f (k b))
  RelT′-mono f rel-halt     = rel-halt

  id-step : ∀ {l : ⟦ ⌊ A' ⌋ ⟧ᴰᴵ} {r : ⟦ A' ⟧ᴰ} → subst (λ z → z) (cohᴰ A') l ≡ r → LayerRel wf-Id l r
  id-step {l} e = trans (sym (subst-sym-subst (cohᴰ A') {l})) (cong (subst (λ z → z) (sym (cohᴰ A'))) e)

  sum₁-step : ∀ {Fa Gb} (wfF : WellFormedF Fa) (wfG : WellFormedF Gb) l r
            → LayerRel wfF l r → LayerRel (wf-Sum wfF wfG) (inj₁ l) (inj₁ r)
  sum₁-step {Fa} {Gb} wfF wfG l r e
    rewrite pushᴰ-+₁ (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                     (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ l)
          | pushᴰᴵ-+₁ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A')
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋)) (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ l))
          | push-⊎₁ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A')) (coerce-functor⁻¹-D wfF A' r)
    = cong inj₁ e

  sum₂-step : ∀ {Fa Gb} (wfF : WellFormedF Fa) (wfG : WellFormedF Gb) l r
            → LayerRel wfG l r → LayerRel (wf-Sum wfF wfG) (inj₂ l) (inj₂ r)
  sum₂-step {Fa} {Gb} wfF wfG l r e
    rewrite pushᴰ-+₂ (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                     (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l)
          | pushᴰᴵ-+₂ (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A')
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)) (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l))
          | push-⊎₂ (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A')) (coerce-functor⁻¹-D wfG A' r)
    = cong inj₂ e

  prod-step : ∀ {Fa Gb} (wfF : WellFormedF Fa) (wfG : WellFormedF Gb) l r l′ r′
            → LayerRel wfF l r → LayerRel wfG l′ r′ → LayerRel (wf-Prod wfF wfG) (l , l′) (r , r′)
  prod-step {Fa} {Gb} wfF wfG l r l′ r′ e e′
    rewrite pushᴰ-* (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋) (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)
                     (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ l)
                     (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l′)
          | pushᴰᴵ-* (⌊⟧T-commute Fa A') (⌊⟧T-commute Gb A')
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Fa) ⌊ A' ⌋)) (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ l))
                     (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF Gb) ⌊ A' ⌋)) (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfG)) ⌈ ⌊ A' ⌋ ⌉ l′))
          | push-× (cohᴰ (⟦ Fa ⟧T A')) (cohᴰ (⟦ Gb ⟧T A'))
                   (coerce-functor⁻¹-D wfF A' r) (coerce-functor⁻¹-D wfG A' r′)
    = cong₂ _,_ e e′

  layer-rel : ∀ {G} (wfG : WellFormedF G)
      {y₁ : ⟦ translateF Carrier Carrier G ⟧SF (T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)}
      {y₂ : ⟦ translateF Carrier Carrier G ⟧SF (T ⟦ A' ⟧ᴰ)}
    → RelSF (translateF Carrier Carrier G) RelC y₁ y₂
    → RelT′ (LayerRel wfG)
        (seqF ⌈ eraseF G ⌉F
          (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfG)) _
            (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh G)) y₁)))
        (seqF G (coerce-μ-out wfG _ y₂))
  layer-rel {TT.K B} (wf-K ib) {y} {.y} refl =
    rel-ret (trans (cong (λ v → injectᵇ (base-⌈⌉ (base-⌊⌋ ib)) (coerce-base-to-full (base-⌈⌉ (base-⌊⌋ ib)) v))
                         (subst-SK (base-coh B) y))
                   (base-z ib y))
  layer-rel wf-Id rc = RelT′-mono id-step rc
  layer-rel (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₁ x₁} {inj₁ x₂} rsf
    rewrite subst-S⊕-inj₁ (tF-coh Fa) (tF-coh Gb) x₁ =
    RelT′-fmap (LayerRel wfF) (LayerRel (wf-Sum wfF wfG)) (sum₁-step wfF wfG) (layer-rel wfF rsf)
  layer-rel (wf-Sum {F = Fa} {G = Gb} wfF wfG) {inj₂ y₁} {inj₂ y₂} rsf
    rewrite subst-S⊕-inj₂ (tF-coh Fa) (tF-coh Gb) y₁ =
    RelT′-fmap (LayerRel wfG) (LayerRel (wf-Sum wfF wfG)) (sum₂-step wfF wfG) (layer-rel wfG rsf)
  layer-rel (wf-Sum wfF wfG) {inj₁ _} {inj₂ _} ()
  layer-rel (wf-Sum wfF wfG) {inj₂ _} {inj₁ _} ()
  layer-rel (wf-Prod {F = Fa} {G = Gb} wfF wfG) {x₁ , z₁} {x₂ , z₂} (rf , rg)
    rewrite subst-S⊗ (tF-coh Fa) (tF-coh Gb) x₁ z₁ =
    RelT′-bind (LayerRel wfF) (LayerRel (wf-Prod wfF wfG)) (layer-rel wfF rf) λ l r e →
    RelT′-bind (LayerRel wfG) (LayerRel (wf-Prod wfF wfG)) (layer-rel wfG rg) λ l′ r′ e′ →
    rel-ret (prod-step wfF wfG l r l′ r′ e e′)

  evalᴰ-Cata-erased : ∀ {F : Functor} {Eˢ : Type} (wfF : WellFormedF F)
      (mir : IR.IR (⌊ Eˢ ⌋ II.* ⌊ ⟦ F ⟧T A' ⌋) ⌊ A' ⌋) (env : ⟦ Eˢ ⟧ᴰ) (w : ⟦ μ-type F ⟧ᴰ)
    → liftFn fmt ρ {Eˢ TT.* μ-type F} {A'} (IR.Cata (wf-⌊⌋ wfF)
                    (subst (λ o → IR.IR (⌊ Eˢ ⌋ II.* o) ⌊ A' ⌋) (⌊⟧T-commute F A') mir))
             (env , w)
      ≡ cata-sem wfF (λ z → liftFn fmt ρ {Eˢ TT.* ⟦ F ⟧T A'} {A'} mir (env , z)) w
  evalᴰ-Cata-erased {F} {Eˢ} wfF mir env w = body
    where
      mir' : IR.IR (⌊ Eˢ ⌋ II.* ⟦ eraseF F ⟧TI ⌊ A' ⌋) ⌊ A' ⌋
      mir' = subst (λ o → IR.IR (⌊ Eˢ ⌋ II.* o) ⌊ A' ⌋) (⌊⟧T-commute F A') mir

      w' : ⟦ ⌊ μ-type F ⌋ ⟧ᴰᴵ
      w' = subst (λ z → z) (sym (cohᴰ (μ-type F))) w

      seed-eq : subst μS (tF-coh F) w' ≡ w
      seed-eq = trans (sym (subst-cong-μS (tF-coh F) w'))
                      (subst-subst-sym {P = λ z → z} (cong μS (tF-coh F)))

      -- plan 0.97: ONE equation of computations, where there used to be a
      -- budget-indexed family of pair equations. `T` is a record, so the
      -- conclusion is assembled by eta (`to-subst-eq`) from the SAME
      -- relation `rc` the fold already produces — the trace and value halves
      -- no longer have to be re-paired by hand at every budget.
      body : liftFn fmt ρ {Eˢ TT.* μ-type F} {A'} (IR.Cata (wf-⌊⌋ wfF) mir') (env , w)
           ≡ cata-sem wfF (λ z → liftFn fmt ρ {Eˢ TT.* ⟦ F ⟧T A'} {A'} mir (env , z)) w
      body = trans (cong (λ W → subst T (cohᴰ A')
                             (evalᴰ fmt ρ (IR.Cata (wf-⌊⌋ wfF) mir') W))
                          (pairᴰ-subst⁻ (cohᴰ Eˢ) (cohᴰ (μ-type F)) env w))
             (trans (cong (subst T (cohᴰ A')) Lr≡) (to-subst-eq rc))
        where
          dalg_L : ⟦ ⟦ ⌈ eraseF F ⌉F ⟧T ⌈ ⌊ A' ⌋ ⌉ ⟧ᴰ → T ⟦ ⌈ ⌊ A' ⌋ ⌉ ⟧ᴰ
          dalg_L z = evalᴰ fmt ρ mir' ( subst (λ t → t) (sym (cohᴰ Eˢ)) env
                                     , subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF F) ⌊ A' ⌋)) z )

          algL : ⟦ translateF Carrier Carrier (⌈ eraseF F ⌉F) ⟧SF (T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ
          algL y = cata-ev-algᴰ-D {⌈ eraseF F ⌉F} {⌈ ⌊ A' ⌋ ⌉} (wf-⌈⌉ (wf-⌊⌋ wfF)) dalg_L (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _ y)

          algL' : ⟦ translateF Carrier Carrier F ⟧SF (T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ) → T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ
          algL' y = algL (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh F)) y)

          algM : ⟦ translateF Carrier Carrier F ⟧SF (T ⟦ A' ⟧ᴰ) → T ⟦ A' ⟧ᴰ
          algM y = cata-ev-algᴰ-D {F} {A'} wfF (λ z → liftFn fmt ρ {Eˢ TT.* ⟦ F ⟧T A'} {A'} mir (env , z)) (coerce-μ-out wfF _ y)

          -- D179: an equality of COMPUTATIONS now — the fold produces a `T`
          -- directly, so there is no budget to apply here.
          Lr≡ : evalᴰ fmt ρ (IR.Cata (wf-⌊⌋ wfF) mir')
                      (subst (λ t → t) (sym (cohᴰ Eˢ)) env , w') ≡ cataS {translateF Carrier Carrier F} algL' w
          Lr≡ = trans (cataS-subst-functor (tF-coh F) algL w')
                      (cong (cataS {translateF Carrier Carrier F} algL') seed-eq)

          -- D179: one `RelT′-bind`. The head is `seqF` of the two layers
          -- (`layer-rel`); the continuation is the algebra, whose two sides
          -- are related by the SAME `step-eq` chain as before — with
          -- `layer-z` replaced by `layer-rel`'s value half at budget `k`.
          from-subst-eq : ∀ {l : T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ} {r : T ⟦ A' ⟧ᴰ}
                        → subst T (cohᴰ A') l ≡ r → RelC l r
          from-subst-eq {l} eq = ≡-RelT′ (subst (λ z → z) (cohᴰ A')) l (trans (sym (subst-T-fmap (cohᴰ A') l)) eq)

          to-subst-eq : ∀ {l : T ⟦ ⌊ A' ⌋ ⟧ᴰᴵ} {r : T ⟦ A' ⟧ᴰ}
                      → RelC l r → subst T (cohᴰ A') l ≡ r
          to-subst-eq {l} rel = trans (subst-T-fmap (cohᴰ A') l) (RelT′-≡ (subst (λ z → z) (cohᴰ A')) rel)

          algR-full : ∀ {y₁ y₂} → RelSF (translateF Carrier Carrier F) RelC y₁ y₂ → RelC (algL' y₁) (algM y₂)
          algR-full {y₁} {y₂} rsf =
            RelT′-bind (LayerRel wfF) (λ l r → subst (λ z → z) (cohᴰ A') l ≡ r)
              {m = mL} {m′ = mM} {f = contL} {f′ = contM}
              (layer-rel wfF rsf)
              (λ x y lr → from-subst-eq (step-eq x y lr))
            where
              mL : T (⟦ ⌈ eraseF F ⌉F ⟧F ⟦ ⌊ A' ⌋ ⟧ᴰᴵ)
              mL = seqF ⌈ eraseF F ⌉F
                     (coerce-μ-out (wf-⌈⌉ (wf-⌊⌋ wfF)) _
                       (subst (λ H → ⟦ H ⟧SF _) (sym (tF-coh F)) y₁))
              mM : T (⟦ F ⟧F ⟦ A' ⟧ᴰ)
              mM = seqF F (coerce-μ-out wfF _ y₂)

              contL = λ layer → dalg_L (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ layer)
              contM = λ layer → liftFn fmt ρ {Eˢ TT.* ⟦ F ⟧T A'} {A'} mir
                                  (env , coerce-functor⁻¹-D wfF A' layer)

              -- plan 0.98: stated at the VALUES. The budget was only ever a way to
              -- NAME them, and `valueT` cannot name a value that may not
              -- exist — the caller now supplies the two the head returned.
              step-eq : ∀ x y → LayerRel wfF x y
                      → subst T (cohᴰ A') (contL (x)) ≡ contM (y)
              step-eq x y lr =
                trans (cong (subst T (cohᴰ A'))
                        (evalᴰ-subst-dom-pair (⌊⟧T-commute F A') mir
                           (subst (λ t → t) (sym (cohᴰ Eˢ)) env)
                           (subst ⟦_⟧ᴰ (sym (⌈⟧TI-commute (eraseF F) ⌊ A' ⌋))
                                  (coerce-functor⁻¹-D (wf-⌈⌉ (wf-⌊⌋ wfF)) ⌈ ⌊ A' ⌋ ⌉ (x)))))
                  (trans (cong (λ Z → subst T (cohᴰ A')
                                  (evalᴰ fmt ρ mir (subst (λ t → t) (sym (cohᴰ Eˢ)) env , Z))) lr)
                         (cong (λ W → subst T (cohᴰ A') (evalᴰ fmt ρ mir W))
                               (sym (pairᴰ-subst⁻ (cohᴰ Eˢ) (cohᴰ (⟦ F ⟧T A')) env _))))

          rc : RelC (cataS {translateF Carrier Carrier F} algL' w) (cataS {translateF Carrier Carrier F} algM w)
          rc = cataS-rel RelC algR-full w

-- A SigOp's lifted meaning is its contract's computation at the first-order
-- argument, read into the value domain (plan 0.105: no emission rule, no
-- `semM` — the tree node IS the event).
liftFn-SigOp : ∀ {A B : Type} (info : SigOpInfo A B)
  → liftFn fmt ρ {A} {B} (IR.SigOp info)
    ≡ (λ arg → fmapT (injectᵇ (conB info)) (sigOpT fmt (ffiE ρ) info (forgetᵇ (baseA info) arg)))
liftFn-SigOp {A} {B} info = extensionality λ arg →
  trans (subst-T-fmap-cancel (cohᴰ B) (injectᵇ (conB info))
           (sigOpT fmt (ffiE ρ) info (forgetᵇ (baseA info)
              (subst (λ z → z) (cohᴰ A) (subst (λ z → z) (sym (cohᴰ A)) arg)))))
        (cong (λ w → fmapT (injectᵇ (conB info)) (sigOpT fmt (ffiE ρ) info (forgetᵇ (baseA info) w)))
              (subst-subst-sym {P = λ z → z} (cohᴰ A)))
