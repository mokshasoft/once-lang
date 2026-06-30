-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

------------------------------------------------------------------------
-- Once.TypeCheck.MorphComplete — the morphism-completeness theorem
-- (Plan 0.49 / D063-D066): every `⊢ᵐ` morphism check-elaborates at its
-- grade. Discharges the `morph-complete` postulate in `Completeness`.
--
-- Strong form (`StrongElab`): `checkElabV` reduces to `(success 0 E d fr , W)`
-- where the result expression `E` extracts a morphism (`extract-morph-eff E ≡
-- just (m , refl)` — handles lift-morphism / arr' / cata uniformly) and the
-- witness `W` extracts the `⊢ᵐ` derivation (`extractMorphWitness W ≡ just mᵐ`).
-- The recursive cases rewrite the arms' equations so the consumer's
-- `with extract-morph-eff … | extractMorphWitness …` reduces.
------------------------------------------------------------------------

module Once.TypeCheck.MorphComplete where

open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.String using (String)

open import Once.Type as T using (Type; Functor; μ-type; ⟦_⟧T)
open import Once.IR using (IR; Heap)
open import Once.Functor.Translate using (WellFormedF)
open import Once.Functor.Decide using (wellFormedF?)
open import Once.TypeCheck.Raw as Raw using (RawExpr)
open import Once.CanonicalName using (CanonicalName; showCanonical)
open import Once.TypeCheck.Classify using (NamedCtx; composeMid;
  lookupLocal; lookupImport; ctxWithImportsAndPolys;
  inspectLookupLocal; inspectLookupImport; llv-found; llv-not-found; liv-found; liv-not-found)
open import Once.Surface.Syntax as Srf using (Expr; lift-morphism; zeroUsage)
open import Once.Denotation.Realize using (realize-morph)
open import Once.TypeCheck.Judgment
open import Once.TypeCheck.Elaborate
  using (checkElab; checkElabV; checkComposeGo; extract-morph-eff;
         inferElabV; inferElabV-RVar-fail-bridge;
         success; failure; _≟T_)

private
  just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

-- `checkElabV` on a morphism succeeds with an extractable result + witness.
StrongElab : (ctx : NamedCtx) (e : RawExpr) (A B : Type) (π : T.Purity) → Set
StrongElab ctx e A B π =
  Σ-syntax (IR A B) λ m →
  Σ-syntax (ctx ⊢ᵐ e ∶ A ⇨[ π ] B) λ mᵐ →
  Σ-syntax (Srf.Expr (NamedCtx.debruijn ctx) zeroUsage (A T.⇒[ T.mk-kind T.Many π ] B)) λ E →
  Σ-syntax ℕ λ d → Σ-syntax ℕ λ fr →
  Σ-syntax (ctx ⊢ᶜ e ∶ (A T.⇒[ T.mk-kind T.Many π ] B) ⨾ zeroUsage) λ W →
    (checkElabV ctx e (A T.⇒[ T.mk-kind T.Many π ] B) ≡ (success zeroUsage E d fr , W))
  × (extract-morph-eff E ≡ just (m , refl))
  × (extractMorphWitness W ≡ just mᵐ)
  × (m ≡ realize-morph mᵐ)

private
  -- `checkComposeGo` is called at the canonical `(composeMid …, refl)`; any
  -- `(mid, p)` collapses to it by J (singleton contractibility).
  go-canonical : ∀ {ctx f g A C} {π : T.Purity} {mid}
    (p : composeMid ctx f g A ≡ mid)
    → checkComposeGo ctx f g A C π mid p
      ≡ checkComposeGo ctx f g A C π (composeMid ctx f g A) refl
  go-canonical refl = refl

  -- The (just B) branch of checkComposeGo reduces to the compose success once
  -- the two arm checks + their morphism/witness extractions are known.
  composeGo-success : ∀ {ctx f g A C} {π : T.Purity} {B}
    {mf : IR B C} {mg : IR A B} {Ef : _} {Eg : _} {Wf : _} {Wg : _} {mFᵐ : _} {mGᵐ : _}
    {df ff dg fg : ℕ}
    (eqB : composeMid ctx f g A ≡ just B)
    → checkElabV ctx f (B T.⇒[ T.mk-kind T.Many π ] C)
        ≡ (success zeroUsage Ef df ff , Wf)
    → checkElabV ctx g (A T.⇒[ T.mk-kind T.Many π ] B)
        ≡ (success zeroUsage Eg dg fg , Wg)
    → extract-morph-eff Ef ≡ just (mf , refl)
    → extract-morph-eff Eg ≡ just (mg , refl)
    → extractMorphWitness Wf ≡ just mFᵐ
    → extractMorphWitness Wg ≡ just mGᵐ
    → Σ-syntax (IR A C) λ m → Σ-syntax ℕ λ d → Σ-syntax ℕ λ fr →
        (checkComposeGo ctx f g A C π (just B) eqB
          ≡ (success zeroUsage (lift-morphism m) d fr , t-morph-lift (m-compose eqB mFᵐ mGᵐ)))
        × (m ≡ mf IR.∘ mg)
  composeGo-success eqB eqf eqg exf exg exwf exwg
    rewrite eqg | eqf | exf | exg | exwf | exwg = _ , _ , _ , refl , refl

-- Three cases are scoped follow-ups (kept as StrongElab postulates so the
-- recursive cases can still take them as arms). They are NOT discharged here:
--   • m-const  — needs a STRONG gd-complete (checkElabV-with-witness form; the
--                Completeness `gd-complete` is checkElab-weak). Mutual-w/-Completeness.
--   • m-cata   — needs a STRONG check-complete on the (⊢ᶜ) algebra. Mutual-w/-Completeness.
--   • m-named  — a bare import elaborates to a CLOSURE pre-plan-0.50 (D064); becomes a
--                direct `IR.SigOp` morphism in plan 0.50 milestone 1, when this is proven.
postulate
  const-morph-strong : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : T.Purity}
                     → ctx ⊢ᵍ e ∶ B → StrongElab ctx e A B π
  cata-morph-strong : ∀ {ctx : NamedCtx} {alg : RawExpr} {F : Functor} {A : Type}
                        {π : T.Purity} {wfF : WellFormedF F}
                    → wellFormedF? F ≡ just wfF
                    → ctxWithImportsAndPolys (NamedCtx.imports ctx) (NamedCtx.polys ctx)
                        ⊢ᶜ alg ∶ (⟦ F ⟧T A T.⇒[ T.mk-kind T.Many π ] A) ⨾ zeroUsage
                    → StrongElab ctx (Raw.RApp (Raw.RVar "cata") alg) (μ-type F) A π
  named-morph-strong : ∀ {ctx : NamedCtx} {x : String} {A B : Type} {π : T.Purity}
                     → ¬ (x ≡ "unit")
                     → lookupLocal ctx x ≡ nothing
                     → lookupImport (NamedCtx.imports ctx) x
                         ≡ just (A T.⇒[ T.mk-kind T.Many π ] B)
                     → StrongElab ctx (Raw.RVar x) A B π
  -- Plan 0.50 Stage 2 (D064): the RESOLVED-name strong-elab leaf, at PARITY with
  -- `named-morph-strong` (same scoped hole, for `RResolved cn`). Discharging both
  -- is the milestone-1 follow-up; the constructor + this leaf make value-use of a
  -- named function (`compose g g`) elaborate as a morphism.
  named-morph-strong-resolved : ∀ {ctx : NamedCtx} {cn : CanonicalName} {A B : Type} {π : T.Purity}
                              → lookupImport (NamedCtx.imports ctx) (showCanonical cn)
                                  ≡ just (A T.⇒[ T.mk-kind T.Many π ] B)
                              → StrongElab ctx (Raw.RResolved cn) A B π

morph-elab : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : T.Purity}
           → ctx ⊢ᵐ e ∶ A ⇨[ π ] B → StrongElab ctx e A B π
-- ---- bare point-free builtins (grade-poly) ----
morph-elab {ctx = ctx} (m-id {T = TT} eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "id") | inferElabV-RVar-fail-bridge ctx "id" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "id" | inspectLookupImport ctx "id"
... | llv-not-found eqL | liv-not-found eqI with TT ≟T TT
...   | yes refl = IR.id , m-id eqL eqI , _ , _ , _ , t-morph-lift (m-id eqL eqI) , refl , refl , refl , refl
...   | no ¬eq = ⊥-elim (¬eq refl)
morph-elab (m-id eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-id eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))

morph-elab {ctx = ctx} (m-fst {A = A} {B = B} eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "fst") | inferElabV-RVar-fail-bridge ctx "fst" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "fst" | inspectLookupImport ctx "fst"
... | llv-not-found eqL | liv-not-found eqI with A ≟T A
...   | yes refl = IR.fst , m-fst eqL eqI , _ , _ , _ , t-morph-lift (m-fst eqL eqI) , refl , refl , refl , refl
...   | no ¬eq = ⊥-elim (¬eq refl)
morph-elab (m-fst eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-fst eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))

morph-elab {ctx = ctx} (m-snd {A = A} {B = B} eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "snd") | inferElabV-RVar-fail-bridge ctx "snd" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "snd" | inspectLookupImport ctx "snd"
... | llv-not-found eqL | liv-not-found eqI with B ≟T B
...   | yes refl = IR.snd , m-snd eqL eqI , _ , _ , _ , t-morph-lift (m-snd eqL eqI) , refl , refl , refl , refl
...   | no ¬eq = ⊥-elim (¬eq refl)
morph-elab (m-snd eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-snd eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))

morph-elab {ctx = ctx} (m-terminal eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "terminal") | inferElabV-RVar-fail-bridge ctx "terminal" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "terminal" | inspectLookupImport ctx "terminal"
... | llv-not-found eqL | liv-not-found eqI = IR.terminal , m-terminal eqL eqI , _ , _ , _ , t-morph-lift (m-terminal eqL eqI) , refl , refl , refl , refl
morph-elab (m-terminal eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-terminal eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))

morph-elab {ctx = ctx} (m-initial eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "initial") | inferElabV-RVar-fail-bridge ctx "initial" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "initial" | inspectLookupImport ctx "initial"
... | llv-not-found eqL | liv-not-found eqI = IR.initial , m-initial eqL eqI , _ , _ , _ , t-morph-lift (m-initial eqL eqI) , refl , refl , refl , refl
morph-elab (m-initial eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-initial eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))

morph-elab {ctx = ctx} (m-inl {A = A} {B = B} eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "inl") | inferElabV-RVar-fail-bridge ctx "inl" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "inl" | inspectLookupImport ctx "inl"
... | llv-not-found eqL | liv-not-found eqI with A ≟T A
...   | yes refl = IR.inl Heap , m-inl eqL eqI , _ , _ , _ , t-morph-lift (m-inl eqL eqI) , refl , refl , refl , refl
...   | no ¬eq = ⊥-elim (¬eq refl)
morph-elab (m-inl eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-inl eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))

morph-elab {ctx = ctx} (m-inr {A = A} {B = B} eqLoc eqImp)
  with inferElabV ctx (Raw.RVar "inr") | inferElabV-RVar-fail-bridge ctx "inr" (λ ()) eqLoc eqImp
... | (failure _ , _) | refl
  with inspectLookupLocal ctx "inr" | inspectLookupImport ctx "inr"
... | llv-not-found eqL | liv-not-found eqI with B ≟T B
...   | yes refl = IR.inr Heap , m-inr eqL eqI , _ , _ , _ , t-morph-lift (m-inr eqL eqI) , refl , refl , refl , refl
...   | no ¬eq = ⊥-elim (¬eq refl)
morph-elab (m-inr eqLoc eqImp) | (failure _ , _) | refl | llv-found imp | _ = ⊥-elim (just≢nothing (trans (sym imp) eqLoc))
morph-elab (m-inr eqLoc eqImp) | (failure _ , _) | refl | _ | liv-found imp = ⊥-elim (just≢nothing (trans (sym imp) eqImp))
-- ---- extensional leaves (HOLES) ----
morph-elab (m-const gd) = const-morph-strong gd
morph-elab (m-named ¬u eqL eqI) = named-morph-strong ¬u eqL eqI
morph-elab (m-named-resolved eqI) = named-morph-strong-resolved eqI
-- ---- recursive combinators ----
morph-elab (m-compose {B = Bmid} eqB df dg) with morph-elab df | morph-elab dg
... | (mf , mFᵐ , Ef , _ , _ , Wf , eqf , exEff-f , exW-f , cons-f) | (mg , mGᵐ , Eg , _ , _ , Wg , eqg , exEff-g , exW-g , cons-g)
      with composeGo-success eqB eqf eqg exEff-f exEff-g exW-f exW-g
...     | (m , d , fr , eqGo , m≡fg) =
        m , m-compose eqB mFᵐ mGᵐ , _ , d , fr , t-morph-lift (m-compose eqB mFᵐ mGᵐ) ,
        trans (sym (go-canonical eqB)) eqGo , refl , refl ,
        trans m≡fg (cong₂ IR._∘_ cons-f cons-g)
morph-elab (m-case df dg) with morph-elab df | morph-elab dg
... | (mf , mFᵐ , Ef , _ , _ , Wf , eqf , exEff-f , exW-f , cons-f) | (mg , mGᵐ , Eg , _ , _ , Wg , eqg , exEff-g , exW-g , cons-g)
      rewrite eqf | eqg | exEff-f | exEff-g | exW-f | exW-g =
      _ , m-case mFᵐ mGᵐ , _ , _ , _ , _ , refl , refl , refl , cong₂ IR.case cons-f cons-g
morph-elab (m-pair df dg) with morph-elab df | morph-elab dg
... | (mf , mFᵐ , Ef , _ , _ , Wf , eqf , exEff-f , exW-f , cons-f) | (mg , mGᵐ , Eg , _ , _ , Wg , eqg , exEff-g , exW-g , cons-g)
      rewrite eqf | eqg | exEff-f | exEff-g | exW-f | exW-g =
      _ , m-pair mFᵐ mGᵐ , _ , _ , _ , _ , refl , refl , refl , cong₂ (λ x y → IR.⟨ x , y ⟩ Heap) cons-f cons-g
morph-elab (m-curry df) with morph-elab df
... | (mf , mFᵐ , Ef , _ , _ , Wf , eqf , exEff-f , exW-f , cons-f)
      rewrite eqf | exEff-f | exW-f = _ , _ , _ , _ , _ , _ , refl , refl , refl , cong (λ z → IR.curry z Heap) cons-f
morph-elab (m-cata eqWF dalg) = cata-morph-strong eqWF dalg

-- The weak (checkElab) morphism-completeness, derived from the strong form.
-- (`checkElab = proj₁ ∘ checkElabV`, Elaborate:1071.)
morph-complete : ∀ {ctx : NamedCtx} {e : RawExpr} {A B : Type} {π : T.Purity}
               → ctx ⊢ᵐ e ∶ A ⇨[ π ] B
               → ∃-syntax (λ eE → ∃-syntax (λ d → ∃-syntax (λ f →
                   checkElab ctx e (A T.⇒[ T.mk-kind T.Many π ] B)
                     ≡ success zeroUsage eE d f)))
morph-complete d with morph-elab d
... | (_ , _ , E , d′ , fr , _ , eqV , _ , _ , _) = E , d′ , fr , cong proj₁ eqV
