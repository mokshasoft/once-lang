-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Denotation.EvalRel — the IR evaluator respects the value relation
-- (plan 0.119 D5).
--
-- `eval-rel` is the fundamental lemma of `ValueRel.RelD` for the IR: a term
-- evaluated at related call environments takes related inputs to related runs.
-- It is what lets a proof about meanings treat an IR term it does not inspect
-- (a pre-built morphism, a reference's call) as a black box. `liftFn-rel`
-- states it at the source value domain, through `cohᴰ` (`RelD-coh`/`RelD-coh⁻`:
-- the relation at `⌈ ⌊ A ⌋ ⌉` IS the relation at `A`, read across the
-- transport).
------------------------------------------------------------------------

module Once.Denotation.EvalRel where

open import Once.Spec.Type using (var; Ty; Fun)
open import Function using () renaming (id to idᶠ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Numerics using (TargetNum)
open import Once.IR
open import Once.IRTy using (IRTy; ⌊_⌋; ⌈_⌉; ⌈_⌉F; ⌈⟧TI-commute; ⟦_⟧TI; _≟IRTy_; IsBaseTypeI; WellFormedFI)
import Once.IRTy as II
open import Once.IRTy.WF using (wf-⌈⌉; base-⌊⌋)
open import Once.CanonicalName using (_≟ᶜ_)
open import Once.IR.Semantics.Trace using (T; ret; call; halt; FFIAnswers; RelT′; rel-ret; rel-call; rel-halt)
open import Once.IR.Semantics.Iterative using (T∞; return∞; _>>=∞_; embed; fmap∞)
open T∞ using (force)
open import Once.SigOp.Info using (SigOpInfo; module SigOpInfo)
open SigOpInfo using (baseA; conB)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn; CallEnv; cata-ev-algᴰ; module CallEnv)
open CallEnv using (callsE; ffiE)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Denotation.Program using (IRFun; tableEnv; tableCalls; tableEnv-at)
open Once.Denotation.Program.IRFun using (fbody; fcod; fdom; fname)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelSB; module RelS; s-ret; s-next; s-call; s-halt; RelS-bind; relS-ret; RelS-embed; RelS-iter∞)
open RelS using (forceS)
open import Once.Denotation.ValueRel
open import Once.IR.Semantics.StreamInf using (νᴵ)
open import Once.Spec.Type as Ty using (Type; Unit; Void; _*_; _+_; _⇒[_]_; Int; Float)
open import Once.Spec.Type using (μ; ν)
open import Once.Spec.Grade using (mk-kind; Zero; One; Many)
open import Once.IR.Semantics.FunctorMeaning using (translateF)
import Once.Type.Concrete as LW
import Once.Spec.Type as LW
open import Once.Spec.Word using (Carrier)
open import Once.IR.Semantics.Value Carrier Carrier using () renaming (⟦_⟧F to ⟦_⟧F′)

------------------------------------------------------------------------
-- IR base types: related is equal, and equal is related.
------------------------------------------------------------------------

base-eqI : ∀ {A : IRTy} → IsBaseTypeI A → ∀ {x y : ⟦ A ⟧ᴰᴵ} → RelD ⌈ A ⌉ x y → x ≡ y
base-eqI II.base-Unit       _ = refl
base-eqI II.base-Void {()}
base-eqI II.base-Int        r = r
base-eqI II.base-Float      r = r
base-eqI (II.base-Prod a b) {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) with base-eqI a r₁ | base-eqI b r₂
... | refl | refl = refl
base-eqI (II.base-Sum a b) {inj₁ x} {inj₁ y} r = cong inj₁ (base-eqI a r)
base-eqI (II.base-Sum a b) {inj₂ x} {inj₂ y} r = cong inj₂ (base-eqI b r)
base-eqI (II.base-Sum a b) {inj₁ _} {inj₂ _} ()
base-eqI (II.base-Sum a b) {inj₂ _} {inj₁ _} ()

base-reflI : ∀ {A : IRTy} → IsBaseTypeI A → ∀ (x : ⟦ A ⟧ᴰᴵ) → RelD ⌈ A ⌉ x x
base-reflI II.base-Unit       x = tt
base-reflI II.base-Void       ()
base-reflI II.base-Int        x = refl
base-reflI II.base-Float      x = refl
base-reflI (II.base-Prod a b) (x , y) = base-reflI a x , base-reflI b y
base-reflI (II.base-Sum a b)  (inj₁ x) = base-reflI a x
base-reflI (II.base-Sum a b)  (inj₂ y) = base-reflI b y

-- A first-order layer over μ: related is equal, and equal is related.
fo-eq : ∀ {F G : II.IRFunctor} → WellFormedFI F → ∀ {x y : ⟦ ⟦ F ⟧TI (II.μ-type G) ⟧ᴰᴵ} → RelD ⌈ ⟦ F ⟧TI (II.μ-type G) ⌉ x y → x ≡ y
fo-eq (II.wf-K b)       r = base-eqI b r
fo-eq II.wf-Id          r = r
fo-eq (II.wf-Sum f g) {inj₁ x} {inj₁ y} r = cong inj₁ (fo-eq f r)
fo-eq (II.wf-Sum f g) {inj₂ x} {inj₂ y} r = cong inj₂ (fo-eq g r)
fo-eq (II.wf-Sum f g) {inj₁ _} {inj₂ _} ()
fo-eq (II.wf-Sum f g) {inj₂ _} {inj₁ _} ()
fo-eq (II.wf-Prod f g) {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) with fo-eq f r₁ | fo-eq g r₂
... | refl | refl = refl

fo-refl : ∀ {F G : II.IRFunctor} → WellFormedFI F → ∀ (x : ⟦ ⟦ F ⟧TI (II.μ-type G) ⟧ᴰᴵ) → RelD ⌈ ⟦ F ⟧TI (II.μ-type G) ⌉ x x
fo-refl (II.wf-K b)      x        = base-reflI b x
fo-refl II.wf-Id         x        = refl
fo-refl (II.wf-Sum f g)  (inj₁ x) = fo-refl f x
fo-refl (II.wf-Sum f g)  (inj₂ y) = fo-refl g y
fo-refl (II.wf-Prod f g) (x , y)  = fo-refl f x , fo-refl g y

------------------------------------------------------------------------
-- Runs.
------------------------------------------------------------------------

-- Two runs that return at once, related values.
RelS-now : ∀ {X Y} {R : X → Y → Set} {m : T∞ X} {m′ : T∞ Y} {v v′}
         → force m ≡ ret (inj₁ v) → force m′ ≡ ret (inj₁ v′) → R v v′ → RelS R m m′
forceS (RelS-now {R = R} {m = m} {m′} e e′ r) = subst₂′ e e′ (s-ret r)
  where
    subst₂′ : ∀ {a b c d} → a ≡ c → b ≡ d → RelSB R c d → RelSB R a b
    subst₂′ refl refl h = h

-- A finite tree is related to itself, call for call.
RelT′-refl : ∀ {X} {R : X → X → Set} → (∀ x → R x x) → ∀ (t : T X) → RelT′ R t t
RelT′-refl h (ret x)      = rel-ret (h x)
RelT′-refl h (call o a k) = rel-call (λ b → RelT′-refl h (k b))
RelT′-refl h (halt o a)   = rel-halt

------------------------------------------------------------------------
-- The relation on call environments, and the evaluator's fundamental lemma.
------------------------------------------------------------------------

module _ (fmt : TargetNum) where

  RelEnv : CallEnv → CallEnv → Set
  RelEnv ρ ρ′ = (∀ f (A B : IRTy) {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (callsE ρ f A B a) (callsE ρ′ f A B a′))
              × (ffiE ρ ≡ ffiE ρ′)

  module _ {ρ ρ′ : CallEnv} (re : RelEnv ρ ρ′) where
    private
      E  : ∀ {A B} → IR A B → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
      E  = evalᴰ fmt ρ
      E′ : ∀ {A B : IRTy} → IR A B → ⟦ A ⟧ᴰᴵ → T∞ ⟦ B ⟧ᴰᴵ
      E′ = evalᴰ fmt ρ′

    -- A SigOp's block is a finite tree of first-order values.
    sigop-rel : ∀ {X Y} (si : SigOpInfo X Y) {a a′} → RelD ⌈ ⌊ X ⌋ ⌉ a a′ → RelS (RelD ⌈ ⌊ Y ⌋ ⌉) (E (SigOp si) a) (E′ (SigOp si) a′)
    sigop-rel si {a} r with base-eqI (base-⌊⌋ (baseA si)) r
    ... | refl rewrite proj₂ re =
      RelS-embed (RelT′-refl (base-reflI (base-⌊⌋ (conB si))) _)

    eval-rel : ∀ {A B} (ir : IR A B) {a a′} → RelD ⌈ A ⌉ a a′ → RelS (RelD ⌈ B ⌉) (E ir a) (E′ ir a′)
    eval-rel id         r = relS-ret r
    eval-rel (g ∘ f)    r = RelS-bind (eval-rel f r) (λ r′ → eval-rel g r′)
    eval-rel fst        r = relS-ret (proj₁ r)
    eval-rel snd        r = relS-ret (proj₂ r)
    eval-rel ⟨ f , g ⟩  r = RelS-bind (eval-rel f r) (λ rb → RelS-bind (eval-rel g r) (λ rc → relS-ret (rb , rc)))
    eval-rel inl        r = relS-ret r
    eval-rel inr        r = relS-ret r
    eval-rel (case f g) {inj₁ a} {inj₁ a′} r = eval-rel f r
    eval-rel (case f g) {inj₂ b} {inj₂ b′} r = eval-rel g r
    eval-rel (case f g) {inj₁ _} {inj₂ _} ()
    eval-rel (case f g) {inj₂ _} {inj₁ _} ()
    eval-rel terminal   r = relS-ret tt
    eval-rel initial {()}
    eval-rel (curry f)  r = relS-ret (λ r′ → eval-rel f (r , r′))
    eval-rel apply      r = proj₁ r (proj₂ r)
    eval-rel (In {F} w) r rewrite fo-eq w r = relS-ret refl
    eval-rel (out-μ {F} w) {x} r rewrite r =
      relS-ret (RelD-subst (sym (⌈⟧TI-commute F (II.μ-type F)))
                 (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ II.μ-type F ⌉ (frefl (wf-⌈⌉ w) _)))
      where
        frefl : ∀ {G : Fun _} (wg : (LW.WFFun LW.∅ₖ) G) (l : ⟦ G ⟧F′ ⟦ ⌈ II.μ-type F ⌉ ⟧ᴰ)
              → FRel (RelD ⌈ II.μ-type F ⌉) G l l
        frefl (LW.wf-K b) l = fr-K
        frefl LW.wf-Id l = fr-Id refl
        frefl (LW.wf-⊕ wf wg) (inj₁ l) = fr-inl (frefl wf l)
        frefl (LW.wf-⊕ wf wg) (inj₂ l) = fr-inr (frefl wg l)
        frefl (LW.wf-⊗ wf wg) (l , l′) = fr-pair (frefl wf l) (frefl wg l′)
    eval-rel (Cata {F} w {E₀} {C} alg) {e , x} {e′ , x′} (re′ , refl) =
      sem-cata-rel (wf-⌈⌉ w) (λ fr → alg-step fr) x
      where
        alg-step : ∀ {l₁ l₂} → FRel (RelS (RelD ⌈ C ⌉)) ⌈ F ⌉F l₁ l₂
                 → RelS (RelD ⌈ C ⌉) (cata-ev-algᴰ fmt ρ w alg e l₁) (cata-ev-algᴰ fmt ρ′ w alg e′ l₂)
        alg-step fr =
          RelS-bind (seqF∞-rel ⌈ F ⌉F fr)
            (λ fl → eval-rel alg (re′ , RelD-subst (sym (⌈⟧TI-commute F C)) (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ C ⌉ fl)))
    eval-rel (Out {F} w) {v} {v′} r =
      RelS-fmap (StreamRel.forceR r)
        (λ l → RelD-subst (sym (⌈⟧TI-commute F (II.ν-type F)))
                 (cfD⁻¹-rel (wf-⌈⌉ w) ⌈ II.ν-type F ⌉ (cμout-rel (wf-⌈⌉ w) (layer→srel (translateF Carrier Carrier ⌈ F ⌉F) l))))
    eval-rel (in-ν {F} w) r =
      relS-ret (in-rel (cμin-rel ⌈ F ⌉F (cfD-rel (wf-⌈⌉ w) ⌈ II.ν-type F ⌉ (RelD-subst (⌈⟧TI-commute F (II.ν-type F)) r))))
    eval-rel (Ana {F} w {E₀} {A₀} c) {e , s} {e′ , s′} (re′ , rs) =
      relS-ret (anaᴵ-rel (λ r → RelS-fmap (RelS-fmap (eval-rel c (re′ , r))
                                            (λ q → cfD-rel (wf-⌈⌉ w) ⌈ A₀ ⌉ (RelD-subst (⌈⟧TI-commute F A₀) q)))
                                          (cμin-rel ⌈ F ⌉F))
                         rs)
    -- the loop: related rounds (the same body, related environments) from
    -- related seeds.
    eval-rel (Iter {E₀} {A₀} {B₀} b) {e , s} {e′ , s′} (re′ , rs) =
      RelS-iter∞ {RB = RelD ⌈ B₀ ⌉} {S = RelD ⌈ B₀ II.+ A₀ ⌉}
                 {f = λ a → E b (e , a)} {f′ = λ a → E′ b (e′ , a)}
                 (λ r → r) (λ r → eval-rel b (re′ , r)) (λ ()) (λ ()) rs
    eval-rel (const II.fits-int v)   r = relS-ret refl
    eval-rel (const II.fits-float v) r = relS-ret refl
    eval-rel (SigOp si) r = sigop-rel si r
    eval-rel (Call {A} {B} f) r = proj₁ re f A B r

  -- A table's call environment is related to itself: entry by entry, each body
  -- evaluated in the environment of the entries below it.
  module _ (φ : FFIAnswers) where
    table-self : ∀ (tbl : List IRFun) → RelEnv (tableEnv fmt φ tbl) (tableEnv fmt φ tbl)
    calls-self : ∀ (tbl : List IRFun) f (A B : IRTy) {a a′} → RelD ⌈ A ⌉ a a′
               → RelS (RelD ⌈ B ⌉) (tableCalls fmt φ tbl f A B a) (tableCalls fmt φ tbl f A B a′)
    table-self tbl = calls-self tbl , refl

    calls-self []       f A B r = RelS-embed rel-halt
    calls-self (e ∷ es) f A B r = at (fname e ≟ᶜ f) (fdom e ≟IRTy A) (fcod e ≟IRTy B) r
      where
        hit : ∀ {A B} (p : fdom e ≡ A) (q : fcod e ≡ B) {a a′} → RelD ⌈ A ⌉ a a′
            → RelS (RelD ⌈ B ⌉)
                (subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q (evalᴰ fmt (tableEnv fmt φ es) (fbody e) (subst ⟦_⟧ᴰᴵ (sym p) a)))
                (subst (λ Y → T∞ ⟦ Y ⟧ᴰᴵ) q (evalᴰ fmt (tableEnv fmt φ es) (fbody e) (subst ⟦_⟧ᴰᴵ (sym p) a′)))
        hit refl refl r = eval-rel (table-self es) (fbody e) r
        at : ∀ d₁ d₂ d₃ {a a′} → RelD ⌈ A ⌉ a a′
           → RelS (RelD ⌈ B ⌉) (tableEnv-at fmt φ e es f A B d₁ d₂ d₃ a)
                                (tableEnv-at fmt φ e es f A B d₁ d₂ d₃ a′)
        at (yes _) (yes p) (yes q) r = hit p q r
        at (yes _) (yes _) (no _)  r = calls-self es f A B r
        at (yes _) (no _)  _       r = calls-self es f A B r
        at (no _)  _       _       r = calls-self es f A B r

------------------------------------------------------------------------
-- The relation at `⌈ ⌊ A ⌋ ⌉` is the relation at `A`, across `cohᴰ`.
------------------------------------------------------------------------

private
  srel-subst : ∀ {H H′} (e : H ≡ H′) {x y : νᴵ H} → StreamRel H x y
             → StreamRel H′ (subst idᶠ (cong νᴵ e) x) (subst idᶠ (cong νᴵ e) y)
  srel-subst refl r = r

  srel-subst⁻ : ∀ {H H′} (e : H ≡ H′) {x y : νᴵ H′} → StreamRel H′ x y
              → StreamRel H (subst idᶠ (sym (cong νᴵ e)) x) (subst idᶠ (sym (cong νᴵ e)) y)
  srel-subst⁻ refl r = r

  arr-subst : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (f : X → T∞ Y) (x′ : X′)
            → subst idᶠ (cong₂ (λ U V → U → T∞ V) P Q) f x′ ≡ subst T∞ Q (f (subst idᶠ (sym P) x′))
  arr-subst refl refl f x′ = refl

  arr-subst⁻ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (f : X′ → T∞ Y′) (x : X)
             → subst idᶠ (sym (cong₂ (λ U V → U → T∞ V) P Q)) f x ≡ subst T∞ (sym Q) (f (subst idᶠ P x))
  arr-subst⁻ refl refl f x = refl

  arr₀-subst : ∀ {Y Y′ : Set} (Q : Y ≡ Y′) (f : ⊤ → T∞ Y) (u : ⊤)
             → subst idᶠ (cong (λ V → ⊤ → T∞ V) Q) f u ≡ subst T∞ Q (f u)
  arr₀-subst refl f u = refl

  arr₀-subst⁻ : ∀ {Y Y′ : Set} (Q : Y ≡ Y′) (f : ⊤ → T∞ Y′) (u : ⊤)
              → subst idᶠ (sym (cong (λ V → ⊤ → T∞ V) Q)) f u ≡ subst T∞ (sym Q) (f u)
  arr₀-subst⁻ refl f u = refl

  pair-subst : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X) (y : Y)
             → subst idᶠ (cong₂ _×_ P Q) (x , y) ≡ (subst idᶠ P x , subst idᶠ Q y)
  pair-subst refl refl x y = refl

  pair-subst⁻ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X′) (y : Y′)
              → subst idᶠ (sym (cong₂ _×_ P Q)) (x , y) ≡ (subst idᶠ (sym P) x , subst idᶠ (sym Q) y)
  pair-subst⁻ refl refl x y = refl

  inj₁-subst : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X)
             → subst idᶠ (cong₂ _⊎_ P Q) (inj₁ x) ≡ inj₁ (subst idᶠ P x)
  inj₁-subst refl refl x = refl

  inj₂-subst : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (y : Y)
             → subst idᶠ (cong₂ _⊎_ P Q) (inj₂ y) ≡ inj₂ (subst idᶠ Q y)
  inj₂-subst refl refl y = refl

  inj₁-subst⁻ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X′)
              → subst idᶠ (sym (cong₂ _⊎_ P Q)) (inj₁ x) ≡ inj₁ (subst idᶠ (sym P) x)
  inj₁-subst⁻ refl refl x = refl

  inj₂-subst⁻ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (y : Y′)
              → subst idᶠ (sym (cong₂ _⊎_ P Q)) (inj₂ y) ≡ inj₂ (subst idᶠ (sym Q) y)
  inj₂-subst⁻ refl refl y = refl

  ≡ᴰ : ∀ {m} (A : Ty m) {u u′ w w′ : ⟦ A ⟧ᴰ} → u ≡ u′ → w ≡ w′ → RelD A u′ w′ → RelD A u w
  ≡ᴰ A refl refl r = r

  ≡ˢ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n n′ : T∞ Y} → m ≡ m′ → n ≡ n′ → RelS R m′ n′ → RelS R m n
  ≡ˢ refl refl h = h

  RelS-substʳ : ∀ {X Y Y′} {R : X → Y′ → Set} (E : Y ≡ Y′) {m : T∞ X} {n : T∞ Y}
              → RelS (λ a b → R a (subst idᶠ E b)) m n → RelS R m (subst T∞ E n)
  RelS-substʳ refl h = h

  RelS-subst₂ : ∀ {X X′} {R : X′ → X′ → Set} (E : X ≡ X′) {m n : T∞ X}
              → RelS (λ a b → R (subst idᶠ E a) (subst idᶠ E b)) m n → RelS R (subst T∞ E m) (subst T∞ E n)
  RelS-subst₂ refl h = h

mutual
  RelD-coh : ∀ {m} (A : Ty m) {x y : ⟦ ⌈ ⌊ A ⌋ ⌉ ⟧ᴰ} → RelD ⌈ ⌊ A ⌋ ⌉ x y
           → RelD A (subst idᶠ (cohᴰ A) x) (subst idᶠ (cohᴰ A) y)
  RelD-coh Unit r = r
  RelD-coh Void {()}
  RelD-coh (A * B) {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) =
    ≡ᴰ (A * B) (pair-subst (cohᴰ A) (cohᴰ B) x₁ x₂) (pair-subst (cohᴰ A) (cohᴰ B) y₁ y₂) (RelD-coh A r₁ , RelD-coh B r₂)
  RelD-coh (A + B) {inj₁ x} {inj₁ y} r =
    ≡ᴰ (A + B) (inj₁-subst (cohᴰ A) (cohᴰ B) x) (inj₁-subst (cohᴰ A) (cohᴰ B) y) (RelD-coh A r)
  RelD-coh (A + B) {inj₂ x} {inj₂ y} r =
    ≡ᴰ (A + B) (inj₂-subst (cohᴰ A) (cohᴰ B) x) (inj₂-subst (cohᴰ A) (cohᴰ B) y) (RelD-coh B r)
  RelD-coh (A + B) {inj₁ _} {inj₂ _} ()
  RelD-coh (A + B) {inj₂ _} {inj₁ _} ()
  RelD-coh (A ⇒[ mk-kind Zero π ] B) {f} {g} r =
    ≡ˢ (arr₀-subst (cohᴰ B) f tt) (arr₀-subst (cohᴰ B) g tt) (RelS-subst₂ (cohᴰ B) (RelS-mono (RelD-coh B) (r tt)))
  RelD-coh (A ⇒[ mk-kind One π ] B) {f} {g} r {a} {a′} ra =
    ≡ˢ (arr-subst (cohᴰ A) (cohᴰ B) f a) (arr-subst (cohᴰ A) (cohᴰ B) g a′)
       (RelS-subst₂ (cohᴰ B) (RelS-mono (RelD-coh B) (r (RelD-coh⁻ A ra))))
  RelD-coh (A ⇒[ mk-kind Many π ] B) {f} {g} r {a} {a′} ra =
    ≡ˢ (arr-subst (cohᴰ A) (cohᴰ B) f a) (arr-subst (cohᴰ A) (cohᴰ B) g a′)
       (RelS-subst₂ (cohᴰ B) (RelS-mono (RelD-coh B) (r (RelD-coh⁻ A ra))))
  RelD-coh (μ F) r = cong (subst idᶠ (cohᴰ (μ F))) r
  RelD-coh (ν F π) r = srel-subst _ r
  RelD-coh Int r = r
  RelD-coh Float r = r
  RelD-coh (var _) {()}

  RelD-coh⁻ : ∀ {m} (A : Ty m) {x y : ⟦ A ⟧ᴰ} → RelD A x y
            → RelD ⌈ ⌊ A ⌋ ⌉ (subst idᶠ (sym (cohᴰ A)) x) (subst idᶠ (sym (cohᴰ A)) y)
  RelD-coh⁻ Unit r = r
  RelD-coh⁻ Void {()}
  RelD-coh⁻ (A * B) {x₁ , x₂} {y₁ , y₂} (r₁ , r₂) =
    ≡ᴰ ⌈ ⌊ A * B ⌋ ⌉ (pair-subst⁻ (cohᴰ A) (cohᴰ B) x₁ x₂) (pair-subst⁻ (cohᴰ A) (cohᴰ B) y₁ y₂) (RelD-coh⁻ A r₁ , RelD-coh⁻ B r₂)
  RelD-coh⁻ (A + B) {inj₁ x} {inj₁ y} r =
    ≡ᴰ ⌈ ⌊ A + B ⌋ ⌉ (inj₁-subst⁻ (cohᴰ A) (cohᴰ B) x) (inj₁-subst⁻ (cohᴰ A) (cohᴰ B) y) (RelD-coh⁻ A r)
  RelD-coh⁻ (A + B) {inj₂ x} {inj₂ y} r =
    ≡ᴰ ⌈ ⌊ A + B ⌋ ⌉ (inj₂-subst⁻ (cohᴰ A) (cohᴰ B) x) (inj₂-subst⁻ (cohᴰ A) (cohᴰ B) y) (RelD-coh⁻ B r)
  RelD-coh⁻ (A + B) {inj₁ _} {inj₂ _} ()
  RelD-coh⁻ (A + B) {inj₂ _} {inj₁ _} ()
  RelD-coh⁻ (A ⇒[ mk-kind Zero π ] B) {f} {g} r {u} {u′} _ =
    ≡ˢ (arr₀-subst⁻ (cohᴰ B) f u) (arr₀-subst⁻ (cohᴰ B) g u′) (RelS-subst₂ (sym (cohᴰ B)) (RelS-mono (RelD-coh⁻ B) r))
  RelD-coh⁻ (A ⇒[ mk-kind One π ] B) {f} {g} r {a} {a′} ra =
    ≡ˢ (arr-subst⁻ (cohᴰ A) (cohᴰ B) f a) (arr-subst⁻ (cohᴰ A) (cohᴰ B) g a′)
       (RelS-subst₂ (sym (cohᴰ B)) (RelS-mono (RelD-coh⁻ B) (r (RelD-coh A ra))))
  RelD-coh⁻ (A ⇒[ mk-kind Many π ] B) {f} {g} r {a} {a′} ra =
    ≡ˢ (arr-subst⁻ (cohᴰ A) (cohᴰ B) f a) (arr-subst⁻ (cohᴰ A) (cohᴰ B) g a′)
       (RelS-subst₂ (sym (cohᴰ B)) (RelS-mono (RelD-coh⁻ B) (r (RelD-coh A ra))))
  RelD-coh⁻ (μ F) r = cong (subst idᶠ (sym (cohᴰ (μ F)))) r
  RelD-coh⁻ (ν F π) r = srel-subst⁻ _ r
  RelD-coh⁻ Int r = r
  RelD-coh⁻ Float r = r
  RelD-coh⁻ (var _) {()}

-- The evaluator's fundamental lemma at the source value domain.
liftFn-rel : ∀ {m} (fmt : TargetNum) {ρ ρ′ : CallEnv} → RelEnv fmt ρ ρ′
           → ∀ {A B : Ty m} (ir : IR ⌊ A ⌋ ⌊ B ⌋) {a a′ : ⟦ A ⟧ᴰ} → RelD A a a′
           → RelS (RelD B) (liftFn fmt ρ {A} {B} ir a) (liftFn fmt ρ′ {A} {B} ir a′)
liftFn-rel fmt re {A} {B} ir r = RelS-subst₂ (cohᴰ B) (RelS-mono (RelD-coh B) (eval-rel fmt re ir (RelD-coh⁻ A r)))

-- Runs related at `⌈ ⌊ A ⌋ ⌉`, transported to the source domain, are related at `A`.
coh-runs : ∀ {mₜ} (A : Ty mₜ) {m n : T∞ ⟦ ⌈ ⌊ A ⌋ ⌉ ⟧ᴰ} → RelS (RelD ⌈ ⌊ A ⌋ ⌉) m n
         → RelS (RelD A) (subst T∞ (cohᴰ A) m) (subst T∞ (cohᴰ A) n)
coh-runs A h = RelS-subst₂ (cohᴰ A) (RelS-mono (RelD-coh A) h)
