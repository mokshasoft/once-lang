-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.CoerceFaithful — a compiled conversion means `⟦ p ⟧<:`
-- (plan 0.99, D226).
--
-- `coerce-lift`: the IR `runCoe p` emits, run through the IR semantics and
-- transported to the source value domain, is related (`RelS (RelD B)`) to the
-- source conversion `⟦ p ⟧<:` mapped over any run the operand is related to.
-- Runs are compared step for step, never by `≡` (plan 0.119 D5: a `T∞` run is
-- a coinductive record). Two cases, split on the SAME decision `runCoe` makes:
--
--   * a void-free derivation emits no code (`subst … f`). Its meaning is a
--     transport along some `⟦ A ⟧ᴰ ≡ ⟦ B ⟧ᴰ` (`vf-sem`) that relates a value to
--     its conversion, and the two transports that meet at the end are equal
--     because identity proofs are unique (K).
--   * otherwise `coeIR p ∘ f`, and `coeIR-rel` shows the structural IR returns
--     at once a value related to `⟦ p ⟧<:`, former by former, from
--     `LiftFnReduce`'s lemmas.
------------------------------------------------------------------------

open import Once.Spec.Numerics using (TargetNum)

open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.CoerceFaithful (fmt : TargetNum) (ρ : CallEnv) where

open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; cong-app; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Once.Spec.Grade as Ty using (Zero; One; Many; mk-kind)
open import Once.Spec.Type as Ty using (Type; _⇒[_]_; _*_; _+_; Unit)
open import Once.Internal.Type.Sub
open import Once.Spec.Sub using (_<:_; _<:ᶜ_; _⊔_≔_; sub-void; sub-unit; sub-int; sub-float; sub-arr; sub-μ; sub-ν; subᶜ-void; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Grade using (_⊑π_; ⊑-pure; ⊑-eff; ⊑-pe; ⊑-act; ⊑-pa; ⊑-ae)
open import Once.Type.Sub
open import Once.Internal.Laws.SubLaws
open import Once.IR as IR using (IR; _∘_; ⟨_,_⟩; fst; snd; curry; apply; inl; inr)
open import Once.IRTy using (IRTy; ⌊_⌋)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ)
open import Once.Internal.Iterative using (T∞; return∞; _>>=∞_; fmap∞)
open import Once.Denotation.TraceMonadInfLaws using (RelS; RelS-bind; relS-ret)
open import Once.Denotation.ValueRel using (RelD; RelS-fmapʳ; retargetˡ; retargetʳ; RelS-substˡ)
open import Once.Denotation.DenotTrace using (evalᴰ; liftFn)
open import Once.Denotation.Sub using (⟦_⟧<:)
open import Once.Surface.CoerceIR
open import Once.Adequacy.LiftFnReduce fmt ρ
  using (liftFn-id; liftFn-fst; liftFn-snd; liftFn-inl; liftFn-inr; liftFn-∘; liftFn-pair;
         liftFn-apply; liftFn-curry; liftFn-case-inj₁; liftFn-case-inj₂;
         liftFn-apply₀; liftFn-apply₁; liftFn-curry₀; liftFn-curry₁)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- Small facts.
------------------------------------------------------------------------

-- Restating the IR side along an equation.
≡ˡ : ∀ {X Y} {R : X → Y → Set} {m m′ : T∞ X} {n : T∞ Y} → m ≡ m′ → RelS R m′ n → RelS R m n
≡ˡ refl h = h

subst-T-∘ : ∀ {X Y Z : Set} (P : X ≡ Y) (Q : Y ≡ Z) (m : T∞ X)
          → subst T∞ Q (subst T∞ P m) ≡ subst T∞ (trans P Q) m
subst-T-∘ refl refl m = refl

subst-⟦⟧ : ∀ {X Y : IRTy} (E : X ≡ Y) (m : T∞ ⟦ X ⟧ᴰᴵ)
         → subst (λ W → T∞ ⟦ W ⟧ᴰᴵ) E m ≡ subst T∞ (cong ⟦_⟧ᴰᴵ E) m
subst-⟦⟧ refl m = refl

eval-subst : ∀ {Z X Y : IRTy} (E : X ≡ Y) (f : IR Z X) (v : ⟦ Z ⟧ᴰᴵ)
           → evalᴰ fmt ρ (subst (IR Z) E f) v ≡ subst (λ W → T∞ ⟦ W ⟧ᴰᴵ) E (evalᴰ fmt ρ f v)
eval-subst refl f v = refl

uip : ∀ {X Y : Set} (p q : X ≡ Y) → p ≡ q
uip refl refl = refl

sym-sym : ∀ {X Y : Set} (E : X ≡ Y) → sym (sym E) ≡ E
sym-sym refl = refl

subst-arr : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (f : X → T∞ Y) (x′ : X′)
          → subst id (cong₂ (λ U V → U → T∞ V) P Q) f x′ ≡ subst T∞ Q (f (subst id (sym P) x′))
subst-arr refl refl f x′ = refl

subst-arr₀ : ∀ {Y Y′ : Set} (Q : Y ≡ Y′) (f : ⊤ → T∞ Y) (u : ⊤)
           → subst id (cong (λ V → ⊤ → T∞ V) Q) f u ≡ subst T∞ Q (f u)
subst-arr₀ refl f u = refl

subst-pair : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X) (y : Y)
           → subst id (cong₂ _×_ P Q) (x , y) ≡ (subst id P x , subst id Q y)
subst-pair refl refl x y = refl

subst-inj₁ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (x : X)
           → subst id (cong₂ _⊎_ P Q) (inj₁ x) ≡ inj₁ (subst id P x)
subst-inj₁ refl refl x = refl

subst-inj₂ : ∀ {X X′ Y Y′ : Set} (P : X ≡ X′) (Q : Y ≡ Y′) (y : Y)
           → subst id (cong₂ _⊎_ P Q) (inj₂ y) ≡ inj₂ (subst id Q y)
subst-inj₂ refl refl y = refl

------------------------------------------------------------------------
-- The structural IR returns at once a value related to `⟦ p ⟧<:`.
------------------------------------------------------------------------

-- At a closure, the source side is written as the bind of returns the IR
-- performs; it forces to the same block (`retargetʳ refl`).
mutual
  coeIR-rel : ∀ {A B} (p : A <: B) {v v′ : ⟦ A ⟧ᴰ} → RelD A v v′
            → RelS (RelD B) (liftFn fmt ρ {A} {B} (coeIR p) v) (return∞ (⟦ p ⟧<: v′))
  coeIR-rel sub-void {()}
  coeIR-rel sub-unit  {v} r = ≡ˡ (cong-app (liftFn-id {A = Unit}) v) (relS-ret r)
  coeIR-rel sub-int   {v} r = ≡ˡ (cong-app (liftFn-id {A = Ty.Int}) v) (relS-ret r)
  coeIR-rel sub-float {v} r = ≡ˡ (cong-app (liftFn-id {A = Ty.Float}) v) (relS-ret r)
  coeIR-rel (sub-μ {F}) {v} r = ≡ˡ (cong-app (liftFn-id {A = Ty.μ-type F}) v) (relS-ret r)
  coeIR-rel (sub-ν {F} {π} _) {v} r = ≡ˡ (cong-app (liftFn-id {A = Ty.ν-type F π}) v) (relS-ret r)
  coeIR-rel sub-rigid {()}   -- D243: no value of a rigid parameter
  coeIR-rel (sub-arr {A} {A′} {B} {B′} {Zero} {π} {π′} a b _) {f} r =
    ≡ˡ (cong-app (liftFn-curry₀ {A = A ⇒[ mk-kind Zero π ] B} {B = A′} {C = B′} {π = π′} (coeIR b ∘ apply)) f)
       (relS-ret (arr₀ {A} {A′} {B} {B′} {π} a b r))
  coeIR-rel (sub-arr {A} {A′} {B} {B′} {One} {π} {π′} a b _) {f} r =
    ≡ˡ (cong-app (liftFn-curry₁ {A = A ⇒[ mk-kind One π ] B} {B = A′} {C = B′} {π = π′}
                                (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩))) f)
       (relS-ret (λ rx → arr₁ {A} {A′} {B} {B′} {π} a b r rx))
  coeIR-rel (sub-arr {A} {A′} {B} {B′} {Many} {π} {π′} a b _) {f} r =
    ≡ˡ (cong-app (liftFn-curry {A = A ⇒[ mk-kind Many π ] B} {B = A′} {C = B′} {π = π′}
                               (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩))) f)
       (relS-ret (λ rx → arrω {A} {A′} {B} {B′} {π} a b r rx))
  coeIR-rel (sub-prod {A} {A′} {B} {B′} a b) {x , y} {x′ , y′} (rx , ry) =
    ≡ˡ (cong-app (liftFn-pair {A = A * B} {B = A′} {C = B′} (coeIR a ∘ fst) (coeIR b ∘ snd)) (x , y))
       (retargetʳ {n′ = return∞ (⟦ a ⟧<: x′) >>=∞ λ u → return∞ (⟦ b ⟧<: y′) >>=∞ λ w → return∞ (u , w)} refl
         (RelS-bind (comp-fst {A} {A′} {B} a rx) λ ru → RelS-bind (comp-snd {A} {B} {B′} b ry) λ rw → relS-ret (ru , rw)))
  coeIR-rel (sub-sum {A} {A′} {B} {B′} a b) {inj₁ x} {inj₁ x′} r =
    ≡ˡ (trans (liftFn-case-inj₁ {A = A} {B = B} {C = A′ + B′} (inl ∘ coeIR a) (inr ∘ coeIR b) x)
              (cong-app (liftFn-∘ {B = A′} {C = A′ + B′} {A = A} inl (coeIR a)) x))
       (retargetʳ {n′ = return∞ (⟦ a ⟧<: x′) >>=∞ λ u → return∞ (inj₁ u)} refl
         (RelS-bind (coeIR-rel a r) λ {u} {u′} ru → ≡ˡ (cong-app (liftFn-inl {A = A′} {B = B′}) u) (relS-ret ru)))
  coeIR-rel (sub-sum {A} {A′} {B} {B′} a b) {inj₂ y} {inj₂ y′} r =
    ≡ˡ (trans (liftFn-case-inj₂ {A = A} {B = B} {C = A′ + B′} (inl ∘ coeIR a) (inr ∘ coeIR b) y)
              (cong-app (liftFn-∘ {B = B′} {C = A′ + B′} {A = B} inr (coeIR b)) y))
       (retargetʳ {n′ = return∞ (⟦ b ⟧<: y′) >>=∞ λ u → return∞ (inj₂ u)} refl
         (RelS-bind (coeIR-rel b r) λ {u} {u′} ru → ≡ˡ (cong-app (liftFn-inr {B = B′} {A = A′}) u) (relS-ret ru)))
  coeIR-rel (sub-sum a b) {inj₁ _} {inj₂ _} ()
  coeIR-rel (sub-sum a b) {inj₂ _} {inj₁ _} ()

  -- A component projected, then converted.
  comp-fst : ∀ {A A′ B} (a : A <: A′) {x x′ : ⟦ A ⟧ᴰ} {y : ⟦ B ⟧ᴰ} → RelD A x x′
           → RelS (RelD A′) (liftFn fmt ρ {A * B} {A′} (coeIR a ∘ fst) (x , y)) (return∞ (⟦ a ⟧<: x′))
  comp-fst {A} {A′} {B} a {x} {x′} {y} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {B = A} {C = A′} {A = A * B} (coeIR a) fst) (x , y))
              (cong (_>>=∞ liftFn fmt ρ {A} {A′} (coeIR a)) (cong-app (liftFn-fst {A = A} {B = B}) (x , y))))
       (retargetˡ refl (coeIR-rel a r))

  comp-snd : ∀ {A B B′} (b : B <: B′) {x : ⟦ A ⟧ᴰ} {y y′ : ⟦ B ⟧ᴰ} → RelD B y y′
           → RelS (RelD B′) (liftFn fmt ρ {A * B} {B′} (coeIR b ∘ snd) (x , y)) (return∞ (⟦ b ⟧<: y′))
  comp-snd {A} {B} {B′} b {x} {y} {y′} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {B = B} {C = B′} {A = A * B} (coeIR b) snd) (x , y))
              (cong (_>>=∞ liftFn fmt ρ {B} {B′} (coeIR b)) (cong-app (liftFn-snd {A = A} {B = B}) (x , y))))
       (retargetˡ refl (coeIR-rel b r))

  -- The closure body at each quantity: `apply` the old closure to the argument
  -- converted backwards, then convert the result forwards.
  arr₀ : ∀ {A A′ B B′ π} (a : A′ <: A) (b : B <: B′) {f f′ : ⟦ A ⇒[ mk-kind Zero π ] B ⟧ᴰ}
       → RelD (A ⇒[ mk-kind Zero π ] B) f f′
       → RelS (RelD B′) (liftFn fmt ρ {(A ⇒[ mk-kind Zero π ] B) * Unit} {B′} (coeIR b ∘ apply) (f , tt))
                        (fmap∞ ⟦ b ⟧<: (f′ tt))
  arr₀ {A} {A′} {B} {B′} {π} a b {f} r =
    ≡ˡ (trans (cong-app (liftFn-∘ {B = B} {C = B′} {A = (A ⇒[ mk-kind Zero π ] B) * Unit} (coeIR b) apply) (f , tt))
              (cong (_>>=∞ liftFn fmt ρ {B} {B′} (coeIR b)) (cong-app (liftFn-apply₀ {A = A} {B = B} {π = π}) (f , tt))))
       (RelS-bind r (coeIR-rel b))

  arr₁ : ∀ {A A′ B B′ π} (a : A′ <: A) (b : B <: B′) {f f′ : ⟦ A ⇒[ mk-kind One π ] B ⟧ᴰ}
       → RelD (A ⇒[ mk-kind One π ] B) f f′ → ∀ {x x′ : ⟦ A′ ⟧ᴰ} → RelD A′ x x′
       → RelS (RelD B′) (liftFn fmt ρ {(A ⇒[ mk-kind One π ] B) * A′} {B′}
                               (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)) (f , x))
                        (fmap∞ ⟦ b ⟧<: (f′ (⟦ a ⟧<: x′)))
  arr₁ {A} {A′} {B} {B′} {π} a b {f} {f′} r {x} {x′} rx =
    ≡ˡ (trans (cong-app (liftFn-∘ {B = B} {C = B′} {A = AB * A′} (coeIR b) (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)) (f , x))
              (cong (_>>=∞ liftFn fmt ρ {B} {B′} (coeIR b))
                    (trans (cong-app (liftFn-∘ {B = AB * A} {C = B} {A = AB * A′} apply ⟨ fst , coeIR a ∘ snd ⟩) (f , x))
                           (trans (cong (_>>=∞ liftFn fmt ρ {AB * A} {B} apply)
                                        (cong-app (liftFn-pair {A = AB * A′} {B = AB} {C = A} fst (coeIR a ∘ snd)) (f , x)))
                                  (cong (λ h → (liftFn fmt ρ {AB * A′} {AB} fst (f , x) >>=∞ λ u → liftFn fmt ρ {AB * A′} {A} (coeIR a ∘ snd) (f , x) >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                                        (liftFn-apply₁ {A = A} {B = B} {π = π}))))))
       (RelS-bind (retargetʳ {n′ = return∞ (f′ , ⟦ a ⟧<: x′) >>=∞ (λ v → proj₁ v (proj₂ v))} refl
                    (RelS-bind {R = RelD (AB * A)} (retargetʳ {n′ = return∞ f′ >>=∞ λ u → return∞ (⟦ a ⟧<: x′) >>=∞ λ w → return∞ (u , w)} refl
                                 (RelS-bind {R = RelD AB}
                                   (≡ˡ (cong-app (liftFn-fst {A = AB} {B = A′}) (f , x)) (relS-ret r))
                                   (λ ru → RelS-bind (comp-snd {AB} {A′} {A} a {f} rx) (λ rw → relS-ret (ru , rw)))))
                               (λ { {u , w} {u′ , w′} (ru , rw) → ru rw })))
                  (coeIR-rel b))
    where AB = A ⇒[ mk-kind One π ] B

  arrω : ∀ {A A′ B B′ π} (a : A′ <: A) (b : B <: B′) {f f′ : ⟦ A ⇒[ mk-kind Many π ] B ⟧ᴰ}
       → RelD (A ⇒[ mk-kind Many π ] B) f f′ → ∀ {x x′ : ⟦ A′ ⟧ᴰ} → RelD A′ x x′
       → RelS (RelD B′) (liftFn fmt ρ {(A ⇒[ mk-kind Many π ] B) * A′} {B′}
                               (coeIR b ∘ (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)) (f , x))
                        (fmap∞ ⟦ b ⟧<: (f′ (⟦ a ⟧<: x′)))
  arrω {A} {A′} {B} {B′} {π} a b {f} {f′} r {x} {x′} rx =
    ≡ˡ (trans (cong-app (liftFn-∘ {B = B} {C = B′} {A = AB * A′} (coeIR b) (apply ∘ ⟨ fst , coeIR a ∘ snd ⟩)) (f , x))
              (cong (_>>=∞ liftFn fmt ρ {B} {B′} (coeIR b))
                    (trans (cong-app (liftFn-∘ {B = AB * A} {C = B} {A = AB * A′} apply ⟨ fst , coeIR a ∘ snd ⟩) (f , x))
                           (trans (cong (_>>=∞ liftFn fmt ρ {AB * A} {B} apply)
                                        (cong-app (liftFn-pair {A = AB * A′} {B = AB} {C = A} fst (coeIR a ∘ snd)) (f , x)))
                                  (cong (λ h → (liftFn fmt ρ {AB * A′} {AB} fst (f , x) >>=∞ λ u → liftFn fmt ρ {AB * A′} {A} (coeIR a ∘ snd) (f , x) >>=∞ λ w → return∞ (u , w)) >>=∞ h)
                                        (liftFn-apply {A = A} {B = B} {π = π}))))))
       (RelS-bind (retargetʳ {n′ = return∞ (f′ , ⟦ a ⟧<: x′) >>=∞ (λ v → proj₁ v (proj₂ v))} refl
                    (RelS-bind {R = RelD (AB * A)} (retargetʳ {n′ = return∞ f′ >>=∞ λ u → return∞ (⟦ a ⟧<: x′) >>=∞ λ w → return∞ (u , w)} refl
                                 (RelS-bind {R = RelD AB}
                                   (≡ˡ (cong-app (liftFn-fst {A = AB} {B = A′}) (f , x)) (relS-ret r))
                                   (λ ru → RelS-bind (comp-snd {AB} {A′} {A} a {f} rx) (λ rw → relS-ret (ru , rw)))))
                               (λ { {u , w} {u′ , w′} (ru , rw) → ru rw })))
                  (coeIR-rel b))
    where AB = A ⇒[ mk-kind Many π ] B

------------------------------------------------------------------------
-- A void-free conversion is a transport, and a transported value is related
-- to its conversion.
------------------------------------------------------------------------

record VfSem {A B : Type} (p : A <: B) : Set₁ where
  field
    D  : ⟦ A ⟧ᴰ ≡ ⟦ B ⟧ᴰ
    pt : ∀ {v v′} → RelD A v v′ → RelD B (subst id D v) (⟦ p ⟧<: v′)
open VfSem

private
  ≡ʳᴰ : ∀ B {u u′ w : ⟦ B ⟧ᴰ} → u ≡ u′ → RelD B u′ w → RelD B u w
  ≡ʳᴰ B refl r = r

  vf-arr₁ : ∀ {A A′ B B′} (a : A′ <: A) (b : B <: B′) (sa : VfSem a) (sb : VfSem b) {f f′ : ⟦ A ⟧ᴰ → T∞ ⟦ B ⟧ᴰ}
    → (∀ {x x′} → RelD A x x′ → RelS (RelD B) (f x) (f′ x′))
    → ∀ {x x′} → RelD A′ x x′
    → RelS (RelD B′) (subst id (cong₂ (λ U V → U → T∞ V) (sym (D sa)) (D sb)) f x) (fmap∞ ⟦ b ⟧<: (f′ (⟦ a ⟧<: x′)))
  vf-arr₁ a b sa sb {f} r {x} rx =
    ≡ˡ (trans (subst-arr (sym (D sa)) (D sb) f x) (cong (λ E → subst T∞ (D sb) (f (subst id E x))) (sym-sym (D sa))))
       (RelS-substˡ (D sb) (RelS-fmapʳ (r (pt sa rx)) (pt sb)))

vf-sem : ∀ {A B} (p : A <: B) → VoidFree p → VfSem p
vf-sem _ vf-void   = record { D = refl ; pt = λ { {()} } }
vf-sem _ vf-unit   = record { D = refl ; pt = λ r → r }
vf-sem _ vf-int    = record { D = refl ; pt = λ r → r }
vf-sem _ vf-float  = record { D = refl ; pt = λ r → r }
vf-sem _ vf-μ      = record { D = refl ; pt = λ r → r }
vf-sem _ vf-ν      = record { D = refl ; pt = λ r → r }
vf-sem _ vf-rigid  = record { D = refl ; pt = λ { {()} } }
vf-sem (sub-arr {q = Zero} a b _) (vf-arr va vb) =
  let sb = vf-sem b vb in
  record { D  = cong (λ V → ⊤ → T∞ V) (D sb)
         ; pt = λ {f} r → ≡ˡ (subst-arr₀ (D sb) f tt) (RelS-substˡ (D sb) (RelS-fmapʳ r (pt sb))) }
vf-sem (sub-arr {q = One} a b _) (vf-arr va vb) =
  record { D  = cong₂ (λ U V → U → T∞ V) (sym (D (vf-sem a va))) (D (vf-sem b vb))
         ; pt = λ r rx → vf-arr₁ a b (vf-sem a va) (vf-sem b vb) r rx }
vf-sem (sub-arr {q = Many} a b _) (vf-arr va vb) =
  record { D  = cong₂ (λ U V → U → T∞ V) (sym (D (vf-sem a va))) (D (vf-sem b vb))
         ; pt = λ r rx → vf-arr₁ a b (vf-sem a va) (vf-sem b vb) r rx }
vf-sem (sub-prod {A′ = A′} {B′ = B′} a b) (vf-prod va vb) =
  let sa = vf-sem a va ; sb = vf-sem b vb in
  record { D  = cong₂ _×_ (D sa) (D sb)
         ; pt = λ { {x , y} {x′ , y′} (rx , ry) →
                    ≡ʳᴰ (A′ * B′) (subst-pair (D sa) (D sb) x y) (pt sa rx , pt sb ry) } }
vf-sem (sub-sum {A′ = A′} {B′ = B′} a b) (vf-sum va vb) =
  let sa = vf-sem a va ; sb = vf-sem b vb in
  record { D  = cong₂ _⊎_ (D sa) (D sb)
         ; pt = λ { {inj₁ x} {inj₁ x′} r → ≡ʳᴰ (A′ + B′) (subst-inj₁ (D sa) (D sb) x) (pt sa r)
                  ; {inj₂ y} {inj₂ y′} r → ≡ʳᴰ (A′ + B′) (subst-inj₂ (D sa) (D sb) y) (pt sb r)
                  ; {inj₁ _} {inj₂ _} ()
                  ; {inj₂ _} {inj₁ _} () } }

coerce-lift-yes : ∀ {Δ A B} (p : A <: B) (vf : VoidFree p) (f : IR ⌊ Δ ⌋ ⌊ A ⌋) (x : ⟦ Δ ⟧ᴰ) {n : T∞ ⟦ A ⟧ᴰ}
  → RelS (RelD A) (liftFn fmt ρ {Δ} {A} f x) n
  → RelS (RelD B) (liftFn fmt ρ {Δ} {B} (subst (IR ⌊ Δ ⌋) (erase-eq p vf) f) x) (fmap∞ ⟦ p ⟧<: n)
coerce-lift-yes {Δ} {A} {B} p vf f x h =
  ≡ˡ (trans (cong (subst T∞ (cohᴰ B)) (eval-subst E f x₀))
       (trans (cong (subst T∞ (cohᴰ B)) (subst-⟦⟧ E m))
         (trans (subst-T-∘ (cong ⟦_⟧ᴰᴵ E) (cohᴰ B) m)
           (trans (cong (λ Q → subst T∞ Q m) (uip (trans (cong ⟦_⟧ᴰᴵ E) (cohᴰ B)) (trans (cohᴰ A) (D s))))
                  (sym (subst-T-∘ (cohᴰ A) (D s) m))))))
     (RelS-substˡ (D s) (RelS-fmapʳ h (pt s)))
  where
    E  = erase-eq p vf
    s  = vf-sem p vf
    x₀ = subst id (sym (cohᴰ Δ)) x
    m  = evalᴰ fmt ρ f x₀

------------------------------------------------------------------------
-- The theorem.
------------------------------------------------------------------------

coerce-lift-dec : ∀ {Δ A B} (p : A <: B) (dv : Dec (VoidFree p)) (f : IR ⌊ Δ ⌋ ⌊ A ⌋) (x : ⟦ Δ ⟧ᴰ) {n : T∞ ⟦ A ⟧ᴰ}
  → RelS (RelD A) (liftFn fmt ρ {Δ} {A} f x) n
  → RelS (RelD B) (liftFn fmt ρ {Δ} {B} (runCoe-dec p dv f) x) (fmap∞ ⟦ p ⟧<: n)
coerce-lift-dec {Δ} p (yes vf) f x h = coerce-lift-yes {Δ} p vf f x h
coerce-lift-dec {Δ} {A} {B} p (no _) f x h =
  ≡ˡ (cong-app (liftFn-∘ {B = A} {C = B} {A = Δ} (coeIR p) f) x) (RelS-bind h (coeIR-rel p))

coerce-lift : ∀ {Δ A B} (p : A <: B) (f : IR ⌊ Δ ⌋ ⌊ A ⌋) (x : ⟦ Δ ⟧ᴰ) {n : T∞ ⟦ A ⟧ᴰ}
  → RelS (RelD A) (liftFn fmt ρ {Δ} {A} f x) n
  → RelS (RelD B) (liftFn fmt ρ {Δ} {B} (runCoe p f) x) (fmap∞ ⟦ p ⟧<: n)
coerce-lift {Δ} p f x = coerce-lift-dec {Δ} p (voidFree? p) f x
