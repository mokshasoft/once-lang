-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.AnaErased
--
-- Plan 0.52 M2: the FUNCTOR-TRANSPORT lemma isolating the erasure round-trip
-- for the `Ana` recursion scheme — the coinductive dual of `CataErased`. After
-- M2 the IR's `Ana` unfolds the ERASED functor `⌈eraseF F⌉F` (`evalᴰ (Ana …)`
-- calls `sem-ana ⌈eraseF F⌉F`), while the surface/meaning value runs `sem-ana F`
-- at `F`. On the ν CODATA `inject`/`forget` are the identity, so the values must
-- genuinely coincide — a coinductive obligation.
--
-- The single export `sem-ana-erase-coh′` bridges the two via the SFunctor level,
-- where `tF-coh : translateF ⌈eraseF F⌉F ≡ translateF F` lives. The coinduction is
-- confined to ONE same-functor bisimulation `sem-ana-anaS` (mirroring the existing
-- `sem-ana-Out-bisim` template): `sem-ana` factors through the νS-level `anaS`.
-- The cross-functor transport `anaS-subst-nat` is then a cheap match-to-refl.
-- Uses the codebase's accepted `bisimS-to-eq` axiom (as `sem-ana-Out-id` does).
------------------------------------------------------------------------

open import Once.Target.Arch using (TargetNum; int-bits; float-format)

-- Plan 0.73 (D113): this module's statements mention a denotation that is
-- target-relative at `Float`, so the format is a parameter. A MODULE parameter
-- rather than a per-lemma argument because everything here is a PROOF —
-- downstream uses these as facts and never reduces them — so the "recursive
-- function in a parameterised module stops reducing" trap does not apply. The
-- denotations themselves take it as an explicit argument.
open import Once.Denotation.DenotTrace using (CallEnv)
module Once.Adequacy.AnaErased (fmt : TargetNum) (ρ : CallEnv) where

open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _++_; length)
open import Data.Nat using (ℕ; zero; _∸_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; subst-subst-sym; subst-sym-subst)

open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Type as TT
  using (Functor; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Functor.Translate using (translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F; ⌈⟧TI-commute; ⌊⟧T-commute)
import Once.IRTy as II
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; νS; anaS; sfmapAna; anaLayerS)
open Once.Semantics.Functor.νS using (unfoldS)
open import Once.Semantics.Functor.Laws
  using (_∼S_; ⟦_⟧SF-rel; bisimS-to-eq)
open Once.Semantics.Functor.Laws._∼S_ using (unfoldS-∼)
open import Once.Semantics.Machine
  using (⟦_⟧F; ⟦_⟧; sem-ana; sfmapSemAna; semAnaLayer; coerce-ν-in; coerce-functor; coh; tF-coh;
         coerce-full-to-base; base-coh)
open import Once.IRTy using (⌊_⌋; ⌈_⌉)
open import Once.Res using (Res; stopped; returns; mapRes; mapRes-id; mapRes-∘; mapRes-cong; Res-rel; rel-stopped; rel-returns)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.Denotation.TraceMonad using (T; returnT)
open import Once.Denotation.ValueDomain
  using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; cohᴰ; νᵈ; forgetᵇ; coerce-functor-D)
open import Once.Functor.Translate using (WellFormedF; wf-K; wf-Id; wf-Sum; wf-Prod;
  IsBaseType; base-Unit; base-Void; base-Int; base-Float; base-Prod; base-Sum; base-rigid)
open import Once.IRTy.WF using (wf-⌊⌋; wf-⌈⌉; base-⌊⌋; base-⌈⌉)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- `sem-ana` factors through the νS-level `anaS`: unfolding the raw functor
-- coalgebra `A → ⟦F⟧F A` equals unfolding its coerced SFunctor form
-- `A → ⟦translateF F⟧SF A`. SAME functor `F` on both sides — a clean
-- bisimulation mirroring `sem-ana-Out-bisim`/`sem-ana-Out-rel`.
------------------------------------------------------------------------

-- plan 0.98: the coalgebra is `Res`-valued — an unfold need not produce a
-- layer — so the bisimulation's layer field is `Res-rel` and the step splits
-- on the result. `anaLayer-rel` is that split, and it is mutual with the rest
-- for the same reason `anaLayerS` is: a partial application handed to a
-- higher-order function is opaque to the guardedness checker.
mutual
  sem-ana-anaS-bisim : ∀ {F : Functor} {A : Set} (coalg : A → Res (⟦ F ⟧F A)) (a : A)
    → sem-ana F coalg a
      ∼S anaS {translateF Carrier Carrier F} (λ x → mapRes (coerce-ν-in F A) (coalg x)) a
  unfoldS-∼ (sem-ana-anaS-bisim {F} {A} coalg a) =
    anaLayer-rel {F} {A} coalg (coalg a)

  anaLayer-rel : ∀ {F : Functor} {A : Set} (coalg : A → Res (⟦ F ⟧F A))
                   (r : Res (⟦ F ⟧F A))
    → Res-rel (⟦ translateF Carrier Carrier F ⟧SF-rel
                 (_∼S_ {translateF Carrier Carrier F}))
        (semAnaLayer F A coalg r)
        (anaLayerS {translateF Carrier Carrier F} (translateF Carrier Carrier F)
                   (λ y → mapRes (coerce-ν-in F A) (coalg y))
                   (mapRes (coerce-ν-in F A) r))
  anaLayer-rel coalg stopped     = rel-stopped
  anaLayer-rel {F} {A} coalg (returns l) =
    rel-returns (sem-ana-anaS-rel coalg (translateF Carrier Carrier F) (coerce-ν-in F A l))

  sem-ana-anaS-rel : ∀ {F : Functor} {A : Set} (coalg : A → Res (⟦ F ⟧F A))
                       (H : SFunctor) (x : ⟦ H ⟧SF A)
    → ⟦ H ⟧SF-rel (_∼S_ {translateF Carrier Carrier F})
        (sfmapSemAna F H coalg x)
        (sfmapAna {translateF Carrier Carrier F} H
                  (λ y → mapRes (coerce-ν-in F A) (coalg y)) x)
  sem-ana-anaS-rel coalg (SK _)      x        = refl
  sem-ana-anaS-rel coalg SId         x        = sem-ana-anaS-bisim coalg x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₁ x) = sem-ana-anaS-rel coalg H₁ x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₂ y) = sem-ana-anaS-rel coalg H₂ y
  sem-ana-anaS-rel coalg (H₁ S⊗ H₂) (x , y)  =
    sem-ana-anaS-rel coalg H₁ x , sem-ana-anaS-rel coalg H₂ y

push× : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A) (b : B)
  → subst id (cong₂ _×_ p q) (a , b) ≡ (subst id p a , subst id q b)
push× refl refl a b = refl

push×⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A') (b : B')
  → subst id (sym (cong₂ _×_ p q)) (a , b) ≡ (subst id (sym p) a , subst id (sym q) b)
push×⁻ refl refl a b = refl

push⊎₁ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A)
  → subst id (cong₂ _⊎_ p q) (inj₁ a) ≡ inj₁ (subst id p a)
push⊎₁ refl refl a = refl

push⊎₁⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (a : A')
  → subst id (sym (cong₂ _⊎_ p q)) (inj₁ a) ≡ inj₁ (subst id (sym p) a)
push⊎₁⁻ refl refl a = refl

push⊎₂ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B)
  → subst id (cong₂ _⊎_ p q) (inj₂ b) ≡ inj₂ (subst id q b)
push⊎₂ refl refl b = refl

push⊎₂⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (b : B')
  → subst id (sym (cong₂ _⊎_ p q)) (inj₂ b) ≡ inj₂ (subst id (sym q) b)
push⊎₂⁻ refl refl b = refl

subst-T-returnT : ∀ {X Y : Set} (eq : X ≡ Y) (x : X)
  → subst T eq (returnT x) ≡ returnT (subst id eq x)
subst-T-returnT refl x = refl

-- plan 0.98: the `resT-lift` twin. `inject` at an arrow lifts a `Res` rather
-- than returning a value, so this is what the arrow clauses transport with.

pushᴵ+₁ : ∀ {X Y X' Y' : II.IRTy} (p : X ≡ X') (q : Y ≡ Y') (a : ⟦ X ⟧ᴰᴵ)
  → subst id (cong ⟦_⟧ᴰᴵ (cong₂ II._+_ p q)) (inj₁ a) ≡ inj₁ (subst id (cong ⟦_⟧ᴰᴵ p) a)
pushᴵ+₁ refl refl a = refl

pushᴵ+₂ : ∀ {X Y X' Y' : II.IRTy} (p : X ≡ X') (q : Y ≡ Y') (b : ⟦ Y ⟧ᴰᴵ)
  → subst id (cong ⟦_⟧ᴰᴵ (cong₂ II._+_ p q)) (inj₂ b) ≡ inj₂ (subst id (cong ⟦_⟧ᴰᴵ q) b)
pushᴵ+₂ refl refl b = refl

pushᴵ* : ∀ {X Y X' Y' : II.IRTy} (p : X ≡ X') (q : Y ≡ Y') (a : ⟦ X ⟧ᴰᴵ) (b : ⟦ Y ⟧ᴰᴵ)
  → subst id (cong ⟦_⟧ᴰᴵ (cong₂ II._*_ p q)) (a , b)
    ≡ (subst id (cong ⟦_⟧ᴰᴵ p) a , subst id (cong ⟦_⟧ᴰᴵ q) b)
pushᴵ* refl refl a b = refl

-- push `subst ⟦_⟧ (cong₂ _+_/_*_ …)` (value semantics) through inj/pair
pushⱽ+₁ : ∀ {X Y X' Y' : TT.Type} (p : X ≡ X') (q : Y ≡ Y') (w : ⟦ X ⟧)
  → subst ⟦_⟧ (cong₂ TT._+_ p q) (inj₁ w) ≡ inj₁ (subst ⟦_⟧ p w)
pushⱽ+₁ refl refl w = refl

pushⱽ+₂ : ∀ {X Y X' Y' : TT.Type} (p : X ≡ X') (q : Y ≡ Y') (w : ⟦ Y ⟧)
  → subst ⟦_⟧ (cong₂ TT._+_ p q) (inj₂ w) ≡ inj₂ (subst ⟦_⟧ q w)
pushⱽ+₂ refl refl w = refl

pushⱽ* : ∀ {X Y X' Y' : TT.Type} (p : X ≡ X') (q : Y ≡ Y') (u : ⟦ X ⟧) (w : ⟦ Y ⟧)
  → subst ⟦_⟧ (cong₂ TT._*_ p q) (u , w) ≡ (subst ⟦_⟧ p u , subst ⟦_⟧ q w)
pushⱽ* refl refl u w = refl

pushSK : ∀ {X : Set} {b₁ b₂ : Set} (eq : b₁ ≡ b₂) (v : b₁)
  → subst (λ H → ⟦ H ⟧SF X) (cong SK eq) v ≡ subst id eq v
pushSK refl v = refl

-- carrier-align is the identity at a K-leaf (⟦K B'⟧F is carrier-blind)
subst-KF-const : ∀ {B' : TT.Type} {X Y : Set} (eq : X ≡ Y) (v : ⟦ TT.K B' ⟧F X)
  → subst (λ Z → ⟦ TT.K B' ⟧F Z) eq v ≡ v
subst-KF-const refl v = refl

-- the erased-side layer value (from `v0`), factored out for readability
push-⊎fam₁ : ∀ {W : Set₁} (P Q : W → Set) {w w' : W} (eq : w ≡ w') (z : P w)
  → subst (λ Z → P Z ⊎ Q Z) eq (inj₁ z) ≡ inj₁ (subst P eq z)
push-⊎fam₁ P Q refl z = refl

push-⊎fam₂ : ∀ {W : Set₁} (P Q : W → Set) {w w' : W} (eq : w ≡ w') (z : Q w)
  → subst (λ Z → P Z ⊎ Q Z) eq (inj₂ z) ≡ inj₂ (subst Q eq z)
push-⊎fam₂ P Q refl z = refl

push-×fam : ∀ {W : Set₁} (P Q : W → Set) {w w' : W} (eq : w ≡ w') (a : P w) (b : Q w)
  → subst (λ Z → P Z × Q Z) eq (a , b) ≡ (subst P eq a , subst Q eq b)
push-×fam P Q refl a b = refl

pushS⊕₁ : ∀ {X : Set} {H₁ H₂ H₁' H₂' : SFunctor} (p : H₁ ≡ H₁') (q : H₂ ≡ H₂') (w : ⟦ H₁ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (cong₂ _S⊕_ p q) (inj₁ w) ≡ inj₁ (subst (λ H → ⟦ H ⟧SF X) p w)
pushS⊕₁ refl refl w = refl

pushS⊕₂ : ∀ {X : Set} {H₁ H₂ H₁' H₂' : SFunctor} (p : H₁ ≡ H₁') (q : H₂ ≡ H₂') (w : ⟦ H₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (cong₂ _S⊕_ p q) (inj₂ w) ≡ inj₂ (subst (λ H → ⟦ H ⟧SF X) q w)
pushS⊕₂ refl refl w = refl

pushS⊗ : ∀ {X : Set} {H₁ H₂ H₁' H₂' : SFunctor} (p : H₁ ≡ H₁') (q : H₂ ≡ H₂') (a : ⟦ H₁ ⟧SF X) (b : ⟦ H₂ ⟧SF X)
  → subst (λ H → ⟦ H ⟧SF X) (cong₂ _S⊗_ p q) (a , b)
    ≡ (subst (λ H → ⟦ H ⟧SF X) p a , subst (λ H → ⟦ H ⟧SF X) q b)
pushS⊗ refl refl a b = refl

-- surface-side layer value splits (mirror `ve-split`)
VE0ᴰ : ∀ (G : Functor) (A : TT.Type) (v0 : ⟦ ⌊ TT.⟦ G ⟧T A ⌋ ⟧ᴰᴵ)
     → ⟦ TT.⟦ ⌈ eraseF G ⌉F ⟧T ⌈ ⌊ A ⌋ ⌉ ⟧ᴰ
VE0ᴰ G A v0 = subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF G) ⌊ A ⌋)
                    (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G A)) v0)

-- ᴰ-carrier push lemmas (the `⟦_⟧ᴰ` mirrors of `pushⱽ*`).
pushᴰ+₁ : ∀ {X Y X' Y' : TT.Type} (p : X ≡ X') (q : Y ≡ Y') (w : ⟦ X ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ TT._+_ p q) (inj₁ w) ≡ inj₁ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p w)
pushᴰ+₁ refl refl w = refl

pushᴰ+₂ : ∀ {X Y X' Y' : TT.Type} (p : X ≡ X') (q : Y ≡ Y') (w : ⟦ Y ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ TT._+_ p q) (inj₂ w) ≡ inj₂ (subst (λ Ty → ⟦ Ty ⟧ᴰ) q w)
pushᴰ+₂ refl refl w = refl

pushᴰ* : ∀ {X Y X' Y' : TT.Type} (p : X ≡ X') (q : Y ≡ Y') (u : ⟦ X ⟧ᴰ) (w : ⟦ Y ⟧ᴰ)
  → subst (λ Ty → ⟦ Ty ⟧ᴰ) (cong₂ TT._*_ p q) (u , w)
    ≡ (subst (λ Ty → ⟦ Ty ⟧ᴰ) p u , subst (λ Ty → ⟦ Ty ⟧ᴰ) q w)
pushᴰ* refl refl u w = refl

-- `VE0ᴰ` distributes over the constructors. The Val-level `ve-split*` had to
-- commute a `forget` past both transports as well; here there is none.
ve-split⊕₁ᴰ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (x0 : ⟦ ⌊ TT.⟦ G₁ ⟧T A ⌋ ⟧ᴰᴵ)
  → VE0ᴰ (G₁ TT.⊕ G₂) A (inj₁ x0) ≡ inj₁ (VE0ᴰ G₁ A x0)
ve-split⊕₁ᴰ G₁ G₂ A x0 =
  trans (cong (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF (G₁ TT.⊕ G₂)) ⌊ A ⌋))
              (pushᴵ+₁ (⌊⟧T-commute G₁ A) (⌊⟧T-commute G₂ A) x0))
        (pushᴰ+₁ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
                 (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₁ A)) x0))

ve-split⊕₂ᴰ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (y0 : ⟦ ⌊ TT.⟦ G₂ ⟧T A ⌋ ⟧ᴰᴵ)
  → VE0ᴰ (G₁ TT.⊕ G₂) A (inj₂ y0) ≡ inj₂ (VE0ᴰ G₂ A y0)
ve-split⊕₂ᴰ G₁ G₂ A y0 =
  trans (cong (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF (G₁ TT.⊕ G₂)) ⌊ A ⌋))
              (pushᴵ+₂ (⌊⟧T-commute G₁ A) (⌊⟧T-commute G₂ A) y0))
        (pushᴰ+₂ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
                 (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₂ A)) y0))

ve-split⊗ᴰ : ∀ (G₁ G₂ : Functor) (A : TT.Type)
               (x0 : ⟦ ⌊ TT.⟦ G₁ ⟧T A ⌋ ⟧ᴰᴵ) (y0 : ⟦ ⌊ TT.⟦ G₂ ⟧T A ⌋ ⟧ᴰᴵ)
  → VE0ᴰ (G₁ TT.⊗ G₂) A (x0 , y0) ≡ (VE0ᴰ G₁ A x0 , VE0ᴰ G₂ A y0)
ve-split⊗ᴰ G₁ G₂ A x0 y0 =
  trans (cong (subst (λ Ty → ⟦ Ty ⟧ᴰ) (⌈⟧TI-commute (eraseF (G₁ TT.⊗ G₂)) ⌊ A ⌋))
              (pushᴵ* (⌊⟧T-commute G₁ A) (⌊⟧T-commute G₂ A) x0 y0))
        (pushᴰ* (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
                (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₁ A)) x0)
                (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₂ A)) y0))

private
  infixr 5 _⟫_
  _⟫_ : ∀ {X : Set} {a b c : X} → a ≡ b → b ≡ c → a ≡ c
  _⟫_ = trans

-- At a base leaf the two coercions are `forgetᵇ` at the erased and at the
-- surface witness; `base-coh` and `cohᴰ` transport between them.
base-in-D : ∀ {B : TT.Type} (b : IsBaseType B) (v0 : ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
  → subst id (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forgetᵇ (base-⌈⌉ (base-⌊⌋ b)) v0))
    ≡ coerce-full-to-base B (forgetᵇ b (subst id (cohᴰ B) v0))
base-in-D base-Unit   v0 = refl
base-in-D base-Int    v0 = refl
base-in-D base-Float  v0 = refl
base-in-D base-Void   ()
base-in-D base-rigid  v0 = refl
base-in-D (base-Prod {A} {B} ba bb) (a , b) =
  trans (push× (base-coh A) (base-coh B)
               (coerce-full-to-base ⌈ ⌊ A ⌋ ⌉ (forgetᵇ (base-⌈⌉ (base-⌊⌋ ba)) a))
               (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forgetᵇ (base-⌈⌉ (base-⌊⌋ bb)) b)))
    (trans (cong₂ _,_ (base-in-D ba a) (base-in-D bb b))
           (sym (cong (λ z → coerce-full-to-base (A * B) (forgetᵇ (base-Prod ba bb) z)) (push× (cohᴰ A) (cohᴰ B) a b))))
base-in-D (base-Sum {A} {B} ba bb) (inj₁ a) =
  trans (push⊎₁ (base-coh A) (base-coh B) (coerce-full-to-base ⌈ ⌊ A ⌋ ⌉ (forgetᵇ (base-⌈⌉ (base-⌊⌋ ba)) a)))
    (trans (cong inj₁ (base-in-D ba a))
           (sym (cong (λ z → coerce-full-to-base (A + B) (forgetᵇ (base-Sum ba bb) z)) (push⊎₁ (cohᴰ A) (cohᴰ B) a))))
base-in-D (base-Sum {A} {B} ba bb) (inj₂ b) =
  trans (push⊎₂ (base-coh A) (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forgetᵇ (base-⌈⌉ (base-⌊⌋ bb)) b)))
    (trans (cong inj₂ (base-in-D bb b))
           (sym (cong (λ z → coerce-full-to-base (A + B) (forgetᵇ (base-Sum ba bb) z)) (push⊎₂ (cohᴰ A) (cohᴰ B) b))))

-- The erased and the surface ν introduction agree on a layer: structural on
-- the functor's well-formedness (plan 0.105: the coercion forgets only at a
-- base leaf, and only first-order values cross).
coerce-νin-erase-D : ∀ {G : Functor} (wf : WellFormedF G) (A : TT.Type) (v0 : ⟦ ⌊ TT.⟦ G ⟧T A ⌋ ⟧ᴰᴵ)
  → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh G)
       (coerce-ν-in ⌈ eraseF G ⌉F ⟦ A ⟧ᴰ
         (subst (λ Z → ⟦ ⌈ eraseF G ⌉F ⟧F Z) (cohᴰ A)
           (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ wf)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G A v0))))
    ≡ coerce-ν-in G ⟦ A ⟧ᴰ
        (coerce-functor-D wf A (subst id (cohᴰ (TT.⟦ G ⟧T A)) v0))
coerce-νin-erase-D {TT.K B} (wf-K b) A v0 =
    cong (subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (TT.K B)))
         (cong (coerce-ν-in ⌈ eraseF (TT.K B) ⌉F ⟦ A ⟧ᴰ)
               (subst-KF-const (cohᴰ A) (forgetᵇ (base-⌈⌉ (base-⌊⌋ b)) v0)))
  ⟫ pushSK (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forgetᵇ (base-⌈⌉ (base-⌊⌋ b)) v0))
  ⟫ base-in-D b v0
coerce-νin-erase-D wf-Id A v0 = refl
coerce-νin-erase-D {G₁ TT.⊕ G₂} (wf-Sum w₁ w₂) A (inj₁ x0) =
    cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ
             (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟧F Z) (cohᴰ A)
               (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ (wf-Sum w₁ w₂))) ⌈ ⌊ A ⌋ ⌉ z))))
         (ve-split⊕₁ᴰ G₁ G₂ A x0)
  ⟫ cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ z))
         (push-⊎fam₁ (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
                     (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₁)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0)))
  ⟫ pushS⊕₁ (tF-coh G₁) (tF-coh G₂)
      (coerce-ν-in ⌈ eraseF G₁ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₁)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0))))
  ⟫ cong inj₁ (coerce-νin-erase-D w₁ A x0)
  ⟫ sym (cong (λ z → coerce-ν-in (G₁ TT.⊕ G₂) ⟦ A ⟧ᴰ (coerce-functor-D (wf-Sum w₁ w₂) A z))
              (push⊎₁ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0))
coerce-νin-erase-D {G₁ TT.⊕ G₂} (wf-Sum w₁ w₂) A (inj₂ y0) =
    cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ
             (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟧F Z) (cohᴰ A)
               (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ (wf-Sum w₁ w₂))) ⌈ ⌊ A ⌋ ⌉ z))))
         (ve-split⊕₂ᴰ G₁ G₂ A y0)
  ⟫ cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ z))
         (push-⊎fam₂ (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
                     (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₂)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0)))
  ⟫ pushS⊕₂ (tF-coh G₁) (tF-coh G₂)
      (coerce-ν-in ⌈ eraseF G₂ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₂)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0))))
  ⟫ cong inj₂ (coerce-νin-erase-D w₂ A y0)
  ⟫ sym (cong (λ z → coerce-ν-in (G₁ TT.⊕ G₂) ⟦ A ⟧ᴰ (coerce-functor-D (wf-Sum w₁ w₂) A z))
              (push⊎₂ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) y0))
coerce-νin-erase-D {G₁ TT.⊗ G₂} (wf-Prod w₁ w₂) A (x0 , y0) =
    cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊗ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟦ A ⟧ᴰ
             (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟧F Z) (cohᴰ A)
               (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ (wf-Prod w₁ w₂))) ⌈ ⌊ A ⌋ ⌉ z))))
         (ve-split⊗ᴰ G₁ G₂ A x0 y0)
  ⟫ cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊗ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟦ A ⟧ᴰ z))
         (push-×fam (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
                    (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₁)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0))
                    (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₂)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0)))
  ⟫ pushS⊗ (tF-coh G₁) (tF-coh G₂)
      (coerce-ν-in ⌈ eraseF G₁ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₁)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0))))
      (coerce-ν-in ⌈ eraseF G₂ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D (wf-⌈⌉ (wf-⌊⌋ w₂)) ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0))))
  ⟫ cong₂ _,_ (coerce-νin-erase-D w₁ A x0) (coerce-νin-erase-D w₂ A y0)
  ⟫ sym (cong (λ z → coerce-ν-in (G₁ TT.⊗ G₂) ⟦ A ⟧ᴰ (coerce-functor-D (wf-Prod w₁ w₂) A z))
              (push× (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0 y0))
