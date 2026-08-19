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

module Once.Adequacy.AnaErased where

open import Function using (id)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _++_)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; subst-subst-sym; subst-sym-subst)

open import Once.Word using (Carrier)
open import Once.Float.Dyadic using (Dyadic)
open import Once.Type as TT
  using (Functor; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Functor.Translate using (translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F; ⌈⟧TI-commute; ⌊⟧T-commute)
import Once.IRTy as II
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; νS; unfoldS; anaS; sfmapAna)
open import Once.Semantics.Functor.Laws
  using (_∼S_; ⟦_⟧SF-rel; unfoldS-∼; bisimS-to-eq)
open import Once.Semantics.Machine
  using (⟦_⟧F; ⟦_⟧; sem-ana; sfmapSemAna; coerce-ν-in; coerce-functor; coh; tF-coh;
         coerce-full-to-base; base-coh)
open import Once.IRTy using (⌊_⌋; ⌈_⌉)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.Denotation.TraceMonad using (T; valueT; returnT)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; forget; inject; cohᴰ)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- `sem-ana` factors through the νS-level `anaS`: unfolding the raw functor
-- coalgebra `A → ⟦F⟧F A` equals unfolding its coerced SFunctor form
-- `A → ⟦translateF F⟧SF A`. SAME functor `F` on both sides — a clean
-- bisimulation mirroring `sem-ana-Out-bisim`/`sem-ana-Out-rel`.
------------------------------------------------------------------------

mutual
  sem-ana-anaS-bisim : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
    → sem-ana F coalg a ∼S anaS {translateF Carrier Carrier F} (λ x → coerce-ν-in F A (coalg x)) a
  unfoldS-∼ (sem-ana-anaS-bisim {F} {A} coalg a) =
    sem-ana-anaS-rel coalg (translateF Carrier Carrier F) (coerce-ν-in F A (coalg a))

  sem-ana-anaS-rel : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A)
                       (H : SFunctor) (x : ⟦ H ⟧SF A)
    → ⟦ H ⟧SF-rel (_∼S_ {translateF Carrier Carrier F})
        (sfmapSemAna F H coalg x)
        (sfmapAna {translateF Carrier Carrier F} H (λ y → coerce-ν-in F A (coalg y)) x)
  sem-ana-anaS-rel coalg (SK _)      x        = refl
  sem-ana-anaS-rel coalg SId         x        = sem-ana-anaS-bisim coalg x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₁ x) = sem-ana-anaS-rel coalg H₁ x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₂ y) = sem-ana-anaS-rel coalg H₂ y
  sem-ana-anaS-rel coalg (H₁ S⊗ H₂) (x , y)  =
    sem-ana-anaS-rel coalg H₁ x , sem-ana-anaS-rel coalg H₂ y

sem-ana-anaS : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
  → sem-ana F coalg a ≡ anaS {translateF Carrier Carrier F} (λ x → coerce-ν-in F A (coalg x)) a
sem-ana-anaS coalg a = bisimS-to-eq _ _ (sem-ana-anaS-bisim coalg a)

------------------------------------------------------------------------
-- Cross-functor transport of `anaS` over an SFunctor equality — cheap
-- (match the equation to `refl`). This is where `tF-coh` discharges.
------------------------------------------------------------------------

anaS-subst-nat : ∀ {H₁ H₂ : SFunctor} {A : Set} (eq : H₁ ≡ H₂)
                   (coalg : A → ⟦ H₁ ⟧SF A) (a : A)
  → subst νS eq (anaS coalg a) ≡ anaS (subst (λ H → A → ⟦ H ⟧SF A) eq coalg) a
anaS-subst-nat refl coalg a = refl

------------------------------------------------------------------------
-- The erasure round-trip: the `tF-coh`-transported erased-functor unfold
-- equals the surface-functor unfold, GIVEN the coalgebras correspond after
-- transport (discharged in `ana-body` from the coalgebra IH + coerce
-- round-trip). Value half of `ana`-faithfulness.
------------------------------------------------------------------------

sem-ana-erase-coh′ : ∀ {F : Functor} {A : Set}
    (cL : A → ⟦ ⌈ eraseF F ⌉F ⟧F A) (cR : A → ⟦ F ⟧F A) (a : A)
    (ceq : subst (λ H → A → ⟦ H ⟧SF A) (tF-coh F)
             (λ x → coerce-ν-in ⌈ eraseF F ⌉F A (cL x))
           ≡ (λ x → coerce-ν-in F A (cR x)))
  → subst νS (tF-coh F) (sem-ana ⌈ eraseF F ⌉F cL a) ≡ sem-ana F cR a
sem-ana-erase-coh′ {F} {A} cL cR a ceq =
  trans (cong (subst νS (tF-coh F)) (sem-ana-anaS cL a))
    (trans (anaS-subst-nat (tF-coh F) (λ x → coerce-ν-in ⌈ eraseF F ⌉F A (cL x)) a)
      (trans (cong (λ c → anaS c a) ceq)
             (sym (sem-ana-anaS cR a))))

-- Carrier-eq packaging: fold a carrier equality `ceq2 : A₁ ≡ A₂` into the
-- erasure round-trip (match-to-refl → `sem-ana-erase-coh′`). Lets `ana-body`
-- run the erased-carrier `Val.⟦⌈⌊A⌋⌉⟧` sem-ana against the surface-carrier
-- `Val.⟦A⟧` one without hand-threading the carrier transport.
sem-ana-erase-full : ∀ {F : Functor} {A₁ A₂ : Set} (ceq2 : A₁ ≡ A₂)
    (cL : A₁ → ⟦ ⌈ eraseF F ⌉F ⟧F A₁) (cR : A₂ → ⟦ F ⟧F A₂) (a₁ : A₁)
    (ceq : subst (λ H → A₂ → ⟦ H ⟧SF A₂) (tF-coh F)
             (λ x → coerce-ν-in ⌈ eraseF F ⌉F A₂
                      (subst (λ Z → ⟦ ⌈ eraseF F ⌉F ⟧F Z) ceq2 (cL (subst id (sym ceq2) x))))
           ≡ (λ x → coerce-ν-in F A₂ (cR x)))
  → subst νS (tF-coh F) (sem-ana ⌈ eraseF F ⌉F cL a₁) ≡ sem-ana F cR (subst id ceq2 a₁)
sem-ana-erase-full refl cL cR a₁ ceq = sem-ana-erase-coh′ cL cR a₁ ceq

------------------------------------------------------------------------
-- TRACE round-trip core. `events-F` DISCARDS the `K`-leaves (`events-F
-- (K _) _ _ = []`), which is exactly where `⌈eraseF G⌉F` and `G` differ —
-- so the erased/surface layer traces coincide as soon as the recursive
-- children (`Id`-positions) agree. `SFRel` is the structural witness that
-- the two functor layers agree at `Id` (`⊤` at `K`, discarded).
------------------------------------------------------------------------

SFRel : ∀ (G : Functor) {Ve Vs : Set} (R : Ve → Vs → Set)
      → ⟦ ⌈ eraseF G ⌉F ⟧F Ve → ⟦ G ⟧F Vs → Set
SFRel (TT.K B)   R le        ls        = ⊤
SFRel TT.Id      R le        ls        = R le ls
SFRel (G₁ TT.⊕ G₂) R (inj₁ xe) (inj₁ xs) = SFRel G₁ R xe xs
SFRel (G₁ TT.⊕ G₂) R (inj₁ _)  (inj₂ _)  = ⊥
SFRel (G₁ TT.⊕ G₂) R (inj₂ _)  (inj₁ _)  = ⊥
SFRel (G₁ TT.⊕ G₂) R (inj₂ ye) (inj₂ ys) = SFRel G₂ R ye ys
SFRel (G₁ TT.⊗ G₂) R (xe , ye) (xs , ys) = SFRel G₁ R xe xs × SFRel G₂ R ye ys

events-F-erase : ∀ (G : Functor) {Ve Vs : Set} (R : Ve → Vs → Set)
    (child-e : Ve → List SigOpEvent) (child-s : Vs → List SigOpEvent)
    (child-R : ∀ {xe xs} → R xe xs → child-e xe ≡ child-s xs)
    (le : ⟦ ⌈ eraseF G ⌉F ⟧F Ve) (ls : ⟦ G ⟧F Vs)
  → SFRel G R le ls
  → events-F ⌈ eraseF G ⌉F child-e le ≡ events-F G child-s ls
events-F-erase (TT.K B)   R ce cs cR le        ls        _        = refl
events-F-erase TT.Id      R ce cs cR le        ls        r        = cR r
events-F-erase (G₁ TT.⊕ G₂) R ce cs cR (inj₁ xe) (inj₁ xs) r      = events-F-erase G₁ R ce cs cR xe xs r
events-F-erase (G₁ TT.⊕ G₂) R ce cs cR (inj₂ ye) (inj₂ ys) r      = events-F-erase G₂ R ce cs cR ye ys r
events-F-erase (G₁ TT.⊗ G₂) R ce cs cR (xe , ye) (xs , ys) (r₁ , r₂) =
  cong₂ _++_ (events-F-erase G₁ R ce cs cR xe xs r₁)
             (events-F-erase G₂ R ce cs cR ye ys r₂)

-- The pre-`coerce` structural relation on the layer VALUES (`⟦_⟧T` level):
-- `coh A` at `Id`, `⊤` at the discarded `K`-leaves. `coerce-functor` (identity
-- at `K`/`Id`, structural at `⊕`/`⊗`) carries it straight to `SFRel`.
TRel : ∀ (G : Functor) (A : TT.Type)
     → ⟦ TT.⟦ ⌈ eraseF G ⌉F ⟧T ⌈ ⌊ A ⌋ ⌉ ⟧ → ⟦ TT.⟦ G ⟧T A ⟧ → Set
TRel (TT.K B)     A ve        vs        = ⊤
TRel TT.Id        A ve        vs        = subst (λ z → z) (coh A) ve ≡ vs
TRel (G₁ TT.⊕ G₂) A (inj₁ xe) (inj₁ xs) = TRel G₁ A xe xs
TRel (G₁ TT.⊕ G₂) A (inj₁ _)  (inj₂ _)  = ⊥
TRel (G₁ TT.⊕ G₂) A (inj₂ _)  (inj₁ _)  = ⊥
TRel (G₁ TT.⊕ G₂) A (inj₂ ye) (inj₂ ys) = TRel G₂ A ye ys
TRel (G₁ TT.⊗ G₂) A (xe , ye) (xs , ys) = TRel G₁ A xe xs × TRel G₂ A ye ys

coerce-SFRel : ∀ (G : Functor) {A : TT.Type}
    (ve : ⟦ TT.⟦ ⌈ eraseF G ⌉F ⟧T ⌈ ⌊ A ⌋ ⌉ ⟧) (vs : ⟦ TT.⟦ G ⟧T A ⟧)
  → TRel G A ve vs
  → SFRel G (λ xe xs → subst (λ z → z) (coh A) xe ≡ xs)
      (coerce-functor ⌈ eraseF G ⌉F ⌈ ⌊ A ⌋ ⌉ ve) (coerce-functor G A vs)
coerce-SFRel (TT.K B)     ve        vs        _        = tt
coerce-SFRel TT.Id        ve        vs        r        = r
coerce-SFRel (G₁ TT.⊕ G₂) (inj₁ xe) (inj₁ xs) r        = coerce-SFRel G₁ xe xs r
coerce-SFRel (G₁ TT.⊕ G₂) (inj₂ ye) (inj₂ ys) r        = coerce-SFRel G₂ ye ys r
coerce-SFRel (G₁ TT.⊗ G₂) (xe , ye) (xs , ys) (r₁ , r₂) =
  coerce-SFRel G₁ xe xs r₁ , coerce-SFRel G₂ ye ys r₂

------------------------------------------------------------------------
-- `forget`/`inject` commute with the `coh`/`cohᴰ` transports (general
-- version of `CataErased.forget-coh`, all types not just base). Mutual,
-- structural on the type, mirroring `forget`/`inject`. The `⊕`/`⊗` cases
-- push `subst` through the constructors; the arrow case is `extensionality`
-- + the closure-run, cross-recursing (`forget-coh-gen` at the codomain,
-- `inject-coh-nat` at the domain). Small refl-push helpers below.
------------------------------------------------------------------------

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

-- pure arrow (for `coh`): apply-then-transport
push→ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (g : A → B) (v : A')
  → subst id (cong₂ (λ x y → x → y) p q) g v ≡ subst id q (g (subst id (sym p) v))
push→ refl refl g v = refl

-- pure arrow (for `coh`, `sym` direction)
push→⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (g : A' → B') (v : A)
  → subst id (sym (cong₂ (λ x y → x → y) p q)) g v ≡ subst id (sym q) (g (subst id p v))
push→⁻ refl refl g v = refl

-- monadic arrow (for `cohᴰ`, `sym` direction): apply the transported closure
push→Tᵈ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (f : A' → T B') (w : A)
  → subst id (sym (cong₂ (λ x y → x → T y) p q)) f w ≡ subst T (sym q) (f (subst id p w))
push→Tᵈ refl refl f w = refl

subst-T-value : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X)
  → valueT (subst T eq h) zero ≡ subst id eq (valueT h zero)
subst-T-value refl h = refl

subst-T-returnT : ∀ {X Y : Set} (eq : X ≡ Y) (x : X)
  → subst T eq (returnT x) ≡ returnT (subst id eq x)
subst-T-returnT refl x = refl

mutual
  forget-coh-gen : ∀ (A : TT.Type) (arg : ⟦ A ⟧ᴰ)
    → subst id (coh A) (forget (subst id (sym (cohᴰ A)) arg)) ≡ forget arg
  forget-coh-gen Unit       arg = refl
  forget-coh-gen Int        arg = refl
  forget-coh-gen Float      arg = refl
  forget-coh-gen Str        arg = refl
  forget-coh-gen Buffer     arg = refl
  forget-coh-gen Void       ()
  forget-coh-gen (μ-type F) arg = subst-subst-sym (coh (μ-type F))
  forget-coh-gen (ν-type F) arg = subst-subst-sym (coh (ν-type F))
  forget-coh-gen (A * B) (a , b) =
    trans (cong (λ p → subst id (coh (A * B)) (forget p)) (push×⁻ (cohᴰ A) (cohᴰ B) a b))
      (trans (push× (coh A) (coh B) (forget (subst id (sym (cohᴰ A)) a))
                                     (forget (subst id (sym (cohᴰ B)) b)))
             (cong₂ _,_ (forget-coh-gen A a) (forget-coh-gen B b)))
  forget-coh-gen (A + B) (inj₁ a) =
    trans (cong (λ p → subst id (coh (A + B)) (forget p)) (push⊎₁⁻ (cohᴰ A) (cohᴰ B) a))
      (trans (push⊎₁ (coh A) (coh B) (forget (subst id (sym (cohᴰ A)) a)))
             (cong inj₁ (forget-coh-gen A a)))
  forget-coh-gen (A + B) (inj₂ b) =
    trans (cong (λ p → subst id (coh (A + B)) (forget p)) (push⊎₂⁻ (cohᴰ A) (cohᴰ B) b))
      (trans (push⊎₂ (coh A) (coh B) (forget (subst id (sym (cohᴰ B)) b)))
             (cong inj₂ (forget-coh-gen B b)))
  forget-coh-gen (A ⇒[ k ] B) arg = extensionality (λ va →
    trans (push→ (coh A) (coh B) (forget {⌈ ⌊ A ⇒[ k ] B ⌋ ⌉} (subst id (sym (cohᴰ (A ⇒[ k ] B))) arg)) va)
      (trans (cong (λ z → subst id (coh B) (forget (valueT z zero)))
                   (push→Tᵈ (cohᴰ A) (cohᴰ B) arg (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))
        (trans (cong (λ z → subst id (coh B) (forget z))
                     (subst-T-value (sym (cohᴰ B)) (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
          (trans (forget-coh-gen B (valueT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va)))) zero))
                 (cong (λ z → forget (valueT (arg z) zero))
                       (trans (cong (subst id (cohᴰ A)) (inject-coh-nat A va))
                              (subst-subst-sym (cohᴰ A))))))))

  inject-coh-nat : ∀ (A : TT.Type) (v : ⟦ A ⟧)
    → inject (subst id (sym (coh A)) v) ≡ subst id (sym (cohᴰ A)) (inject v)
  inject-coh-nat Unit       v = refl
  inject-coh-nat Int        v = refl
  inject-coh-nat Float      v = refl
  inject-coh-nat Str        v = refl
  inject-coh-nat Buffer     v = refl
  inject-coh-nat Void       ()
  inject-coh-nat (μ-type F) v = refl
  inject-coh-nat (ν-type F) v = refl
  inject-coh-nat (A * B) (a , b) =
    trans (cong (λ p → inject p) (push×⁻ (coh A) (coh B) a b))
      (trans (cong₂ _,_ (inject-coh-nat A a) (inject-coh-nat B b))
             (sym (push×⁻ (cohᴰ A) (cohᴰ B) (inject a) (inject b))))
  inject-coh-nat (A + B) (inj₁ a) =
    trans (cong inject (push⊎₁⁻ (coh A) (coh B) a))
      (trans (cong inj₁ (inject-coh-nat A a))
             (sym (push⊎₁⁻ (cohᴰ A) (cohᴰ B) (inject a))))
  inject-coh-nat (A + B) (inj₂ b) =
    trans (cong inject (push⊎₂⁻ (coh A) (coh B) b))
      (trans (cong inj₂ (inject-coh-nat B b))
             (sym (push⊎₂⁻ (cohᴰ A) (cohᴰ B) (inject b))))
  inject-coh-nat (A ⇒[ k ] B) v = extensionality (λ da →
    trans (cong (λ z → returnT (inject z)) (push→⁻ (coh A) (coh B) v (forget da)))
      (trans (cong returnT (inject-coh-nat B (v (subst id (coh A) (forget da)))))
        (trans (cong (λ z → returnT (subst id (sym (cohᴰ B)) (inject (v z))))
                     (trans (cong (λ w → subst id (coh A) (forget w)) (sym (subst-sym-subst (cohᴰ A))))
                            (forget-coh-gen A (subst id (cohᴰ A) da))))
               (sym (trans (push→Tᵈ (cohᴰ A) (cohᴰ B) (inject {A ⇒[ k ] B} v) da)
                           (subst-T-returnT (sym (cohᴰ B)) (inject {B} (v (forget {A} (subst id (cohᴰ A) da))))))))))

------------------------------------------------------------------------
-- `coh-to-TRel`: the shared `v0` of the erased & surface layer values
-- (both `subst`-transports of `v0 = valueT (evalᴰ p (inject seed)) m`) is
-- coh-A-related at every `Id`-position — i.e. `TRel` holds. Structural on
-- `G`, pushing the four transports through `inj`/pair (refl push-helpers),
-- the `Id`-leaf discharged by `forget-coh-gen`. Feeds `ana-ev-bridge`.
------------------------------------------------------------------------

-- push `subst id (cong ⟦_⟧ᴰᴵ (cong₂ _+_/_*_ …))` through inj/pair
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

ve-split⊕₁ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (x0 : ⟦ ⌊ TT.⟦ G₁ ⟧T A ⌋ ⟧ᴰᴵ)
  → subst ⟦_⟧ (⌈⟧TI-commute (eraseF (G₁ TT.⊕ G₂)) ⌊ A ⌋)
       (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute (G₁ TT.⊕ G₂) A)) (inj₁ x0)))
    ≡ inj₁ (subst ⟦_⟧ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋)
              (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₁ A)) x0)))
ve-split⊕₁ G₁ G₂ A x0 =
  trans (cong (λ z → subst ⟦_⟧ (⌈⟧TI-commute (eraseF (G₁ TT.⊕ G₂)) ⌊ A ⌋) (forget z))
              (pushᴵ+₁ (⌊⟧T-commute G₁ A) (⌊⟧T-commute G₂ A) x0))
        (pushⱽ+₁ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
                 (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₁ A)) x0)))

ve-split⊕₂ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (y0 : ⟦ ⌊ TT.⟦ G₂ ⟧T A ⌋ ⟧ᴰᴵ)
  → subst ⟦_⟧ (⌈⟧TI-commute (eraseF (G₁ TT.⊕ G₂)) ⌊ A ⌋)
       (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute (G₁ TT.⊕ G₂) A)) (inj₂ y0)))
    ≡ inj₂ (subst ⟦_⟧ (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
              (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₂ A)) y0)))
ve-split⊕₂ G₁ G₂ A y0 =
  trans (cong (λ z → subst ⟦_⟧ (⌈⟧TI-commute (eraseF (G₁ TT.⊕ G₂)) ⌊ A ⌋) (forget z))
              (pushᴵ+₂ (⌊⟧T-commute G₁ A) (⌊⟧T-commute G₂ A) y0))
        (pushⱽ+₂ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
                 (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₂ A)) y0)))

ve-split⊗ : ∀ (G₁ G₂ : Functor) (A : TT.Type)
              (x0 : ⟦ ⌊ TT.⟦ G₁ ⟧T A ⌋ ⟧ᴰᴵ) (y0 : ⟦ ⌊ TT.⟦ G₂ ⟧T A ⌋ ⟧ᴰᴵ)
  → subst ⟦_⟧ (⌈⟧TI-commute (eraseF (G₁ TT.⊗ G₂)) ⌊ A ⌋)
       (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute (G₁ TT.⊗ G₂) A)) (x0 , y0)))
    ≡ (subst ⟦_⟧ (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₁ A)) x0))
      , subst ⟦_⟧ (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋) (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₂ A)) y0)))
ve-split⊗ G₁ G₂ A x0 y0 =
  trans (cong (λ z → subst ⟦_⟧ (⌈⟧TI-commute (eraseF (G₁ TT.⊗ G₂)) ⌊ A ⌋) (forget z))
              (pushᴵ* (⌊⟧T-commute G₁ A) (⌊⟧T-commute G₂ A) x0 y0))
        (pushⱽ* (⌈⟧TI-commute (eraseF G₁) ⌊ A ⌋) (⌈⟧TI-commute (eraseF G₂) ⌊ A ⌋)
                (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₁ A)) x0))
                (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G₂ A)) y0)))

coh-to-TRel : ∀ (G : Functor) (A : TT.Type) (v0 : ⟦ ⌊ TT.⟦ G ⟧T A ⌋ ⟧ᴰᴵ)
  → TRel G A
      (subst ⟦_⟧ (⌈⟧TI-commute (eraseF G) ⌊ A ⌋)
             (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G A)) v0)))
      (forget (subst id (cohᴰ (TT.⟦ G ⟧T A)) v0))
coh-to-TRel (TT.K B) A v0 = tt
coh-to-TRel TT.Id A v0 =
  trans (cong (λ w → subst id (coh A) (forget w)) (sym (subst-sym-subst (cohᴰ A))))
        (forget-coh-gen A (subst id (cohᴰ A) v0))
coh-to-TRel (G₁ TT.⊕ G₂) A (inj₁ x0) =
  subst₂ (TRel (G₁ TT.⊕ G₂) A)
    (sym (ve-split⊕₁ G₁ G₂ A x0))
    (sym (cong (forget {TT.⟦ G₁ TT.⊕ G₂ ⟧T A}) (push⊎₁ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0)))
    (coh-to-TRel G₁ A x0)
coh-to-TRel (G₁ TT.⊕ G₂) A (inj₂ y0) =
  subst₂ (TRel (G₁ TT.⊕ G₂) A)
    (sym (ve-split⊕₂ G₁ G₂ A y0))
    (sym (cong (forget {TT.⟦ G₁ TT.⊕ G₂ ⟧T A}) (push⊎₂ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) y0)))
    (coh-to-TRel G₂ A y0)
coh-to-TRel (G₁ TT.⊗ G₂) A (x0 , y0) =
  subst₂ (TRel (G₁ TT.⊗ G₂) A)
    (sym (ve-split⊗ G₁ G₂ A x0 y0))
    (sym (cong (forget {TT.⟦ G₁ TT.⊗ G₂ ⟧T A}) (push× (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0 y0)))
    (coh-to-TRel G₁ A x0 , coh-to-TRel G₂ A y0)

------------------------------------------------------------------------
-- `coerce-ν-in-erase`: the value-half coalgebra correspondence (`ceq` for
-- `sem-ana-erase-full`). Dual of `coh-to-TRel` but landing in `⟦_⟧SF` via
-- `coerce-ν-in` — so, unlike `events-F`, the K-leaves must be reconciled
-- (`base-in`, via `coerce-full-to-base`/`base-coh`). Structural on `G`.
------------------------------------------------------------------------

-- K-leaf: `coerce-full-to-base` commutes with the `coh`/`base-coh` transports.
base-in : ∀ (B : TT.Type) (v0 : ⟦ ⌊ B ⌋ ⟧ᴰᴵ)
  → subst id (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forget v0))
    ≡ coerce-full-to-base B (forget (subst id (cohᴰ B) v0))
base-in Unit       v0 = refl
base-in Int        v0 = refl
base-in Float      v0 = refl
base-in Str        v0 = refl
base-in Buffer     v0 = refl
base-in Void       ()
base-in (A ⇒[ k ] B) v0 = refl
base-in (μ-type F) v0 = refl
base-in (ν-type F) v0 = refl
base-in (A * B) (a , b) =
  trans (push× (base-coh A) (base-coh B)
               (coerce-full-to-base ⌈ ⌊ A ⌋ ⌉ (forget a)) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forget b)))
    (trans (cong₂ _,_ (base-in A a) (base-in B b))
           (sym (cong (coerce-full-to-base (A * B)) (cong forget (push× (cohᴰ A) (cohᴰ B) a b)))))
base-in (A + B) (inj₁ a) =
  trans (push⊎₁ (base-coh A) (base-coh B) (coerce-full-to-base ⌈ ⌊ A ⌋ ⌉ (forget a)))
    (trans (cong inj₁ (base-in A a))
           (sym (cong (coerce-full-to-base (A + B)) (cong forget (push⊎₁ (cohᴰ A) (cohᴰ B) a)))))
base-in (A + B) (inj₂ b) =
  trans (push⊎₂ (base-coh A) (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forget b)))
    (trans (cong inj₂ (base-in B b))
           (sym (cong (coerce-full-to-base (A + B)) (cong forget (push⊎₂ (cohᴰ A) (cohᴰ B) b)))))

-- push `subst (λ H → ⟦H⟧SF X)(cong SK eq)` (SK-constant, carrier-blind)
pushSK : ∀ {X : Set} {b₁ b₂ : Set} (eq : b₁ ≡ b₂) (v : b₁)
  → subst (λ H → ⟦ H ⟧SF X) (cong SK eq) v ≡ subst id eq v
pushSK refl v = refl

-- carrier-align is the identity at a K-leaf (⟦K B'⟧F is carrier-blind)
subst-KF-const : ∀ {B' : TT.Type} {X Y : Set} (eq : X ≡ Y) (v : ⟦ TT.K B' ⟧F X)
  → subst (λ Z → ⟦ TT.K B' ⟧F Z) eq v ≡ v
subst-KF-const refl v = refl

-- the erased-side layer value (from `v0`), factored out for readability
VE0 : ∀ (G : Functor) (A : TT.Type) (v0 : ⟦ ⌊ TT.⟦ G ⟧T A ⌋ ⟧ᴰᴵ) → ⟦ TT.⟦ ⌈ eraseF G ⌉F ⟧T ⌈ ⌊ A ⌋ ⌉ ⟧
VE0 G A v0 = subst ⟦_⟧ (⌈⟧TI-commute (eraseF G) ⌊ A ⌋) (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G A)) v0))

-- subst over ⊎-/×-valued families and over `cong₂ _S⊕_/_S⊗_` (all refl-match)
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
vs-split⊕₁ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (x0 : ⟦ ⌊ TT.⟦ G₁ ⟧T A ⌋ ⟧ᴰᴵ)
  → forget (subst id (cohᴰ (TT.⟦ G₁ TT.⊕ G₂ ⟧T A)) (inj₁ x0))
    ≡ inj₁ (forget (subst id (cohᴰ (TT.⟦ G₁ ⟧T A)) x0))
vs-split⊕₁ G₁ G₂ A x0 =
  cong (forget {TT.⟦ G₁ TT.⊕ G₂ ⟧T A}) (push⊎₁ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0)

vs-split⊕₂ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (y0 : ⟦ ⌊ TT.⟦ G₂ ⟧T A ⌋ ⟧ᴰᴵ)
  → forget (subst id (cohᴰ (TT.⟦ G₁ TT.⊕ G₂ ⟧T A)) (inj₂ y0))
    ≡ inj₂ (forget (subst id (cohᴰ (TT.⟦ G₂ ⟧T A)) y0))
vs-split⊕₂ G₁ G₂ A y0 =
  cong (forget {TT.⟦ G₁ TT.⊕ G₂ ⟧T A}) (push⊎₂ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) y0)

vs-split⊗ : ∀ (G₁ G₂ : Functor) (A : TT.Type) (x0 : ⟦ ⌊ TT.⟦ G₁ ⟧T A ⌋ ⟧ᴰᴵ) (y0 : ⟦ ⌊ TT.⟦ G₂ ⟧T A ⌋ ⟧ᴰᴵ)
  → forget (subst id (cohᴰ (TT.⟦ G₁ TT.⊗ G₂ ⟧T A)) (x0 , y0))
    ≡ (forget (subst id (cohᴰ (TT.⟦ G₁ ⟧T A)) x0) , forget (subst id (cohᴰ (TT.⟦ G₂ ⟧T A)) y0))
vs-split⊗ G₁ G₂ A x0 y0 =
  cong (forget {TT.⟦ G₁ TT.⊗ G₂ ⟧T A}) (push× (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0 y0)

coerce-νin-erase : ∀ (G : Functor) (A : TT.Type) (v0 : ⟦ ⌊ TT.⟦ G ⟧T A ⌋ ⟧ᴰᴵ)
  → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh G)
       (coerce-ν-in ⌈ eraseF G ⌉F ⟦ A ⟧
         (subst (λ Z → ⟦ ⌈ eraseF G ⌉F ⟧F Z) (coh A)
           (coerce-functor ⌈ eraseF G ⌉F ⌈ ⌊ A ⌋ ⌉
             (subst ⟦_⟧ (⌈⟧TI-commute (eraseF G) ⌊ A ⌋)
                    (forget (subst id (cong ⟦_⟧ᴰᴵ (⌊⟧T-commute G A)) v0))))))
    ≡ coerce-ν-in G ⟦ A ⟧ (coerce-functor G A (forget (subst id (cohᴰ (TT.⟦ G ⟧T A)) v0)))
coerce-νin-erase (TT.K B) A v0 =
  trans (cong (subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (TT.K B)))
              (cong (coerce-ν-in ⌈ eraseF (TT.K B) ⌉F ⟦ A ⟧) (subst-KF-const (coh A) (forget v0))))
    (trans (pushSK (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forget v0)))
           (base-in B v0))
coerce-νin-erase TT.Id A v0 = coh-to-TRel TT.Id A v0
coerce-νin-erase (G₁ TT.⊕ G₂) A (inj₁ x0) =
  trans (cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (G₁ TT.⊕ G₂))
                (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧
                  (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟧F Z) (coh A)
                    (coerce-functor ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⌈ ⌊ A ⌋ ⌉ z))))
              (ve-split⊕₁ G₁ G₂ A x0))
    (trans (cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (G₁ TT.⊕ G₂))
                  (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ z))
                (push-⊎fam₁ (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (coh A)
                            (coerce-functor ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₁ A x0))))
      (trans (pushS⊕₁ (tF-coh G₁) (tF-coh G₂)
                (coerce-ν-in ⌈ eraseF G₁ ⌉F ⟦ A ⟧
                  (subst (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (coh A) (coerce-functor ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₁ A x0)))))
        (trans (cong inj₁ (coerce-νin-erase G₁ A x0))
               (sym (cong (λ z → coerce-ν-in (G₁ TT.⊕ G₂) ⟦ A ⟧ (coerce-functor (G₁ TT.⊕ G₂) A z))
                          (vs-split⊕₁ G₁ G₂ A x0))))))
coerce-νin-erase (G₁ TT.⊕ G₂) A (inj₂ y0) =
  trans (cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (G₁ TT.⊕ G₂))
                (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧
                  (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟧F Z) (coh A)
                    (coerce-functor ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⌈ ⌊ A ⌋ ⌉ z))))
              (ve-split⊕₂ G₁ G₂ A y0))
    (trans (cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (G₁ TT.⊕ G₂))
                  (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ z))
                (push-⊎fam₂ (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (coh A)
                            (coerce-functor ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₂ A y0))))
      (trans (pushS⊕₂ (tF-coh G₁) (tF-coh G₂)
                (coerce-ν-in ⌈ eraseF G₂ ⌉F ⟦ A ⟧
                  (subst (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (coh A) (coerce-functor ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₂ A y0)))))
        (trans (cong inj₂ (coerce-νin-erase G₂ A y0))
               (sym (cong (λ z → coerce-ν-in (G₁ TT.⊕ G₂) ⟦ A ⟧ (coerce-functor (G₁ TT.⊕ G₂) A z))
                          (vs-split⊕₂ G₁ G₂ A y0))))))
coerce-νin-erase (G₁ TT.⊗ G₂) A (x0 , y0) =
  trans (cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (G₁ TT.⊗ G₂))
                (coerce-ν-in ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟦ A ⟧
                  (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟧F Z) (coh A)
                    (coerce-functor ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⌈ ⌊ A ⌋ ⌉ z))))
              (ve-split⊗ G₁ G₂ A x0 y0))
    (trans (cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧) (tF-coh (G₁ TT.⊗ G₂))
                  (coerce-ν-in ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟦ A ⟧ z))
                (push-×fam (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (coh A)
                           (coerce-functor ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₁ A x0))
                           (coerce-functor ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₂ A y0))))
      (trans (pushS⊗ (tF-coh G₁) (tF-coh G₂)
                (coerce-ν-in ⌈ eraseF G₁ ⌉F ⟦ A ⟧ (subst (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (coh A) (coerce-functor ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₁ A x0))))
                (coerce-ν-in ⌈ eraseF G₂ ⌉F ⟦ A ⟧ (subst (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (coh A) (coerce-functor ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0 G₂ A y0)))))
        (trans (cong₂ _,_ (coerce-νin-erase G₁ A x0) (coerce-νin-erase G₂ A y0))
               (sym (cong (λ z → coerce-ν-in (G₁ TT.⊗ G₂) ⟦ A ⟧ (coerce-functor (G₁ TT.⊗ G₂) A z))
                          (vs-split⊗ G₁ G₂ A x0 y0))))))
