-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson and contributors

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
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst-subst-sym; subst-sym-subst)

open import Once.Word using (Carrier)
open import Once.Type as TT
  using (Functor; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Functor.Translate using (translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F)
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; νS; unfoldS; anaS; sfmapAna)
open import Once.Semantics.Functor.Laws
  using (_∼S_; ⟦_⟧SF-rel; unfoldS-∼; bisimS-to-eq)
open import Once.Semantics.Machine
  using (⟦_⟧F; ⟦_⟧; sem-ana; sfmapSemAna; coerce-ν-in; coerce-functor; coh; tF-coh)
open import Once.IRTy using (⌊_⌋; ⌈_⌉)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.Denotation.TraceMonad using (T; valueT; returnT)
open import Once.Denotation.ValueDomain using (⟦_⟧ᴰ; forget; inject; cohᴰ)
open import Once.Postulates using (extensionality)

------------------------------------------------------------------------
-- `sem-ana` factors through the νS-level `anaS`: unfolding the raw functor
-- coalgebra `A → ⟦F⟧F A` equals unfolding its coerced SFunctor form
-- `A → ⟦translateF F⟧SF A`. SAME functor `F` on both sides — a clean
-- bisimulation mirroring `sem-ana-Out-bisim`/`sem-ana-Out-rel`.
------------------------------------------------------------------------

mutual
  sem-ana-anaS-bisim : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
    → sem-ana F coalg a ∼S anaS {translateF Carrier F} (λ x → coerce-ν-in F A (coalg x)) a
  unfoldS-∼ (sem-ana-anaS-bisim {F} {A} coalg a) =
    sem-ana-anaS-rel coalg (translateF Carrier F) (coerce-ν-in F A (coalg a))

  sem-ana-anaS-rel : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A)
                       (H : SFunctor) (x : ⟦ H ⟧SF A)
    → ⟦ H ⟧SF-rel (_∼S_ {translateF Carrier F})
        (sfmapSemAna F H coalg x)
        (sfmapAna {translateF Carrier F} H (λ y → coerce-ν-in F A (coalg y)) x)
  sem-ana-anaS-rel coalg (SK _)      x        = refl
  sem-ana-anaS-rel coalg SId         x        = sem-ana-anaS-bisim coalg x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₁ x) = sem-ana-anaS-rel coalg H₁ x
  sem-ana-anaS-rel coalg (H₁ S⊕ H₂) (inj₂ y) = sem-ana-anaS-rel coalg H₂ y
  sem-ana-anaS-rel coalg (H₁ S⊗ H₂) (x , y)  =
    sem-ana-anaS-rel coalg H₁ x , sem-ana-anaS-rel coalg H₂ y

sem-ana-anaS : ∀ {F : Functor} {A : Set} (coalg : A → ⟦ F ⟧F A) (a : A)
  → sem-ana F coalg a ≡ anaS {translateF Carrier F} (λ x → coerce-ν-in F A (coalg x)) a
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
