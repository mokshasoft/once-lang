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
module Once.Adequacy.AnaErased (fmt : TargetNum) where

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
  using (Functor; Unit; Void; Int; Str; Float; Buffer; _*_; _+_; _⇒[_]_; μ-type; ν-type)
open import Once.Functor.Translate using (translateF)
open import Once.IRTy using (eraseF; ⌈_⌉F; ⌈⟧TI-commute; ⌊⟧T-commute)
import Once.IRTy as II
open import Once.Semantics.Functor
  using (SFunctor; SK; SId; _S⊕_; _S⊗_; ⟦_⟧SF; νS; unfoldS; anaS; sfmapAna; anaLayerS)
open import Once.Semantics.Functor.Laws
  using (_∼S_; ⟦_⟧SF-rel; unfoldS-∼; bisimS-to-eq)
open import Once.Semantics.Machine
  using (⟦_⟧F; ⟦_⟧; sem-ana; sfmapSemAna; semAnaLayer; coerce-ν-in; coerce-functor; coh; tF-coh;
         coerce-full-to-base; base-coh)
open import Once.IRTy using (⌊_⌋; ⌈_⌉)
open import Once.Res using (Res; stopped; returns; mapRes; mapRes-id; mapRes-∘; mapRes-cong; Res-rel)
open import Once.Denotation.Trace using (SigOpEvent)
open import Once.Denotation.TraceDenote using (events-F)
open import Once.Denotation.TraceMonad using (T; valueT; returnT; resT-lift)
open import Once.Denotation.ValueDomain
  using (⟦_⟧ᴰ; ⟦_⟧ᴰᴵ; forget; inject; cohᴰ; injectν-coh; forgetν-coh;
         νᵈ; forgetν; injectν; mapForgetν; mapInjectν; forgetLayer; injectLayer; coerce-functor-D)
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
  anaLayer-rel coalg stopped     = tt
  anaLayer-rel {F} {A} coalg (returns l) =
    sem-ana-anaS-rel coalg (translateF Carrier Carrier F) (coerce-ν-in F A l)

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
-- plan 0.98: the PURE arrow's codomain is `Res`-wrapped (`coh`'s arrow
-- clauses), so transporting a function value moves its result by `mapRes`.
push→ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (g : A → Res B) (v : A')
  → subst id (cong₂ (λ x y → x → Res y) p q) g v
    ≡ mapRes (subst id q) (g (subst id (sym p) v))
push→ refl refl g v = sym (mapRes-id (g v))

-- pure arrow (for `coh`, `sym` direction)
push→⁻ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (g : A' → Res B') (v : A)
  → subst id (sym (cong₂ (λ x y → x → Res y) p q)) g v
    ≡ mapRes (subst id (sym q)) (g (subst id p v))
push→⁻ refl refl g v = sym (mapRes-id (g v))

-- monadic arrow (for `cohᴰ`, `sym` direction): apply the transported closure
push→Tᵈ : ∀ {A A' B B' : Set} (p : A ≡ A') (q : B ≡ B') (f : A' → T B') (w : A)
  → subst id (sym (cong₂ (λ x y → x → T y) p q)) f w ≡ subst T (sym q) (f (subst id p w))
push→Tᵈ refl refl f w = refl

-- D143: the ERASED arrow. `coh`/`cohᴰ` build it with a ONE-equation `cong`
-- (only the codomain is transported — both sides already forget the argument),
-- so the two-equation `push→`/`push→Tᵈ` above do not apply. These are their
-- erased counterparts: the argument is passed through untouched.
push→₀ : ∀ {U B B' : Set} (q : B ≡ B') (g : U → Res B) (u : U)
  → subst id (cong (λ y → U → Res y) q) g u ≡ mapRes (subst id q) (g u)
push→₀ refl g u = sym (mapRes-id (g u))

push→₀⁻ : ∀ {U B B' : Set} (q : B ≡ B') (g : U → Res B') (u : U)
  → subst id (sym (cong (λ y → U → Res y) q)) g u ≡ mapRes (subst id (sym q)) (g u)
push→₀⁻ refl g u = sym (mapRes-id (g u))

push→T₀ᵈ : ∀ {U B B' : Set} (q : B ≡ B') (f : U → T B') (u : U)
  → subst id (sym (cong (λ y → U → T y) q)) f u ≡ subst T (sym q) (f u)
push→T₀ᵈ refl f u = refl

-- plan 0.98: the RESULT, not the value — a transported computation stops
-- exactly where the original does.
subst-T-value : ∀ {X Y : Set} (eq : X ≡ Y) (h : T X)
  → T.resT (subst T eq h) ≡ mapRes (subst id eq) (T.resT h)
subst-T-value refl h = sym (mapRes-id (T.resT h))

subst-T-returnT : ∀ {X Y : Set} (eq : X ≡ Y) (x : X)
  → subst T eq (returnT x) ≡ returnT (subst id eq x)
subst-T-returnT refl x = refl

-- plan 0.98: the `resT-lift` twin. `inject` at an arrow lifts a `Res` rather
-- than returning a value, so this is what the arrow clauses transport with.
subst-T-resT-lift : ∀ {X Y : Set} (eq : X ≡ Y) (r : Res X)
  → subst T eq (resT-lift r) ≡ resT-lift (mapRes (subst id eq) r)
subst-T-resT-lift refl r = cong resT-lift (sym (mapRes-id r))

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
  -- D179: no longer `subst-subst-sym` — ν's two domains differ, so this is
  -- the naturality square for `forgetν` rather than a transport cancelling.
  forget-coh-gen (ν-type F) arg = forgetν-coh (tF-coh F) arg
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
  -- D143: at an ERASED arrow neither side has an argument of type `A` to
  -- convert, so there is no `inject`/`coh A` round-trip — only the codomain
  -- transports, via the one-equation pushes.
  -- plan 0.98: the same chain, one level up. `forget` at an arrow is
  -- `mapRes forget ∘ T.resT`, and the codomain transport is a `mapRes` too, so
  -- the two fuse (`mapRes-∘`) and the old pointwise step becomes a
  -- `mapRes-cong` over the SAME induction hypothesis.
  forget-coh-gen (A ⇒[ TT.mk-kind TT.Zero π ] B) arg = extensionality (λ u →
    trans (push→₀ (coh B)
             (forget {⌈ ⌊ A ⇒[ TT.mk-kind TT.Zero π ] B ⌋ ⌉}
                     (subst id (sym (cohᴰ (A ⇒[ TT.mk-kind TT.Zero π ] B))) arg)) u)
      (trans (cong (λ z → mapRes (subst id (coh B)) (mapRes forget (T.resT z)))
                   (push→T₀ᵈ (cohᴰ B) arg u))
        (trans (cong (λ z → mapRes (subst id (coh B)) (mapRes forget z))
                     (subst-T-value (sym (cohᴰ B)) (arg u)))
          (trans (cong (mapRes (subst id (coh B)))
                       (mapRes-∘ forget (subst id (sym (cohᴰ B))) (T.resT (arg u))))
            (trans (mapRes-∘ (subst id (coh B)) _ (T.resT (arg u)))
                   (mapRes-cong (λ z → forget-coh-gen B z) (T.resT (arg u))))))))
  forget-coh-gen (A ⇒[ TT.mk-kind TT.One π ] B) arg = extensionality (λ va →
    trans (push→ (coh A) (coh B) (forget {⌈ ⌊ A ⇒[ TT.mk-kind TT.One π ] B ⌋ ⌉} (subst id (sym (cohᴰ (A ⇒[ TT.mk-kind TT.One π ] B))) arg)) va)
      (trans (cong (λ z → mapRes (subst id (coh B)) (mapRes forget (T.resT z)))
                   (push→Tᵈ (cohᴰ A) (cohᴰ B) arg (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))
        (trans (cong (λ z → mapRes (subst id (coh B)) (mapRes forget z))
                     (subst-T-value (sym (cohᴰ B)) (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
          (trans (cong (mapRes (subst id (coh B)))
                       (mapRes-∘ forget (subst id (sym (cohᴰ B)))
                                 (T.resT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va)))))))
            (trans (mapRes-∘ (subst id (coh B)) _
                             (T.resT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
              (trans (mapRes-cong (λ z → forget-coh-gen B z)
                                  (T.resT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
                     (cong (λ z → mapRes forget (T.resT (arg z)))
                           (trans (cong (subst id (cohᴰ A)) (inject-coh-nat A va))
                                  (subst-subst-sym (cohᴰ A))))))))))
  forget-coh-gen (A ⇒[ TT.mk-kind TT.Many π ] B) arg = extensionality (λ va →
    trans (push→ (coh A) (coh B) (forget {⌈ ⌊ A ⇒[ TT.mk-kind TT.Many π ] B ⌋ ⌉} (subst id (sym (cohᴰ (A ⇒[ TT.mk-kind TT.Many π ] B))) arg)) va)
      (trans (cong (λ z → mapRes (subst id (coh B)) (mapRes forget (T.resT z)))
                   (push→Tᵈ (cohᴰ A) (cohᴰ B) arg (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))
        (trans (cong (λ z → mapRes (subst id (coh B)) (mapRes forget z))
                     (subst-T-value (sym (cohᴰ B)) (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
          (trans (cong (mapRes (subst id (coh B)))
                       (mapRes-∘ forget (subst id (sym (cohᴰ B)))
                                 (T.resT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va)))))))
            (trans (mapRes-∘ (subst id (coh B)) _
                             (T.resT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
              (trans (mapRes-cong (λ z → forget-coh-gen B z)
                                  (T.resT (arg (subst id (cohᴰ A) (inject {⌈ ⌊ A ⌋ ⌉} (subst id (sym (coh A)) va))))))
                     (cong (λ z → mapRes forget (T.resT (arg z)))
                           (trans (cong (subst id (cohᴰ A)) (inject-coh-nat A va))
                                  (subst-subst-sym (cohᴰ A))))))))))

  inject-coh-nat : ∀ (A : TT.Type) (v : ⟦ A ⟧)
    → inject (subst id (sym (coh A)) v) ≡ subst id (sym (cohᴰ A)) (inject v)
  inject-coh-nat Unit       v = refl
  inject-coh-nat Int        v = refl
  inject-coh-nat Float      v = refl
  inject-coh-nat Str        v = refl
  inject-coh-nat Buffer     v = refl
  inject-coh-nat Void       ()
  inject-coh-nat (μ-type F) v = refl
  -- ν is no longer the identity on either side of the square (D179).
  inject-coh-nat (ν-type F) v = injectν-coh (tF-coh F) v
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
  -- D143: the ERASED arrow. Both `inject`s pass the argument straight through
  -- (`inject {A ⇒[Zero] B} pf = λ u → returnT (inject (pf u))`), so there is no
  -- `forget`/`coh A` round-trip on the domain — only the codomain transports.
  inject-coh-nat (A ⇒[ TT.mk-kind TT.Zero π ] B) v = extensionality (λ u →
    trans (cong (λ z → resT-lift (mapRes inject z)) (push→₀⁻ (coh B) v u))
      (trans (cong resT-lift
               (trans (mapRes-∘ inject (subst id (sym (coh B))) (v u))
               (trans (mapRes-cong (λ z → inject-coh-nat B z) (v u))
                      (sym (mapRes-∘ (subst id (sym (cohᴰ B))) inject (v u))))))
             (sym (trans (push→T₀ᵈ (cohᴰ B) (inject {A ⇒[ TT.mk-kind TT.Zero π ] B} v) u)
                         (subst-T-resT-lift (sym (cohᴰ B)) (mapRes inject (v u)))))))
  inject-coh-nat (A ⇒[ TT.mk-kind TT.One π ] B) v = extensionality (λ da →
    trans (cong (λ z → resT-lift (mapRes inject z)) (push→⁻ (coh A) (coh B) v (forget da)))
      (trans (cong resT-lift
               (trans (mapRes-∘ inject (subst id (sym (coh B))) (v (subst id (coh A) (forget da))))
               (trans (mapRes-cong (λ z → inject-coh-nat B z) (v (subst id (coh A) (forget da))))
                      (sym (mapRes-∘ (subst id (sym (cohᴰ B))) inject
                                     (v (subst id (coh A) (forget da))))))))
        (trans (cong (λ z → resT-lift (mapRes (subst id (sym (cohᴰ B))) (mapRes inject (v z))))
                     (trans (cong (λ w → subst id (coh A) (forget w)) (sym (subst-sym-subst (cohᴰ A))))
                            (forget-coh-gen A (subst id (cohᴰ A) da))))
               (sym (trans (push→Tᵈ (cohᴰ A) (cohᴰ B) (inject {A ⇒[ TT.mk-kind TT.One π ] B} v) da)
                           (subst-T-resT-lift (sym (cohᴰ B))
                             (mapRes inject (v (forget {A} (subst id (cohᴰ A) da))))))))))
  inject-coh-nat (A ⇒[ TT.mk-kind TT.Many π ] B) v = extensionality (λ da →
    trans (cong (λ z → resT-lift (mapRes inject z)) (push→⁻ (coh A) (coh B) v (forget da)))
      (trans (cong resT-lift
               (trans (mapRes-∘ inject (subst id (sym (coh B))) (v (subst id (coh A) (forget da))))
               (trans (mapRes-cong (λ z → inject-coh-nat B z) (v (subst id (coh A) (forget da))))
                      (sym (mapRes-∘ (subst id (sym (cohᴰ B))) inject
                                     (v (subst id (coh A) (forget da))))))))
        (trans (cong (λ z → resT-lift (mapRes (subst id (sym (cohᴰ B))) (mapRes inject (v z))))
                     (trans (cong (λ w → subst id (coh A) (forget w)) (sym (subst-sym-subst (cohᴰ A))))
                            (forget-coh-gen A (subst id (cohᴰ A) da))))
               (sym (trans (push→Tᵈ (cohᴰ A) (cohᴰ B) (inject {A ⇒[ TT.mk-kind TT.Many π ] B} v) da)
                           (subst-T-resT-lift (sym (cohᴰ B))
                             (mapRes inject (v (forget {A} (subst id (cohᴰ A) da))))))))))

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

------------------------------------------------------------------------
-- D179: `forget ∘ inject ≡ id` AT ν.
--
-- While ν's monadic meaning WAS its pure meaning, this was `refl`. Now the
-- round trip goes `νS → νᵈ → νS`, rebuilding every layer, so it is a
-- COINDUCTIVE equality. Both sides land back in `νS`, so it discharges
-- through the codebase's EXISTING `bisimS-to-eq` — no new axiom, and the same
-- precedent as `sem-CoIn-CoOut`.
--
-- The structural map is INLINED rather than routed through the existing
-- `sfmap-∼S-refl`: `--guardedness` rejects a corecursive call passed to a
-- defined function (D062), so a corecursive proof must place its own map
-- structurally at `SId`. That is a constraint, not duplication by choice.
------------------------------------------------------------------------

mutual
  forgetν-injectν-bisim : ∀ {F : SFunctor} (v : νS F) → forgetν (injectν v) ∼S v
  unfoldS-∼ (forgetν-injectν-bisim {F} v) = forgetν-injectν-res F F (unfoldS v)

  -- plan 0.98: the round-trip at the RESULT. A stopped ν forgets and injects
  -- back to a stopped one with no layer to relate, which is the `tt` clause.
  forgetν-injectν-res : ∀ (F G : SFunctor) (r : Res (⟦ G ⟧SF (νS F)))
                      → Res-rel (⟦ G ⟧SF-rel (_∼S_ {F}))
                          (forgetLayer F G (injectLayer F G r)) r
  forgetν-injectν-res F G stopped     = tt
  forgetν-injectν-res F G (returns x) = forgetν-injectν-rel F G x

  forgetν-injectν-rel : ∀ (F G : SFunctor) (x : ⟦ G ⟧SF (νS F))
                      → ⟦ G ⟧SF-rel (_∼S_ {F}) (mapForgetν F G (mapInjectν F G x)) x
  forgetν-injectν-rel F (SK B)     x        = refl
  forgetν-injectν-rel F SId        x        = forgetν-injectν-bisim x
  forgetν-injectν-rel F (G₁ S⊕ G₂) (inj₁ x) = forgetν-injectν-rel F G₁ x
  forgetν-injectν-rel F (G₁ S⊕ G₂) (inj₂ y) = forgetν-injectν-rel F G₂ y
  forgetν-injectν-rel F (G₁ S⊗ G₂) (x , y)  =
    (forgetν-injectν-rel F G₁ x , forgetν-injectν-rel F G₂ y)

forgetν-injectν : ∀ {F : SFunctor} (v : νS F) → forgetν (injectν v) ≡ v
forgetν-injectν v = bisimS-to-eq _ v (forgetν-injectν-bisim v)

------------------------------------------------------------------------
-- D179: the `ᴰ`-level analogue of `coerce-νin-erase`. The coalgebra is now
-- EFFECTFUL, so `ana`-faithfulness needs the erasure round-trip in the
-- MONADIC domain `⟦_⟧ᴰ`, not in `Val.⟦_⟧`.
--
-- Stated first and assumed, to check it is what `ana-body` actually needs
-- before it is proved (the statement is the risky part, not the induction).
------------------------------------------------------------------------

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

-- Structural on `G`, mirroring `coerce-νin-erase` — but SIMPLER, because
-- `coerce-functor-D` forgets only at `K`: the `Id` positions carry the
-- monadic carrier straight through, with no `forget` to commute past the
-- transports. The carrier-polymorphic `push*` helpers above are reused as-is.
coerce-νin-erase-D : ∀ (G : Functor) (A : TT.Type) (v0 : ⟦ ⌊ TT.⟦ G ⟧T A ⌋ ⟧ᴰᴵ)
  → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh G)
       (coerce-ν-in ⌈ eraseF G ⌉F ⟦ A ⟧ᴰ
         (subst (λ Z → ⟦ ⌈ eraseF G ⌉F ⟧F Z) (cohᴰ A)
           (coerce-functor-D ⌈ eraseF G ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G A v0))))
    ≡ coerce-ν-in G ⟦ A ⟧ᴰ
        (coerce-functor-D G A (subst id (cohᴰ (TT.⟦ G ⟧T A)) v0))
-- At `K` the ᴰ chain goes through `forget` exactly as the pure one does
-- (`coerce-functor-D (K _) = forget`), so this is the same proof — `base-in`
-- is reused unchanged.
coerce-νin-erase-D (TT.K B) A v0 =
    cong (subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (TT.K B)))
         (cong (coerce-ν-in ⌈ eraseF (TT.K B) ⌉F ⟦ A ⟧ᴰ)
               (subst-KF-const (cohᴰ A) (forget v0)))
  ⟫ pushSK (base-coh B) (coerce-full-to-base ⌈ ⌊ B ⌋ ⌉ (forget v0))
  ⟫ base-in B v0
coerce-νin-erase-D TT.Id A v0 = refl
coerce-νin-erase-D (G₁ TT.⊕ G₂) A (inj₁ x0) =
    cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ
             (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟧F Z) (cohᴰ A)
               (coerce-functor-D ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⌈ ⌊ A ⌋ ⌉ z))))
         (ve-split⊕₁ᴰ G₁ G₂ A x0)
  ⟫ cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ z))
         (push-⊎fam₁ (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
                     (coerce-functor-D ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0)))
  ⟫ pushS⊕₁ (tF-coh G₁) (tF-coh G₂)
      (coerce-ν-in ⌈ eraseF G₁ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0))))
  ⟫ cong inj₁ (coerce-νin-erase-D G₁ A x0)
  ⟫ sym (cong (λ z → coerce-ν-in (G₁ TT.⊕ G₂) ⟦ A ⟧ᴰ (coerce-functor-D (G₁ TT.⊕ G₂) A z))
              (push⊎₁ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0))
coerce-νin-erase-D (G₁ TT.⊕ G₂) A (inj₂ y0) =
    cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ
             (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟧F Z) (cohᴰ A)
               (coerce-functor-D ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⌈ ⌊ A ⌋ ⌉ z))))
         (ve-split⊕₂ᴰ G₁ G₂ A y0)
  ⟫ cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊕ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊕ G₂) ⌉F ⟦ A ⟧ᴰ z))
         (push-⊎fam₂ (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
                     (coerce-functor-D ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0)))
  ⟫ pushS⊕₂ (tF-coh G₁) (tF-coh G₂)
      (coerce-ν-in ⌈ eraseF G₂ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0))))
  ⟫ cong inj₂ (coerce-νin-erase-D G₂ A y0)
  ⟫ sym (cong (λ z → coerce-ν-in (G₁ TT.⊕ G₂) ⟦ A ⟧ᴰ (coerce-functor-D (G₁ TT.⊕ G₂) A z))
              (push⊎₂ (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) y0))
coerce-νin-erase-D (G₁ TT.⊗ G₂) A (x0 , y0) =
    cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊗ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟦ A ⟧ᴰ
             (subst (λ Z → ⟦ ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟧F Z) (cohᴰ A)
               (coerce-functor-D ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⌈ ⌊ A ⌋ ⌉ z))))
         (ve-split⊗ᴰ G₁ G₂ A x0 y0)
  ⟫ cong (λ z → subst (λ H → ⟦ H ⟧SF ⟦ A ⟧ᴰ) (tF-coh (G₁ TT.⊗ G₂))
           (coerce-ν-in ⌈ eraseF (G₁ TT.⊗ G₂) ⌉F ⟦ A ⟧ᴰ z))
         (push-×fam (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
                    (coerce-functor-D ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0))
                    (coerce-functor-D ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0)))
  ⟫ pushS⊗ (tF-coh G₁) (tF-coh G₂)
      (coerce-ν-in ⌈ eraseF G₁ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₁ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D ⌈ eraseF G₁ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₁ A x0))))
      (coerce-ν-in ⌈ eraseF G₂ ⌉F ⟦ A ⟧ᴰ
        (subst (λ Z → ⟦ ⌈ eraseF G₂ ⌉F ⟧F Z) (cohᴰ A)
          (coerce-functor-D ⌈ eraseF G₂ ⌉F ⌈ ⌊ A ⌋ ⌉ (VE0ᴰ G₂ A y0))))
  ⟫ cong₂ _,_ (coerce-νin-erase-D G₁ A x0) (coerce-νin-erase-D G₂ A y0)
  ⟫ sym (cong (λ z → coerce-ν-in (G₁ TT.⊗ G₂) ⟦ A ⟧ᴰ (coerce-functor-D (G₁ TT.⊗ G₂) A z))
              (push× (cohᴰ (TT.⟦ G₁ ⟧T A)) (cohᴰ (TT.⟦ G₂ ⟧T A)) x0 y0))
