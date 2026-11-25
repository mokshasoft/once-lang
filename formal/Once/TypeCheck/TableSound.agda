-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.TableSound — the checker's reading of the generator table
-- is the table (plan 0.151).
--
-- Each decider of `TypeCheck.Table` answers with a row of the Spec's
-- `Morphism` exactly when there is one, and with the morphism the row
-- compiles to: sound (an answer is a row, `d-map`'s answer the least) and
-- complete (a row is found, as the IR the realization gives it).
------------------------------------------------------------------------

module Once.TypeCheck.TableSound where

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (yes; no)

open import Once.Spec.Grade using (Purity; pure; fin; Many; mk-kind)
open import Once.Spec.Type using (Ty; KCtx; Fun; var; Unit; Void; Int; Float; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F; WFFun)
open import Once.Spec.Sub using (_<:ᶜ_; subᶜ-void; subᶜ-var; subᶜ-unit; subᶜ-int; subᶜ-float; subᶜ-arr; subᶜ-*; subᶜ-+; subᶜ-μ; subᶜ-ν)
open import Once.Spec.Core.Syntax using (Defs; Tm)
open import Once.Spec.Core.Derived using (𝕋)
open import Once.Spec.Surface.Generators
open import Once.Type.DecEq using (_≟T_)
open import Once.Type.Sub using (⊑π-refl)
open import Once.Functor.Decide using (wfFun?)
open import Once.TypeCheck.DeciderComplete using (wfFun?-complete-at)
open import Once.Surface.Map using (Map)
open import Once.TypeCheck.Table

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

≟T-refl : ∀ {m} (A : Ty m) → (A ≟T A) ≡ yes refl
≟T-refl A with A ≟T A
... | yes refl = refl
... | no ¬p    = ⊥-elim (¬p refl)

<:ᶜ-refl : ∀ {m} (A : Ty m) → A <:ᶜ A
<:ᶜ-refl (var i)              = subᶜ-var
<:ᶜ-refl Unit                 = subᶜ-unit
<:ᶜ-refl Void                 = subᶜ-void
<:ᶜ-refl Int                  = subᶜ-int
<:ᶜ-refl Float                = subᶜ-float
<:ᶜ-refl (A ⇒[ mk-kind q π ] B) = subᶜ-arr (<:ᶜ-refl B) (⊑π-refl π)
<:ᶜ-refl (A * B)              = subᶜ-* (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (A + B)              = subᶜ-+ (<:ᶜ-refl A) (<:ᶜ-refl B)
<:ᶜ-refl (μ F)                = subᶜ-μ
<:ᶜ-refl (ν F f)              = subᶜ-ν (⊑π-refl (fin f))

-- Below `Void` is only `Void`.
<:ᶜ-Void : ∀ {m} {B : Ty m} → B <:ᶜ Void → B ≡ Void
<:ᶜ-Void subᶜ-void = refl

module _ {m} {Δ : KCtx m} {s} {S : Defs s} {n : _} where

  Mor : Gen → Ty m → Purity → Ty m → Set
  Mor g A π B = Σ[ k ∈ IsMap (kind g) ] Σ[ t ∈ Tm S m n ] Morphism {S = S} Δ {n = n} g k A π B t

  ------------------------------------------------------------------------
  -- From a domain
  ------------------------------------------------------------------------

  -- What `mapFrom?` answers.
  record FromOK (g : Gen) (A : Ty m) (π : Purity) (B : Ty m) (mI : Map A B) : Set where
    field
      from  : FromDomain (kind g)
      row   : Mor g A π B
      ir    : morphMap (proj₂ (proj₂ row)) ≡ mI
      least : ∀ {k′ B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} g k′ A π B′ t′ → B <:ᶜ B′

  private
    -- every row of the fixed-codomain maps has one codomain
    c-id : ∀ {k′ T π B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} id k′ T π B′ t′ → T ≡ B′
    c-id m-id = refl
    c-fst : ∀ {k′ X Y π B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} fst k′ (X * Y) π B′ t′ → X ≡ B′
    c-fst m-fst = refl
    c-snd : ∀ {k′ X Y π B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} snd k′ (X * Y) π B′ t′ → Y ≡ B′
    c-snd m-snd = refl
    c-terminal : ∀ {k′ A π B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} terminal k′ A π B′ t′ → Unit ≡ B′
    c-terminal m-terminal = refl
    c-apply : ∀ {k′ X ρ Y π B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} apply k′ ((X ⇒[ mk-kind Many ρ ] Y) * X) π B′ t′ → 𝕋 ρ Y ≡ B′
    c-apply m-apply = refl
    c-Out : ∀ {k′ F f π B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} Out k′ (ν F f) π B′ t′ → 𝕋 (fin f) (⟦ F ⟧F (ν F f)) ≡ B′
    c-Out (m-Out _) = refl


    to-ᶜ : ∀ {B B′ : Ty m} → B ≡ B′ → B <:ᶜ B′
    to-ᶜ {B} refl = <:ᶜ-refl B


  private
    fstS : ∀ {A : Ty m} π (v : ProdV A) {B mI} → mapFrom?-fst v ≡ just (B , mI) → FromOK fst A π B mI
    fstS π (prod-at X Y) refl = record { from = fd-domain ; row = is-map , _ , m-fst ; ir = refl ; least = λ mo′ → to-ᶜ (c-fst mo′) }
    fstS π prod-other ()
    sndS : ∀ {A : Ty m} π (v : ProdV A) {B mI} → mapFrom?-snd v ≡ just (B , mI) → FromOK snd A π B mI
    sndS π (prod-at X Y) refl = record { from = fd-domain ; row = is-map , _ , m-snd ; ir = refl ; least = λ mo′ → to-ᶜ (c-snd mo′) }
    sndS π prod-other ()
    initialS : ∀ (A : Ty m) π (d : Relation.Nullary.Dec (A ≡ Void)) {B mI} → mapFrom?-initial A d ≡ just (B , mI) → FromOK initial A π B mI
    initialS .Void π (yes refl) refl = record { from = fd-both ; row = is-map , _ , m-initial ; ir = refl ; least = λ _ → subᶜ-void }
    initialS A π (no _) ()
    applyAtS : ∀ (X : Ty m) ρ (Y : Ty m) {X′ : Ty m} π (d : Relation.Nullary.Dec (X ≡ X′)) {B mI}
             → mapFrom?-apply-at X ρ Y d ≡ just (B , mI) → FromOK apply ((X ⇒[ mk-kind Many ρ ] Y) * X′) π B mI
    applyAtS X ρ Y π (yes refl) refl = record { from = fd-domain ; row = is-map , _ , m-apply ; ir = refl ; least = λ mo′ → to-ᶜ (c-apply mo′) }
    applyAtS X ρ Y π (no _) ()
    applyS : ∀ {A : Ty m} π (v : ApplyV A) {B mI} → mapFrom?-apply v ≡ just (B , mI) → FromOK apply A π B mI
    applyS π (apply-at X ρ Y X′) e = applyAtS X ρ Y π (X ≟T X′) e
    applyS π apply-other ()
    outWfS : ∀ (F : Fun m) f π (mw : Maybe (WFFun Δ F)) {B mI} → mapFrom?-Out-wf {Δ = Δ} F f mw ≡ just (B , mI) → FromOK Out (ν F f) π B mI
    outWfS F f π (just w) refl = record { from = fd-domain ; row = is-map , _ , m-Out w ; ir = refl ; least = λ mo′ → to-ᶜ (c-Out mo′) }
    outWfS F f π nothing ()
    outS : ∀ {A : Ty m} π (v : NuV A) {B mI} → mapFrom?-Out Δ v ≡ just (B , mI) → FromOK Out A π B mI
    outS π (nu-at F f) e = outWfS F f π (wfFun? Δ F) e
    outS π nu-other ()

  mapFrom?-sound : ∀ g (A : Ty m) (π : Purity) {B mI} → mapFrom? Δ g A ≡ just (B , mI) → FromOK g A π B mI
  mapFrom?-sound id A π refl =
    record { from = fd-both ; row = is-map , _ , m-id ; ir = refl ; least = λ mo′ → to-ᶜ (c-id mo′) }
  mapFrom?-sound fst A π e = fstS π (prodV A) e
  mapFrom?-sound snd A π e = sndS π (prodV A) e
  mapFrom?-sound terminal A π refl =
    record { from = fd-domain ; row = is-map , _ , m-terminal ; ir = refl ; least = λ mo′ → to-ᶜ (c-terminal mo′) }
  mapFrom?-sound initial A π e = initialS A π (A ≟T Void) e
  mapFrom?-sound apply A π e = applyS π (applyV A) e
  mapFrom?-sound Out A π e = outS π (nuV A) e
  mapFrom?-sound compose A π ()
  mapFrom?-sound pair A π ()
  mapFrom?-sound inl A π ()
  mapFrom?-sound inr A π ()
  mapFrom?-sound case A π ()
  mapFrom?-sound curry A π ()
  mapFrom?-sound In A π ()
  mapFrom?-sound cata A π ()
  mapFrom?-sound ana A π ()
  mapFrom?-sound unit A π ()
  mapFrom?-sound toFloat A π ()

  -- `fst`, `snd`, `apply`, `Out` at a domain of another shape: no answer.
  -- (Covered by the views' `other` cases reducing to `nothing`.)

  mapFrom?-complete : ∀ {g k A π B} {t : Tm S m n} → FromDomain (kind g) → (mo : Morphism {S = S} Δ {n = n} g k A π B t)
                    → (∀ {k′ B′} {t′ : Tm S m n} → Morphism {S = S} Δ {n = n} g k′ A π B′ t′ → B <:ᶜ B′)
                    → mapFrom? Δ g A ≡ just (B , morphMap mo)
  mapFrom?-complete fd m-id       _ = refl
  mapFrom?-complete fd m-fst      _ = refl
  mapFrom?-complete fd m-snd      _ = refl
  mapFrom?-complete fd m-terminal _ = refl
  mapFrom?-complete fd m-initial least with <:ᶜ-Void (least (m-initial {A = Void}))
  ... | refl rewrite ≟T-refl {m} Void = refl
  mapFrom?-complete fd (m-apply {A = X}) _ rewrite ≟T-refl X = refl
  mapFrom?-complete fd (m-Out {F = F} w) _ rewrite wfFun?-complete-at w = refl

  ------------------------------------------------------------------------
  -- To a codomain (at pure)
  ------------------------------------------------------------------------

  record ToOK (g : Gen) (A B : Ty m) (mI : Map A B) : Set where
    field
      to  : FromCodomain (kind g)
      row : Mor g A pure B
      ir  : morphMap (proj₂ (proj₂ row)) ≡ mI

  private
    inlS : ∀ {B : Ty m} (v : SumV B) {A mI} → mapTo?-inl v ≡ just (A , mI) → ToOK inl A B mI
    inlS (sum-at X Y) refl = record { to = fc-codomain ; row = is-map , _ , m-inl ; ir = refl }
    inlS sum-other ()
    inrS : ∀ {B : Ty m} (v : SumV B) {A mI} → mapTo?-inr v ≡ just (A , mI) → ToOK inr A B mI
    inrS (sum-at X Y) refl = record { to = fc-codomain ; row = is-map , _ , m-inr ; ir = refl }
    inrS sum-other ()
    inWfS : ∀ (F : Fun m) (mw : Maybe (WFFun Δ F)) {A mI} → mapTo?-In-wf {Δ = Δ} F mw ≡ just (A , mI) → ToOK In A (μ F) mI
    inWfS F (just w) refl = record { to = fc-codomain ; row = is-map , _ , m-In w ; ir = refl }
    inWfS F nothing ()
    inS : ∀ {B : Ty m} (v : MuV B) {A mI} → mapTo?-In Δ v ≡ just (A , mI) → ToOK In A B mI
    inS (mu-at F) e = inWfS F (wfFun? Δ F) e
    inS mu-other ()

  mapTo?-sound : ∀ g (B : Ty m) {A mI} → mapTo? Δ g B ≡ just (A , mI) → ToOK g A B mI
  mapTo?-sound id B refl          = record { to = fc-both ; row = is-map , _ , m-id ; ir = refl }
  mapTo?-sound inl B e            = inlS (sumV B) e
  mapTo?-sound inr B e            = inrS (sumV B) e
  mapTo?-sound initial B refl     = record { to = fc-both ; row = is-map , _ , m-initial ; ir = refl }
  mapTo?-sound In B e             = inS (muV B) e
  mapTo?-sound compose B ()
  mapTo?-sound fst B ()
  mapTo?-sound snd B ()
  mapTo?-sound terminal B ()
  mapTo?-sound pair B ()
  mapTo?-sound case B ()
  mapTo?-sound apply B ()
  mapTo?-sound curry B ()
  mapTo?-sound cata B ()
  mapTo?-sound Out B ()
  mapTo?-sound ana B ()
  mapTo?-sound unit B ()
  mapTo?-sound toFloat B ()

  mapTo?-complete : ∀ {g k A B} {t : Tm S m n} → FromCodomain (kind g) → (mo : Morphism {S = S} Δ {n = n} g k A pure B t)
                  → mapTo? Δ g B ≡ just (A , morphMap mo)
  mapTo?-complete fc m-id      = refl
  mapTo?-complete fc m-inl     = refl
  mapTo?-complete fc m-inr     = refl
  mapTo?-complete fc m-initial = refl
  mapTo?-complete fc (m-In {F = F} w) rewrite wfFun?-complete-at w = refl

  ------------------------------------------------------------------------
  -- At an arrow
  ------------------------------------------------------------------------

  record AtOK (g : Gen) (A : Ty m) (π : Purity) (B : Ty m) (mI : Map A B) : Set where
    field
      row : Mor g A π B
      ir  : morphMap (proj₂ (proj₂ row)) ≡ mI

  private
    viaFrom : ∀ g (A : Ty m) π (B : Ty m) {mI} → mapAt?-by-dom {A = A} B (mapFrom? Δ g A) ≡ just mI → AtOK g A π B mI
    viaFrom g A π B e with mapFrom? Δ g A in eq
    viaFrom g A π B () | nothing
    viaFrom g A π B e  | just (B′ , m′) with B′ ≟T B
    viaFrom g A π B refl | just (.B , m′) | yes refl =
      let ok = mapFrom?-sound g A π eq in record { row = FromOK.row ok ; ir = FromOK.ir ok }
    viaFrom g A π B () | just (B′ , m′) | no _

    viaTo : ∀ g (A : Ty m) π (B : Ty m) {mI} → mapAt?-by-cod A {B = B} (mapTo? Δ g B) ≡ just mI → AtOK g A π B mI
    viaTo g A π B e with mapTo? Δ g B in eq
    viaTo g A π B () | nothing
    viaTo g A π B e  | just (A′ , m′) with A′ ≟T A
    viaTo g A π B refl | just (.A , m′) | yes refl = go (mapTo?-sound g B eq)
      where
        -- a codomain-fixed map's row at pure is a row at every grade
        regrade : ∀ {g k A B} {t : Tm S m n} → Morphism {S = S} Δ {n = n} g k A pure B t → Mor g A π B
        regrade m-id      = is-map , _ , m-id
        regrade m-inl     = is-map , _ , m-inl
        regrade m-inr     = is-map , _ , m-inr
        regrade m-initial = is-map , _ , m-initial
        regrade m-fst     = is-map , _ , m-fst
        regrade m-snd     = is-map , _ , m-snd
        regrade m-terminal = is-map , _ , m-terminal
        regrade m-apply   = is-map , _ , m-apply
        regrade (m-In w)  = is-map , _ , m-In w
        regrade (m-Out w) = is-map , _ , m-Out w
        same : ∀ {g k A B} {t : Tm S m n} (mo : Morphism {S = S} Δ {n = n} g k A pure B t)
             → morphMap (proj₂ (proj₂ (regrade mo))) ≡ morphMap mo
        same m-id = refl
        same m-inl = refl
        same m-inr = refl
        same m-initial = refl
        same m-fst = refl
        same m-snd = refl
        same m-terminal = refl
        same m-apply = refl
        same (m-In w) = refl
        same (m-Out w) = refl
        go : ToOK g A B m′ → AtOK g A π B m′
        go ok = record { row = regrade (proj₂ (proj₂ (ToOK.row ok))) ; ir = trans (same (proj₂ (proj₂ (ToOK.row ok)))) (ToOK.ir ok) }
    viaTo g A π B () | just (A′ , m′) | no _

  private
    atInitial : ∀ (A : Ty m) π (B : Ty m) (d : Relation.Nullary.Dec (A ≡ Void)) {mI} → mapAt?-initial A {B = B} d ≡ just mI → AtOK initial A π B mI
    atInitial .Void π B (yes refl) refl = record { row = is-map , _ , m-initial ; ir = refl }
    atInitial A π B (no _) ()

  mapAt?-sound : ∀ g (A : Ty m) (π : Purity) (B : Ty m) {mI} → mapAt? Δ g A B ≡ just mI → AtOK g A π B mI
  mapAt?-sound initial A π B e = atInitial A π B (A ≟T Void) e
  mapAt?-sound inl      A π B e = viaTo inl A π B e
  mapAt?-sound inr      A π B e = viaTo inr A π B e
  mapAt?-sound In       A π B e = viaTo In A π B e
  mapAt?-sound id       A π B e = viaFrom id A π B e
  mapAt?-sound fst      A π B e = viaFrom fst A π B e
  mapAt?-sound snd      A π B e = viaFrom snd A π B e
  mapAt?-sound terminal A π B e = viaFrom terminal A π B e
  mapAt?-sound apply    A π B e = viaFrom apply A π B e
  mapAt?-sound Out      A π B e = viaFrom Out A π B e
  mapAt?-sound compose  A π B ()
  mapAt?-sound pair     A π B ()
  mapAt?-sound case     A π B ()
  mapAt?-sound curry    A π B ()
  mapAt?-sound cata     A π B ()
  mapAt?-sound ana      A π B ()
  mapAt?-sound unit     A π B ()
  mapAt?-sound toFloat  A π B ()

  mapAt?-complete : ∀ {g k A π B} {t : Tm S m n} (mo : Morphism {S = S} Δ {n = n} g k A π B t)
                  → mapAt? Δ g A B ≡ just (morphMap mo)
  mapAt?-complete {A = A} m-id rewrite ≟T-refl A = refl
  mapAt?-complete {B = B} m-fst rewrite ≟T-refl B = refl
  mapAt?-complete {B = B} m-snd rewrite ≟T-refl B = refl
  mapAt?-complete m-terminal rewrite ≟T-refl {m} Unit = refl
  mapAt?-complete {A = A} m-inl rewrite ≟T-refl A = refl
  mapAt?-complete {A = A} m-inr rewrite ≟T-refl A = refl
  mapAt?-complete m-initial rewrite ≟T-refl {m} Void = refl
  mapAt?-complete {B = B} (m-apply {A = X}) rewrite ≟T-refl X | ≟T-refl B = refl
  mapAt?-complete {A = A} (m-In {F = F} w) rewrite wfFun?-complete-at w | ≟T-refl A = refl
  mapAt?-complete {B = B} (m-Out {F = F} w) rewrite wfFun?-complete-at w | ≟T-refl B = refl
