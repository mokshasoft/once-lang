-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.GenInv — a generator's core typing read back
-- (plan 0.121 §3.6, F5).
--
-- Each generator is a core term (`Spec.Core.Derived`). A typing of it gives
-- its type — a closed one's from its own annotations, a combinator's from its
-- arguments' — and, for a combinator, its arguments' typings at usages the
-- whole one bounds (an argument moved under a binder is strengthened back).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Data.Nat
open import Once.Spec.Signature using (Signature)
import Once.Spec.Core.Syntax as SC
import Once.Spec.Type as ST

module Once.Adequacy.SpecFront.GenInv (Σ : Signature) {s : ℕ} (S : SC.Defs s) {m : ℕ} {Δ : ST.KCtx m} where

open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; mk-kind; Finite; fin; pureᶠ; actᶠ)
open import Once.Spec.Type using (Ty; Fun; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Context using (Ctx; _▸_; lookup; Usage; _∷_; _+ᵘ_; _*ᵘ_; _⊑ᵘ_)
open import Once.Spec.Core.Syntax using (Tm; wk)
open import Once.Spec.Core.Typing Σ S using (_⊩_⊢[_]_∷_!_)
open import Once.Spec.Core.Derived
open import Once.Adequacy.SpecFront.CoreInv Σ S {Δ = Δ}

private
  _⇒⟨_⟩_ : Ty m → Purity → Ty m → Ty m
  A ⇒⟨ π ⟩ B = A ⇒[ mk-kind Many π ] B

  arr-inj : ∀ {A B A′ B′ : Ty m} {q q′ π π′}
          → (A ⇒[ mk-kind q π ] B) ≡ (A′ ⇒[ mk-kind q′ π′ ] B′) → (A ≡ A′) × (q ≡ q′) × (π ≡ π′) × (B ≡ B′)
  arr-inj refl = refl , refl , refl , refl

  prod-inj : ∀ {A B A′ B′ : Ty m} → (A * B) ≡ (A′ * B′) → (A ≡ A′) × (B ≡ B′)
  prod-inj refl = refl , refl

  sum-inj : ∀ {A B A′ B′ : Ty m} → (A + B) ≡ (A′ + B′) → (A ≡ A′) × (B ≡ B′)
  sum-inj refl = refl , refl

  ν-inj : ∀ {F F′ : Fun m} {f f′} → ν F f ≡ ν F′ f′ → (F ≡ F′) × (f ≡ f′)
  ν-inj refl = refl , refl

  -- a lambda's type: its annotations, and its body's
  lam-ty : ∀ {n} {Γ : Ctx m n} {Φ A q π t X π₀} (d : Δ ⊩ Γ ⊢[ Φ ] SC.lam A q π t ∷ X ! π₀)
         → X ≡ A ⇒[ mk-kind q π ] ILam.B (inv-lam d)
  lam-ty d = ILam.ty (inv-lam d)

------------------------------------------------------------------------
-- The closed generators: their types
------------------------------------------------------------------------

module _ {n : ℕ} {Γ : Ctx m n} {Φ : Usage n} {X : Ty m} {π₀ : Purity} where

  idᶜ-ty : ∀ {A π} → Δ ⊩ Γ ⊢[ Φ ] idᶜ A π ∷ X ! π₀ → X ≡ A ⇒⟨ π ⟩ A
  idᶜ-ty d = trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (proj₁ (inv-var (ILam.body (inv-lam d)))))

  terminalᶜ-ty : ∀ {A π} → Δ ⊩ Γ ⊢[ Φ ] terminalᶜ A π ∷ X ! π₀ → X ≡ A ⇒⟨ π ⟩ Unit
  terminalᶜ-ty d = trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (inv-unit (ILam.body (inv-lam d))))

  initialᶜ-ty : ∀ {A π} → Δ ⊩ Γ ⊢[ Φ ] initialᶜ A π ∷ X ! π₀ → X ≡ Void ⇒⟨ π ⟩ A
  initialᶜ-ty d = trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (inv-absurd (ILam.body (inv-lam d))))

  fstᶜ-ty : ∀ {A B π} → Δ ⊩ Γ ⊢[ Φ ] fstᶜ A B π ∷ X ! π₀ → X ≡ (A * B) ⇒⟨ π ⟩ A
  fstᶜ-ty d =
    let (Y , _ , _ , dv , _) = inv-fst (ILam.body (inv-lam d))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (proj₁ (prod-inj (proj₁ (inv-var dv)))))

  sndᶜ-ty : ∀ {A B π} → Δ ⊩ Γ ⊢[ Φ ] sndᶜ A B π ∷ X ! π₀ → X ≡ (A * B) ⇒⟨ π ⟩ B
  sndᶜ-ty d =
    let (Y , _ , _ , dv , _) = inv-snd (ILam.body (inv-lam d))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (proj₂ (prod-inj (proj₁ (inv-var dv)))))

  inlᶜ-ty : ∀ {A B π} → Δ ⊩ Γ ⊢[ Φ ] inlᶜ A B π ∷ X ! π₀ → X ≡ A ⇒⟨ π ⟩ (A + B)
  inlᶜ-ty d =
    let (A₀ , e , _ , _ , dv) = inv-inl (ILam.body (inv-lam d))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (trans e (cong (_+ _) (proj₁ (inv-var dv)))))

  inrᶜ-ty : ∀ {A B π} → Δ ⊩ Γ ⊢[ Φ ] inrᶜ A B π ∷ X ! π₀ → X ≡ B ⇒⟨ π ⟩ (A + B)
  inrᶜ-ty d =
    let (B₀ , e , _ , _ , dv) = inv-inr (ILam.body (inv-lam d))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (trans e (cong (_ +_) (proj₁ (inv-var dv)))))

  applyᶜ-ty : ∀ {A B} → Δ ⊩ Γ ⊢[ Φ ] applyᶜ A B ∷ X ! π₀ → X ≡ ((A ⇒⟨ pure ⟩ B) * A) ⇒⟨ pure ⟩ B
  applyᶜ-ty d =
    let r  = inv-app (ILam.body (inv-lam d))
        (Y , _ , _ , dv , _) = inv-fst (IApp.df r)
        (_ , _ , _ , cod) = arr-inj (proj₁ (prod-inj (proj₁ (inv-var dv))))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) cod)

  applyEffᶜ-ty : ∀ {π A B} → Δ ⊩ Γ ⊢[ Φ ] applyEffᶜ π A B ∷ X ! π₀ → X ≡ ((A ⇒⟨ π ⟩ B) * A) ⇒⟨ pure ⟩ (Unit ⇒⟨ π ⟩ B)
  applyEffᶜ-ty d =
    let inner = ILam.body (inv-lam d)
        r  = inv-app (ILam.body (inv-lam inner))
        (Y , _ , _ , dv , _) = inv-fst (IApp.df r)
        (_ , _ , _ , cod) = arr-inj (proj₁ (prod-inj (proj₁ (inv-var dv))))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (trans (lam-ty inner) (cong (λ C → Unit ⇒⟨ _ ⟩ C) cod)))

  inᶜ-ty : ∀ {F} → Δ ⊩ Γ ⊢[ Φ ] inᶜ F ∷ X ! π₀ → X ≡ (⟦ F ⟧F (μ F)) ⇒⟨ pure ⟩ μ F
  inᶜ-ty d = trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (inv-roll (ILam.body (inv-lam d))))

  outᶜ-ty : ∀ {F} → Δ ⊩ Γ ⊢[ Φ ] outᶜ F ∷ X ! π₀ → X ≡ (ν F pureᶠ) ⇒⟨ pure ⟩ ⟦ F ⟧F (ν F pureᶠ)
  outᶜ-ty d =
    let (F₁ , f₁ , e , _ , _ , dv) = inv-out (ILam.body (inv-lam d))
        (eF , ef) = ν-inj (proj₁ (inv-var dv))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B) (trans e (cong₂ (λ G g → ⟦ G ⟧F (ν G g)) eF ef)))

  outActᶜ-ty : ∀ {F} → Δ ⊩ Γ ⊢[ Φ ] outActᶜ F ∷ X ! π₀ → X ≡ (ν F actᶠ) ⇒⟨ pure ⟩ (Unit ⇒⟨ act ⟩ ⟦ F ⟧F (ν F actᶠ))
  outActᶜ-ty d =
    let inner = ILam.body (inv-lam d)
        (F₁ , f₁ , e , _ , _ , dv) = inv-out (ILam.body (inv-lam inner))
        (eF , ef) = ν-inj (proj₁ (inv-var dv))
    in trans (lam-ty d) (cong (λ B → _ ⇒⟨ _ ⟩ B)
         (trans (lam-ty inner) (cong (λ C → Unit ⇒⟨ act ⟩ C) (trans e (cong₂ (λ G g → ⟦ G ⟧F (ν G g)) eF ef)))))

------------------------------------------------------------------------
-- The combinators: their arguments, and their types
------------------------------------------------------------------------

open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-+; ⊑ᵘ-*ʳ; ⊑ᵘ-≡; +ᵘ-comm; One*ᵘ)
open import Once.Spec.Grade using (_≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω; _+q_)

private
  ≤q-refl : ∀ q → q ≤q q
  ≤q-refl Zero = 0≤q
  ≤q-refl One  = 1≤1
  ≤q-refl Many = ω≤ω

  ≤q-+ʳ : ∀ p q → q ≤q p +q q
  ≤q-+ʳ Zero q    = ≤q-refl q
  ≤q-+ʳ One  Zero = 0≤q
  ≤q-+ʳ One  One  = 1≤ω
  ≤q-+ʳ One  Many = ω≤ω
  ≤q-+ʳ Many Zero = 0≤q
  ≤q-+ʳ Many One  = 1≤ω
  ≤q-+ʳ Many Many = ω≤ω

  ⊑-+ʳ : ∀ {k} (Ψ Φ : Usage k) → Φ ⊑ᵘ Ψ +ᵘ Φ
  ⊑-+ʳ Once.Spec.Context.[]      Once.Spec.Context.[]      = Once.Spec.Context.[]
  ⊑-+ʳ (p ∷ Ψ) (q ∷ Φ) = ≤q-+ʳ p q Once.Spec.Context.⊑∷ ⊑-+ʳ Ψ Φ

  ⊑-tail : ∀ {k p q} {Ψ Φ : Usage k} → (p ∷ Ψ) ⊑ᵘ (q ∷ Φ) → Ψ ⊑ᵘ Φ
  ⊑-tail (_ Once.Spec.Context.⊑∷ t) = t

  tailᵘ : ∀ {k} → Usage (Data.Nat.suc k) → Usage k
  tailᵘ (q ∷ Ψ) = Ψ

  ⊑-tailᵘ : ∀ {k} {Ψ Φ : Usage (Data.Nat.suc k)} → Ψ ⊑ᵘ Φ → tailᵘ Ψ ⊑ᵘ tailᵘ Φ
  ⊑-tailᵘ (_ Once.Spec.Context.⊑∷ t) = t

  tail-+* : ∀ {k} (Ψ Ψ′ : Usage (Data.Nat.suc k)) q → tailᵘ (Ψ +ᵘ q *ᵘ Ψ′) ≡ tailᵘ Ψ +ᵘ q *ᵘ tailᵘ Ψ′
  tail-+* (a ∷ Ψ) (b ∷ Ψ′) q = refl

  str-wk : ∀ {k} {Γ′ : Ctx m k} {Y Ψ t A π} → Δ ⊩ (Γ′ ▸ Y) ⊢[ Ψ ] wk t ∷ A ! π → Δ ⊩ Γ′ ⊢[ tailᵘ Ψ ] t ∷ A ! π
  str-wk {Ψ = a ∷ Ψ} d = strengthen-wk d

  -- `Φ₁ + Φ₃ ⊑ Φ` from the two lets' usages
  two-lets : ∀ {k} {Φ Φ₁ Φ₂ Φ₃ Ψ₂ : Usage k} {q} → Φ₂ +ᵘ One *ᵘ Φ₁ ⊑ᵘ Φ → (Ψ₂ +ᵘ q *ᵘ Φ₃) ⊑ᵘ Φ₂
           → Φ₁ +ᵘ q *ᵘ Φ₃ ⊑ᵘ Φ
  two-lets {Φ = Φ} {Φ₁} {Φ₂} {Φ₃} {Ψ₂} {q = q} u₁ u₂ =
    ⊑ᵘ-trans (⊑ᵘ-trans (⊑ᵘ-+ (⊑ᵘ-≡ (sym (One*ᵘ Φ₁))) (⊑ᵘ-trans (⊑-+ʳ Ψ₂ (q *ᵘ Φ₃)) u₂))
                       (⊑ᵘ-≡ (+ᵘ-comm (One *ᵘ Φ₁) Φ₂))) u₁

module _ {n : ℕ} {Γ : Ctx m n} {Φ : Usage n} {X : Ty m} {π₀ : Purity} where

  record Two (f g : Tm S m n) (q : Quantity) : Set where
    field
      {F G}     : Ty m
      {πf πg}   : Purity
      {Φf Φg}   : Usage n
      df        : Δ ⊩ Γ ⊢[ Φf ] f ∷ F ! πf
      dg        : Δ ⊩ Γ ⊢[ Φg ] g ∷ G ! πg
      use       : Φf +ᵘ q *ᵘ Φg ⊑ᵘ Φ

  -- `let f; let wk g; body`: the two arguments, at usages the whole bounds
  lets : ∀ {q f g b} → Δ ⊩ Γ ⊢[ Φ ] SC.let′ One f (SC.let′ q (wk g) b) ∷ X ! π₀
       → Σ[ r ∈ Two f g q ] Σ[ Ψb ∈ Usage (Data.Nat.suc n) ] Σ[ πb ∈ Purity ]
           Δ ⊩ (Γ ▸ Two.F r ▸ Two.G r) ⊢[ q ∷ Ψb ] b ∷ X ! πb
  lets {q} d =
    record { df = ILet.de r₁ ; dg = str-wk (ILet.de r₂)
           ; use = two-lets (ILet.use r₁) (subst (_⊑ᵘ ILet.Φ₂ r₁) (tail-+* (ILet.Φ₂ r₂) (ILet.Φ₁ r₂) q) (⊑-tailᵘ (ILet.use r₂))) }
    , _ , _ , ILet.db r₂
    where
      r₁ = inv-let d
      r₂ = inv-let (ILet.db r₁)

  record One′ (f : Tm S m n) (q : Quantity) : Set where
    field
      {F}  : Ty m
      {πf} : Purity
      {Φf} : Usage n
      df   : Δ ⊩ Γ ⊢[ Φf ] f ∷ F ! πf
      use  : q *ᵘ Φf ⊑ᵘ Φ

  -- `let f; body`
  let1 : ∀ {q f b} → Δ ⊩ Γ ⊢[ Φ ] SC.let′ q f b ∷ X ! π₀
       → Σ[ r ∈ One′ f q ] Σ[ Ψb ∈ Usage n ] Σ[ πb ∈ Purity ] Δ ⊩ (Γ ▸ One′.F r) ⊢[ q ∷ Ψb ] b ∷ X ! πb
  let1 {q} d = record { df = ILet.de r ; use = ⊑ᵘ-trans (⊑-+ʳ (ILet.Φ₂ r) (q *ᵘ ILet.Φ₁ r)) (ILet.use r) } , _ , _ , ILet.db r
    where r = inv-let d

  -- the function variable `i` of a body is the argument at `i`
  private
    fun-at : ∀ {k} {Γ′ : Ctx m k} {Φ′ x Z π′} (i : Fin k)
           → Δ ⊩ Γ′ ⊢[ Φ′ ] SC.app (SC.var i) x ∷ Z ! π′
           → Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] lookup Γ′ i ≡ M ⇒[ mk-kind q πa ] Z
    fun-at i d = let r = inv-app d in _ , _ , _ , sym (proj₁ (inv-var (IApp.df r)))

  compose-inv : ∀ {A π f g} → Δ ⊩ Γ ⊢[ Φ ] composeᶜ A π f g ∷ X ! π₀
              → Σ[ r ∈ Two f g Many ] Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Σ[ C ∈ Ty m ]
                  (Two.F r ≡ M ⇒[ mk-kind q πa ] C) × (X ≡ A ⇒⟨ π ⟩ C)
  compose-inv d =
    let (r , Ψb , πb , db) = lets d
        l = inv-lam db
        (M , q , πa , eF) = fun-at (suc (suc zero)) (ILam.body l)
    in r , M , q , πa , _ , eF , ILam.ty l

  pair-inv : ∀ {A π f g} → Δ ⊩ Γ ⊢[ Φ ] pairᶜ A π f g ∷ X ! π₀
           → Σ[ r ∈ Two f g One ] Σ[ B ∈ Ty m ] Σ[ C ∈ Ty m ]
               (Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Two.F r ≡ M ⇒[ mk-kind q πa ] B)
               × (Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Two.G r ≡ M ⇒[ mk-kind q πa ] C)
               × (X ≡ A ⇒⟨ π ⟩ (B * C))
  pair-inv d =
    let (r , Ψb , πb , db) = lets d
        l = inv-lam db
        p = inv-pair (ILam.body l)
        (M , q , πa , eF) = fun-at (suc (suc zero)) (IPair.da p)
        (M′ , q′ , πa′ , eG) = fun-at (suc zero) (IPair.db p)
    in r , _ , _ , (M , q , πa , eF) , (M′ , q′ , πa′ , eG) , trans (ILam.ty l) (cong (λ Z → _ ⇒⟨ _ ⟩ Z) (IPair.ty p))

  case-inv : ∀ {A B π f g} → Δ ⊩ Γ ⊢[ Φ ] caseᶜ A B π f g ∷ X ! π₀
           → Σ[ r ∈ Two f g One ] Σ[ C ∈ Ty m ]
               (Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Two.F r ≡ M ⇒[ mk-kind q πa ] C)
               × (Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Two.G r ≡ M ⇒[ mk-kind q πa ] C)
               × (X ≡ (A + B) ⇒⟨ π ⟩ C)
  case-inv d =
    let (r , Ψb , πb , db) = lets d
        l = inv-lam db
        c = inv-case (ILam.body l)
        (M , q , πa , eF) = fun-at (suc (suc (suc zero))) (ICase.dl c)
        (M′ , q′ , πa′ , eG) = fun-at (suc (suc zero)) (ICase.dr c)
    in r , _ , (M , q , πa , eF) , (M′ , q′ , πa′ , eG) , ILam.ty l

  curry-inv : ∀ {A B π₁ π f} → Δ ⊩ Γ ⊢[ Φ ] curryᶜ A B π₁ π f ∷ X ! π₀
            → Σ[ r ∈ One′ f One ] Σ[ M ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Σ[ C ∈ Ty m ]
                (One′.F r ≡ M ⇒[ mk-kind q πa ] C) × (X ≡ A ⇒⟨ π₁ ⟩ (B ⇒⟨ π ⟩ C))
  curry-inv d =
    let (r , Ψb , πb , db) = let1 d
        l  = inv-lam db
        l′ = inv-lam (ILam.body l)
        (M , q , πa , eF) = fun-at (suc (suc zero)) (ILam.body l′)
    in r , M , q , πa , _ , eF , trans (ILam.ty l) (cong (λ Z → _ ⇒⟨ _ ⟩ Z) (ILam.ty l′))

  cata-inv : ∀ {F π a} → Δ ⊩ Γ ⊢[ Φ ] cataᶜ F π a ∷ X ! π₀
           → Σ[ r ∈ One′ a Many ] Σ[ A ∈ Ty m ] Σ[ π₁ ∈ Purity ]
               (One′.F r ≡ ⟦ F ⟧F A ⇒[ mk-kind Many π₁ ] A) × (X ≡ μ F ⇒⟨ π ⟩ A)
  cata-inv d =
    let (r , Ψb , πb , db) = let1 d
        l = inv-lam db
        (π₁ , _ , _ , dv) = inv-fold (ILam.body l)
    in r , _ , π₁ , sym (proj₁ (inv-var dv)) , ILam.ty l

  loop-inv : ∀ {A c} → Δ ⊩ Γ ⊢[ Φ ] loopᶜ A c ∷ X ! π₀
           → Σ[ r ∈ One′ c Many ] Σ[ A₁ ∈ Ty m ] Σ[ B ∈ Ty m ]
               (One′.F r ≡ A₁ ⇒[ mk-kind Many act ] (B + A₁)) × (X ≡ A ⇒⟨ eff ⟩ B)
  loop-inv d =
    let (r , Ψb , πb , db) = let1 d
        l = inv-lam db
        (A₁ , _ , _ , dv) = inv-iter (ILam.body l)
    in r , A₁ , _ , sym (proj₁ (inv-var dv)) , ILam.ty l

  ana-inv : ∀ {F A π c} → Δ ⊩ Γ ⊢[ Φ ] anaᶜ F A π c ∷ X ! π₀
          → Σ[ f ∈ Finite ] Σ[ A₁ ∈ Ty m ] Σ[ πc ∈ Purity ] Σ[ Φc ∈ Usage n ]
              (Δ ⊩ Γ ⊢[ Φc ] c ∷ A₁ ⇒[ mk-kind Many (fin f) ] ⟦ F ⟧F A₁ ! πc)
              × (Many *ᵘ Φc ⊑ᵘ Φ) × (X ≡ A ⇒⟨ π ⟩ ν F f)
  ana-inv d =
    let l = inv-lam d
        (f , A₁ , e , πc , Φk , Φa , dk , u) = inv-unfold (ILam.body l)
    in f , A₁ , πc , tailᵘ Φk , str-wk dk
       , ⊑ᵘ-trans (⊑ᵘ-trans (⊑-+ʳ′ (Many *ᵘ tailᵘ Φk) (tailᵘ Φa)) (subst (_⊑ᵘ ILam.Ψ l) (tail-+′ Φk Φa) (⊑-tailᵘ u))) (ILam.use l)
       , trans (ILam.ty l) (cong (λ Z → _ ⇒⟨ _ ⟩ Z) e)
    where
      ⊑-+ʳ′ : ∀ {k} (Ψ Φ′ : Usage k) → Ψ ⊑ᵘ Ψ +ᵘ Φ′
      ⊑-+ʳ′ Ψ Φ′ = ⊑ᵘ-trans (⊑-+ʳ Φ′ Ψ) (⊑ᵘ-≡ (+ᵘ-comm Φ′ Ψ))
      tail-+′ : ∀ {k} (Ψ Ψ′ : Usage (Data.Nat.suc k)) → tailᵘ (Many *ᵘ Ψ +ᵘ Ψ′) ≡ Many *ᵘ tailᵘ Ψ +ᵘ tailᵘ Ψ′
      tail-+′ (a ∷ Ψ) (b ∷ Ψ′) = refl

  effApp-inv : ∀ {π f x} → Δ ⊩ Γ ⊢[ Φ ] effAppᶜ π f x ∷ X ! π₀
             → Σ[ A ∈ Ty m ] Σ[ q ∈ Quantity ] Σ[ πa ∈ Purity ] Σ[ B ∈ Ty m ]
               Σ[ πf ∈ Purity ] Σ[ πx ∈ Purity ] Σ[ Φf ∈ Usage n ] Σ[ Φx ∈ Usage n ]
                 (Δ ⊩ Γ ⊢[ Φf ] f ∷ A ⇒[ mk-kind q πa ] B ! πf) × (Δ ⊩ Γ ⊢[ Φx ] x ∷ A ! πx)
                 × (Φf +ᵘ q *ᵘ Φx ⊑ᵘ Φ) × (X ≡ Unit ⇒⟨ π ⟩ B)
  effApp-inv d =
    let l = inv-lam d
        a = inv-app (ILam.body l)
    in _ , _ , _ , _ , _ , _ , _ , _ , str-wk (IApp.df a) , str-wk (IApp.dx a)
       , ⊑ᵘ-trans (subst (_⊑ᵘ ILam.Ψ l) (tail-+* (IApp.Φ₁ a) (IApp.Φ₂ a) (IApp.q a)) (⊑-tailᵘ (IApp.use a))) (ILam.use l)
       , ILam.ty l
