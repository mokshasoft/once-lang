-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.TypeCheck.Witness — what the checker proves of an accepted
-- expression: the Spec's derivation of it, with its usage (plan 0.122
-- §2b-3, stage d).
--
-- `W⇒ L e A t Ψ` is a derivation of the Spec's surface judgment
-- (`e` synthesizes `A` and names `t` in the locals `L`) annotated with
-- the usage `Ψ` (`TypeCheck.Use`). One smart constructor per Spec rule
-- builds it from its premises' witnesses; each takes the rule's own
-- arguments and the usage facts `Use` carries.
------------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Core.Syntax using (Defs)
open import Once.Spec.Type using (KCtx)

module Once.TypeCheck.Witness (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) {m : ℕ} (Δ : KCtx m) where

open import Data.Bool using (true)
open import Data.Integer using (ℤ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.String using (String)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Many; One; Purity; pure; act; eff; Finite; fin; pureᶠ; actᶠ; mk-kind; _⊑π_; EffGrade)
open import Once.Spec.Type using (Ty; Type; TySub; Respects; WFFun; Occurs; _⟨_⟩; _⇒[_]_; _*_; _+_; Unit; Void; Int; Float; μ; ν; ⟦_⟧F)
open import Once.Spec.Sub using (_<:_; _⊔_≔_)
open import Once.Spec.Signature using (_∶_; ⌜_⌝ᵈ)
open import Once.Spec.Name using (gen; NotGenerator)
open import Once.Spec.Float.Decimal using (decimalOf; negate)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Core.Syntax
  using (Tm; lit; lit-int; lit-float; unit; var; sigop; ref; pair; prim; p-neg; p-i2f; let′; case; coerce; app; lam;
         _!!_; module Schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Derived
open import Once.Spec.Context using (Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_)
open import Once.Internal.Context using (_⊔ᵘ_)
open import Once.Internal.Type using (wk₀)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; _▹_∶_; _∋_⦂_at_; SpecialHead; IntArith; FloatArith; Compare; _⇒⟨_⟩_; ↑)
open import Once.TypeCheck.Use Σ S nm Δ

------------------------------------------------------------------------
-- The witnesses
------------------------------------------------------------------------

W⇒ : ∀ {n} → Locals m n → Expr → Ty m → Tm S m n → Usage n → Set
W⇒ L e A t Ψ = Σ[ d ∈ L ⊢ e ⇒ A ↝ t ] Use⇒ d Ψ

W⇐ : ∀ {n} → Locals m n → Expr → Ty m → Tm S m n → Usage n → Set
W⇐ L e A t Ψ = Σ[ d ∈ L ⊢ e ⇐ A ↝ t ] Use⇐ d Ψ

W↦ : ∀ {n} → Locals m n → Expr → Ty m → Purity → Ty m → Tm S m n → Usage n → Set
W↦ L e A π B t Ψ = Σ[ d ∈ L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t ] Use↦ d Ψ

module _ {n} {L : Locals m n} where

  ------------------------------------------------------------------
  -- Synthesis
  ------------------------------------------------------------------

  w-int : ∀ (i : ℤ) → W⇒ L (RInt i) Int (lit (lit-int i)) zeroUsage
  w-int i = SU.s-int i , u-int

  w-float : ∀ i f l → W⇒ L (RFloat i f l) Float (lit (lit-float (decimalOf i f l))) zeroUsage
  w-float i f l = SU.s-float i f l , u-float

  w-unit : W⇒ L RUnit Unit unit zeroUsage
  w-unit = SU.s-unit , u-unit

  w-unit-g : W⇒ L (RResolved (gen "unit")) Unit unit zeroUsage
  w-unit-g = SU.s-unit-g , u-unit-g

  w-var : ∀ {x A i} → L ∋ x ⦂ A at i → W⇒ L (RVar x) A (var i) (singleUse i One)
  w-var v = SU.s-var v , u-var

  w-sigop : ∀ {c t} → NotGenerator c → (mem : (c ∶ t) ∈ Σ) {T : Type} → IsConcrete T → ⌜ t ⌝ᵈ ≡ wk₀ {m} T
          → W⇒ L (RResolved c) ⌜ t ⌝ᵈ (sigop c t) zeroUsage
  w-sigop ng mem k e = SU.s-sigop ng mem , u-sigop k e

  w-def : ∀ {c} (d : Fin s) → nm d ≡ c → (τ : TySub (arity (S !! d)) m) → arity (S !! d) ≡ 0
        → W⇒ L (RResolved c) (type (S !! d) ⟨ τ ⟩) (ref d τ) zeroUsage
  w-def d e τ a = SU.s-def d e τ a , u-def

  w-annot : ∀ {e T t Ψ} → W⇐ L e (↑ T) t Ψ → W⇒ L (RAnnot e T) (↑ T) t Ψ
  w-annot (d , u) = SU.s-annot d , u-annot u

  w-pair : ∀ {a b A B ta tb Ψ₁ Ψ₂} → W⇒ L a A ta Ψ₁ → W⇒ L b B tb Ψ₂ → W⇒ L (RPair a b) (A * B) (pair ta tb) (Ψ₁ +ᵘ Ψ₂)
  w-pair (da , ua) (db , ub) = SU.s-pair da db , u-pair ua ub

  w-neg : ∀ {e t Ψ} → W⇒ L e Int t Ψ → W⇒ L (RNeg e) Int (prim p-neg t) Ψ
  w-neg (d , u) = SU.s-neg d , u-neg u

  w-neg-float : ∀ i f l → W⇒ L (RNeg (RFloat i f l)) Float (lit (lit-float (negate (decimalOf i f l)))) zeroUsage
  w-neg-float i f l = SU.s-neg-float i f l , u-neg-float

  w-let : ∀ {x e₁ e₂ A B t₁ t₂ Ψ₁ Ψ₂} (q : Quantity)
        → W⇒ L e₁ A t₁ Ψ₁ → W⇒ (L ▹ x ∶ A) e₂ B t₂ (q ∷ Ψ₂)
        → W⇒ L (RLet x e₁ e₂) B (let′ q t₁ t₂) (Ψ₂ +ᵘ (q *ᵘ Ψ₁))
  w-let q (d₁ , u₁) (d₂ , u₂) = SU.s-let q d₁ d₂ , u-let u₁ u₂

  w-case : ∀ {e xl el xr er A B Cl Cr C ts tl tr Ψs Ψₗ Ψᵣ} (ql qr : Quantity)
         → W⇒ L e (A + B) ts Ψs → W⇒ (L ▹ xl ∶ A) el Cl tl (ql ∷ Ψₗ) → W⇒ (L ▹ xr ∶ B) er Cr tr (qr ∷ Ψᵣ) → Cl ⊔ Cr ≔ C
         → W⇒ L (RDestruct e xl el xr er) C (case ql qr ts (coerce Cl C tl) (coerce Cr C tr)) (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
  w-case ql qr (ds , us) (dl , ul) (dr , ur) j = SU.s-case ql qr ds dl dr j , u-case us ul ur

  w-arith : ∀ {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → IntArith op p → W⇒ L e₁ Int t₁ Ψ₁ → W⇒ L e₂ Int t₂ Ψ₂
          → W⇒ L (RBinOp op e₁ e₂) Int (prim p (pair t₁ t₂)) (Ψ₁ +ᵘ Ψ₂)
  w-arith o (d₁ , u₁) (d₂ , u₂) = SU.s-arith o d₁ d₂ , u-arith u₁ u₂

  w-arith-float : ∀ {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → FloatArith op p → W⇒ L e₁ Float t₁ Ψ₁ → W⇒ L e₂ Float t₂ Ψ₂
                → W⇒ L (RBinOp op e₁ e₂) Float (prim p (pair t₁ t₂)) (Ψ₁ +ᵘ Ψ₂)
  w-arith-float o (d₁ , u₁) (d₂ , u₂) = SU.s-arith-float o d₁ d₂ , u-arith-float u₁ u₂

  w-arith-float-il : ∀ {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → FloatArith op p → W⇒ L e₁ Int t₁ Ψ₁ → W⇒ L e₂ Float t₂ Ψ₂
                   → W⇒ L (RBinOp op e₁ e₂) Float (prim p (pair (prim p-i2f t₁) t₂)) (Ψ₁ +ᵘ Ψ₂)
  w-arith-float-il o (d₁ , u₁) (d₂ , u₂) = SU.s-arith-float-il o d₁ d₂ , u-arith-float-il u₁ u₂

  w-arith-float-ir : ∀ {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → FloatArith op p → W⇒ L e₁ Float t₁ Ψ₁ → W⇒ L e₂ Int t₂ Ψ₂
                   → W⇒ L (RBinOp op e₁ e₂) Float (prim p (pair t₁ (prim p-i2f t₂))) (Ψ₁ +ᵘ Ψ₂)
  w-arith-float-ir o (d₁ , u₁) (d₂ , u₂) = SU.s-arith-float-ir o d₁ d₂ , u-arith-float-ir u₁ u₂

  w-compare : ∀ {op p e₁ e₂ t₁ t₂ Ψ₁ Ψ₂} → Compare op p → W⇒ L e₁ Int t₁ Ψ₁ → W⇒ L e₂ Int t₂ Ψ₂
            → W⇒ L (RBinOp op e₁ e₂) (Unit + Unit) (prim p (pair t₁ t₂)) (Ψ₁ +ᵘ Ψ₂)
  w-compare o (d₁ , u₁) (d₂ , u₂) = SU.s-compare o d₁ d₂ , u-compare u₁ u₂

  w-id-app : ∀ {e T t Ψ} → W⇒ L e T t Ψ → W⇒ L (RApp (RResolved (gen "id")) e) T (app (idᶜ T pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-id-app (d , u) = SU.s-id-app d , u-id-app u

  w-fst-app : ∀ {e A B t Ψ} → W⇒ L e (A * B) t Ψ → W⇒ L (RApp (RResolved (gen "fst")) e) A (app (fstᶜ A B pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-fst-app (d , u) = SU.s-fst-app d , u-fst-app u

  w-snd-app : ∀ {e A B t Ψ} → W⇒ L e (A * B) t Ψ → W⇒ L (RApp (RResolved (gen "snd")) e) B (app (sndᶜ A B pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-snd-app (d , u) = SU.s-snd-app d , u-snd-app u

  w-terminal-app : ∀ {e T t Ψ} → W⇒ L e T t Ψ → W⇒ L (RApp (RResolved (gen "terminal")) e) Unit (app (terminalᶜ T pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-terminal-app (d , u) = SU.s-terminal-app d , u-terminal-app u

  w-apply-app : ∀ {e A B t Ψ} → W⇒ L e ((A ⇒⟨ pure ⟩ B) * A) t Ψ
              → W⇒ L (RApp (RResolved (gen "apply")) e) B (app (applyᶜ A B) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-apply-app (d , u) = SU.s-apply-app d , u-apply-app u

  w-apply-eff-app : ∀ {e A B π t Ψ} → EffGrade π → W⇒ L e ((A ⇒⟨ π ⟩ B) * A) t Ψ
                  → W⇒ L (RApp (RResolved (gen "apply")) e) (Unit ⇒⟨ π ⟩ B) (app (applyEffᶜ π A B) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-apply-eff-app g (d , u) = SU.s-apply-eff-app g d , u-apply-eff-app u

  w-Out-app : ∀ {e F t Ψ} → WFFun Δ F → W⇒ L e (ν F pureᶠ) t Ψ
            → W⇒ L (RApp (RResolved (gen "Out")) e) (⟦ F ⟧F (ν F pureᶠ)) (app (outᶜ F) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-Out-app w (d , u) = SU.s-Out-app w d , u-Out-app u

  w-Out-act-app : ∀ {e F t Ψ} → WFFun Δ F → W⇒ L e (ν F actᶠ) t Ψ
                → W⇒ L (RApp (RResolved (gen "Out")) e) (Unit ⇒⟨ act ⟩ ⟦ F ⟧F (ν F actᶠ)) (app (outActᶜ F) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-Out-act-app w (d , u) = SU.s-Out-act-app w d , u-Out-act-app u

  w-app : ∀ {f x A B q tf tx Ψ₁ Ψ₂} → ¬ SpecialHead f
        → W⇒ L f (A ⇒[ mk-kind q pure ] B) tf Ψ₁ → W⇐ L x A tx Ψ₂ → W⇒ L (RApp f x) B (app tf tx) (Ψ₁ +ᵘ (q *ᵘ Ψ₂))
  w-app ns (df , uf) (dx , ux) = SU.s-app ns df dx , u-app uf ux

  w-effApp : ∀ {f x A B π tf tx Ψ₁ Ψ₂} → ¬ SpecialHead f → EffGrade π
           → W⇒ L f (A ⇒⟨ π ⟩ B) tf Ψ₁ → W⇐ L x A tx Ψ₂ → W⇒ L (RApp f x) (Unit ⇒⟨ π ⟩ B) (effAppᶜ π tf tx) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-effApp ns g (df , uf) (dx , ux) = SU.s-effApp ns g df dx , u-effApp uf ux

  w-app-spine : ∀ {f x X T tf tx Ψ₁ Ψ₂} → ¬ SpecialHead f
              → W⇒ L x X tx Ψ₂ → W↦ L f X pure T tf Ψ₁ → W⇒ L (RApp f x) T (app tf tx) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-app-spine ns (dx , ux) (df , uf) = SU.s-app-spine ns dx df , u-app-spine ux uf

  ------------------------------------------------------------------
  -- Checking
  ------------------------------------------------------------------

  w-id : ∀ {T π} → W⇐ L (RResolved (gen "id")) (T ⇒⟨ π ⟩ T) (idᶜ T π) zeroUsage
  w-id = SU.c-id , u-id

  w-fst : ∀ {A B π} → W⇐ L (RResolved (gen "fst")) ((A * B) ⇒⟨ π ⟩ A) (fstᶜ A B π) zeroUsage
  w-fst = SU.c-fst , u-fst

  w-snd : ∀ {A B π} → W⇐ L (RResolved (gen "snd")) ((A * B) ⇒⟨ π ⟩ B) (sndᶜ A B π) zeroUsage
  w-snd = SU.c-snd , u-snd

  w-terminal : ∀ {A π} → W⇐ L (RResolved (gen "terminal")) (A ⇒⟨ π ⟩ Unit) (terminalᶜ A π) zeroUsage
  w-terminal = SU.c-terminal , u-terminal

  w-initial : ∀ {A π} → W⇐ L (RResolved (gen "initial")) (Void ⇒⟨ π ⟩ A) (initialᶜ A π) zeroUsage
  w-initial = SU.c-initial , u-initial

  w-inl : ∀ {A B π} → W⇐ L (RResolved (gen "inl")) (A ⇒⟨ π ⟩ (A + B)) (inlᶜ A B π) zeroUsage
  w-inl = SU.c-inl , u-inl

  w-inr : ∀ {A B π} → W⇐ L (RResolved (gen "inr")) (B ⇒⟨ π ⟩ (A + B)) (inrᶜ A B π) zeroUsage
  w-inr = SU.c-inr , u-inr

  w-compose-g : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W↦ L g A π B tg Ψ₂ → W⇐ L f (B ⇒⟨ π ⟩ C) tf Ψ₁
              → W⇐ L (RApp (RApp (RResolved (gen "compose")) f) g) (A ⇒⟨ π ⟩ C) (composeᶜ A π tf tg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-compose-g (dg , ug) (df , uf) = SU.c-compose-g dg df , u-compose-g ug uf

  w-compose-f : ∀ {f g A B C C′ π π′ tf tg Ψ₁ Ψ₂}
              → W⇒ L f (B ⇒⟨ π′ ⟩ C′) tf Ψ₁ → (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C) → W⇐ L g (A ⇒⟨ π ⟩ B) tg Ψ₂
              → W⇐ L (RApp (RApp (RResolved (gen "compose")) f) g) (A ⇒⟨ π ⟩ C)
                   (composeᶜ A π (coerce (B ⇒⟨ π′ ⟩ C′) (B ⇒⟨ π ⟩ C) tf) tg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-compose-f (df , uf) p (dg , ug) = SU.c-compose-f df p dg , u-compose-f uf ug

  w-case′ : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W⇐ L f (A ⇒⟨ π ⟩ C) tf Ψ₁ → W⇐ L g (B ⇒⟨ π ⟩ C) tg Ψ₂
          → W⇐ L (RApp (RApp (RResolved (gen "case")) f) g) ((A + B) ⇒⟨ π ⟩ C) (caseᶜ A B π tf tg) (Ψ₁ +ᵘ Ψ₂)
  w-case′ (df , uf) (dg , ug) = SU.c-case df dg , u-case uf ug

  w-pair′ : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W⇐ L f (A ⇒⟨ π ⟩ B) tf Ψ₁ → W⇐ L g (A ⇒⟨ π ⟩ C) tg Ψ₂
          → W⇐ L (RApp (RApp (RResolved (gen "pair")) f) g) (A ⇒⟨ π ⟩ (B * C)) (pairᶜ A π tf tg) (Ψ₁ +ᵘ Ψ₂)
  w-pair′ (df , uf) (dg , ug) = SU.c-pair df dg , u-pair uf ug

  w-curry : ∀ {f A B C π₀ π t Ψ} → W⇐ L f ((A * B) ⇒⟨ π ⟩ C) t Ψ
          → W⇐ L (RApp (RResolved (gen "curry")) f) (A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C)) (curryᶜ A B π₀ π t) Ψ
  w-curry (d , u) = SU.c-curry d , u-curry u

  w-cata : ∀ {alg F A π t Ψ} → WFFun Δ F → W⇐ L alg (⟦ F ⟧F A ⇒⟨ π ⟩ A) t Ψ
         → W⇐ L (RApp (RResolved (gen "cata")) alg) (μ F ⇒⟨ π ⟩ A) (cataᶜ F π t) (Many *ᵘ Ψ)
  w-cata w (d , u) = SU.c-cata w d , u-cata u

  w-ana : ∀ {c F A π₀ f t Ψ} → π₀ ⊑π act → WFFun Δ F → W⇐ L c (A ⇒⟨ fin f ⟩ ⟦ F ⟧F A) t Ψ
        → W⇐ L (RApp (RResolved (gen "ana")) c) (A ⇒⟨ π₀ ⟩ ν F f) (anaᶜ F A π₀ t) (Many *ᵘ Ψ)
  w-ana g w (d , u) = SU.c-ana g w d , u-ana u

  w-loop : ∀ {c A B t Ψ} → W⇐ L c (A ⇒⟨ act ⟩ (B + A)) t Ψ
         → W⇐ L (RApp (RResolved (gen "ana")) c) (A ⇒⟨ eff ⟩ B) (loopᶜ A t) (Many *ᵘ Ψ)
  w-loop (d , u) = SU.c-loop d , u-loop u

  w-sub : ∀ {e A B t Ψ} → W⇒ L e A t Ψ → A <: B → W⇐ L e B (coerce A B t) Ψ
  w-sub (d , u) p = SU.c-sub d p , u-sub u

  w-lam : ∀ {x body A B q q′ π t Ψ} → (q′ ≤qᵇ q) ≡ true → W⇐ (L ▹ x ∶ A) body B t (q′ ∷ Ψ)
        → W⇐ L (RLam x body) (A ⇒[ mk-kind q π ] B) (lam A q π t) Ψ
  w-lam ≤p (d , u) = SU.c-lam d , u-lam ≤p u

  w-pair-lit : ∀ {a b A B ta tb Ψ₁ Ψ₂} → W⇐ L a A ta Ψ₁ → W⇐ L b B tb Ψ₂ → W⇐ L (RPair a b) (A * B) (pair ta tb) (Ψ₁ +ᵘ Ψ₂)
  w-pair-lit (da , ua) (db , ub) = SU.c-pair-lit da db , u-pair-lit ua ub

  w-In-app : ∀ {e F t Ψ} → WFFun Δ F → W⇐ L e (⟦ F ⟧F (μ F)) t Ψ
           → W⇐ L (RApp (RResolved (gen "In")) e) (μ F) (app (inᶜ F) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-In-app w (d , u) = SU.c-In-app w d , u-In-app u

  w-apply-app′ : ∀ {e A B t Ψ} → W⇒ L e ((A ⇒⟨ pure ⟩ B) * A) t Ψ
               → W⇐ L (RApp (RResolved (gen "apply")) e) B (app (applyᶜ A B) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-apply-app′ (d , u) = SU.c-apply-app d , u-apply-app u

  w-inl-app : ∀ {e A B t Ψ} → W⇐ L e A t Ψ → W⇐ L (RApp (RResolved (gen "inl")) e) (A + B) (app (inlᶜ A B pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-inl-app (d , u) = SU.c-inl-app d , u-inl-app u

  w-inr-app : ∀ {e A B t Ψ} → W⇐ L e B t Ψ → W⇐ L (RApp (RResolved (gen "inr")) e) (A + B) (app (inrᶜ A B pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-inr-app (d , u) = SU.c-inr-app d , u-inr-app u

  w-initial-app : ∀ {e T t Ψ} → W⇐ L e Void t Ψ
                → W⇐ L (RApp (RResolved (gen "initial")) e) T (app (initialᶜ T pure) t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-initial-app (d , u) = SU.c-initial-app d , u-initial-app u

  w-poly : ∀ {c} (d : Fin s) → nm d ≡ c → 0 < arity (S !! d) → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
         → W⇐ L (RResolved c) (type (S !! d) ⟨ τ ⟩) (ref d τ) zeroUsage
  w-poly d e a τ r = SU.c-poly d e a τ r , u-poly

  ------------------------------------------------------------------
  -- An arrow out of a given domain
  ------------------------------------------------------------------

  w-infer : ∀ {g A A′ B π π′ t Ψ} → W⇒ L g (A′ ⇒⟨ π′ ⟩ B) t Ψ → A <: A′ → π′ ⊑π π
          → W↦ L g A π B (coerce (A′ ⇒⟨ π′ ⟩ B) (A ⇒⟨ π ⟩ B) t) Ψ
  w-infer (d , u) p o = SU.d-infer d p o , u-infer u

  w-poly↦ : ∀ {c} (d : Fin s) → nm d ≡ c → 0 < arity (S !! d)
          → ∀ {sd sc π′ A B π} → type (S !! d) ≡ sd ⇒⟨ π′ ⟩ sc → (∀ i → Occurs i sc → Occurs i sd)
          → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
          → sd ⟨ τ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B → π′ ⊑π π
          → W↦ L (RResolved c) A π B (coerce (A ⇒⟨ π′ ⟩ B) (A ⇒⟨ π ⟩ B) (ref d τ)) zeroUsage
  w-poly↦ d e a ty oc τ r ea eb o = SU.d-poly d e a ty oc τ r ea eb o , u-poly

  w-lam↦ : ∀ {x body A B π t q′ Ψ} → W⇒ (L ▹ x ∶ A) body B t (q′ ∷ Ψ) → W↦ L (RLam x body) A π B (lam A Many π t) Ψ
  w-lam↦ (d , u) = SU.d-lam d , u-lam u

  w-compose↦ : ∀ {f g A M B π tf tg Ψ₁ Ψ₂} → W↦ L g A π M tg Ψ₂ → W↦ L f M π B tf Ψ₁
             → W↦ L (RApp (RApp (RResolved (gen "compose")) f) g) A π B (composeᶜ A π tf tg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-compose↦ (dg , ug) (df , uf) = SU.d-compose dg df , u-compose ug uf

  w-id↦ : ∀ {A π} → W↦ L (RResolved (gen "id")) A π A (idᶜ A π) zeroUsage
  w-id↦ = SU.d-id , u-id

  w-fst↦ : ∀ {A B π} → W↦ L (RResolved (gen "fst")) (A * B) π A (fstᶜ A B π) zeroUsage
  w-fst↦ = SU.d-fst , u-fst

  w-snd↦ : ∀ {A B π} → W↦ L (RResolved (gen "snd")) (A * B) π B (sndᶜ A B π) zeroUsage
  w-snd↦ = SU.d-snd , u-snd

  w-terminal↦ : ∀ {A π} → W↦ L (RResolved (gen "terminal")) A π Unit (terminalᶜ A π) zeroUsage
  w-terminal↦ = SU.d-terminal , u-terminal

  w-initial↦ : ∀ {π} → W↦ L (RResolved (gen "initial")) Void π Void (initialᶜ Void π) zeroUsage
  w-initial↦ = SU.d-initial , u-initial

  w-case↦ : ∀ {f g A B Cf Cg C π tf tg Ψ₁ Ψ₂} → W↦ L f A π Cf tf Ψ₁ → W↦ L g B π Cg tg Ψ₂ → Cf ⊔ Cg ≔ C
          → W↦ L (RApp (RApp (RResolved (gen "case")) f) g) (A + B) π C
               (caseᶜ A B π (coerce (A ⇒⟨ π ⟩ Cf) (A ⇒⟨ π ⟩ C) tf) (coerce (B ⇒⟨ π ⟩ Cg) (B ⇒⟨ π ⟩ C) tg)) (Ψ₁ +ᵘ Ψ₂)
  w-case↦ (df , uf) (dg , ug) j = SU.d-case df dg j , u-case uf ug

  w-pair↦ : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W↦ L f A π B tf Ψ₁ → W↦ L g A π C tg Ψ₂
          → W↦ L (RApp (RApp (RResolved (gen "pair")) f) g) A π (B * C) (pairᶜ A π tf tg) (Ψ₁ +ᵘ Ψ₂)
  w-pair↦ (df , uf) (dg , ug) = SU.d-pair df dg , u-pair uf ug

  w-cata↦ : ∀ {alg F A π t Ψ} → WFFun Δ F → W⇒ L alg (⟦ F ⟧F A ⇒⟨ π ⟩ A) t Ψ
          → W↦ L (RApp (RResolved (gen "cata")) alg) (μ F) π A (cataᶜ F π t) (Many *ᵘ Ψ)
  w-cata↦ w (d , u) = SU.d-cata w d , u-cata u
