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
open import Once.Spec.Type using (KCtx; Type)

module Once.TypeCheck.Witness (Σ : Signature) {s : ℕ} (S : Defs s) (nm : Fin s → CanonicalName) (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) {m : ℕ} (Δ : KCtx m) where

open import Data.Bool using (true)
open import Data.Integer using (ℤ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)
open import Once.Spec.Grade using (Quantity; Many; One; Purity; pure; mk-kind; _⊑π_)
open import Once.Spec.Type using (Ty; Type; TySub; Respects; WFFun; Occurs; _⟨_⟩; _⇒[_]_; _*_; _+_; Unit; Int; Float; μ; ⟦_⟧F)
open import Once.Spec.Sub using (_<:_; _⊔_≔_)
open import Once.Spec.Signature using (_∶_; ⌜_⌝ᵈ)
open import Once.Spec.Surface.Generators using (Gen; kind; FromDomain; FromCodomain; Constant; Morphism; Final)
open import Once.Spec.Surface.Syntax
open import Once.Spec.Core.Syntax
  using (Tm; lit; lit-int; lit-float; unit; var; sigop; ref; pair; prim; num; let′; case; coerce; app; lam;
         _!!_; module Schema)
open Schema using (arity; kinds; type)
open import Once.Spec.Core.Derived
open import Once.Spec.Context using (Usage; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_)
open import Once.Context using (_⊔ᵘ_)
open import Once.Type.Concrete using (IsConcrete)
open import Once.Type.Grade using (_≤qᵇ_)
import Once.Spec.Surface.Typing Σ S nm as SU
open SU using (Locals; _▹_∶_; _∋_⦂_at_; PartialCombinator; CheckHead; OwnCheck; DomainForm; _⇒⟨_⟩_; ↑)
open import Once.Spec.Sub using (_<:ᶜ_)
open import Once.Spec.Surface.Operator using (binSym; BinSym)
open BinSym using (theory; shape; symbol)
open import Once.Spec.Theory using (Has; Neg; ⌜_⌝ⁿ; symCod; ‵neg)
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Type.Honest using (HonestFFI)
open import Once.Core.Decl using (declS)

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

  w-float : ∀ sg i f l
          → W⇒ L (RFloat sg i f l) Float (lit (lit-float (signedDecimal sg i f l))) zeroUsage
  w-float sg i f l = SU.s-float sg i f l , u-float

  w-unit : W⇒ L RUnit Unit unit zeroUsage
  w-unit = SU.s-unit , u-unit

  w-const : ∀ {g k T t} → Constant Δ g k T t → W⇒ L (RGen g) T t zeroUsage
  w-const c = SU.s-const c , u-const

  w-var : ∀ {x A i} → L ∋ x ⦂ A at i → W⇒ L (RVar x) A (var i) (singleUse i One)
  w-var v = SU.s-var v , u-var

  w-sigop : ∀ {c} {T : Type} {ok : OkS c T} → (mem : (c ∶ declS T) ∈ Σ) → IsConcrete T → HonestFFI T
          → W⇒ L (RResolved c) ⌜ declS T ⌝ᵈ (sigop c (declS T)) zeroUsage
  w-sigop {ok = ok} mem k h = SU.s-sigop mem , u-sigop {ok = ok} k h

  w-def : ∀ {c} (d : Fin s) {ok : Ok d} → nm d ≡ c → (τ : TySub (arity (S !! d)) m) → arity (S !! d) ≡ 0
        → W⇒ L (RResolved c) (type (S !! d) ⟨ τ ⟩) (ref d τ) zeroUsage
  w-def d {ok} e τ a = SU.s-def d e τ a , u-def {ok = ok}

  w-annot : ∀ {e T t Ψ} → W⇐ L e (↑ T) t Ψ → W⇒ L (RAnnot e T) (↑ T) t Ψ
  w-annot (d , u) = SU.s-annot d , u-annot u

  w-pair : ∀ {a b A B ta tb Ψ₁ Ψ₂} → W⇒ L a A ta Ψ₁ → W⇒ L b B tb Ψ₂ → W⇒ L (RPair a b) (A * B) (pair ta tb) (Ψ₁ +ᵘ Ψ₂)
  w-pair (da , ua) (db , ub) = SU.s-pair da db , u-pair ua ub

  w-neg : ∀ {e A t Ψ} (h : Has A Neg) → W⇒ L e ⌜ A ⌝ⁿ t Ψ → W⇒ L (RNeg e) ⌜ A ⌝ⁿ (prim (num h ‵neg) t) Ψ
  w-neg h (d , u) = SU.s-neg h d , u-neg u

  w-let : ∀ {x e₁ e₂ A B t₁ t₂ Ψ₁ Ψ₂} (q : Quantity)
        → W⇒ L e₁ A t₁ Ψ₁ → W⇒ (L ▹ x ∶ A) e₂ B t₂ (q ∷ Ψ₂)
        → W⇒ L (RLet x e₁ e₂) B (let′ q t₁ t₂) (Ψ₂ +ᵘ (q *ᵘ Ψ₁))
  w-let q (d₁ , u₁) (d₂ , u₂) = SU.s-let q d₁ d₂ , u-let u₁ u₂

  w-case : ∀ {e xl el xr er A B Cl Cr C ts tl tr Ψs Ψₗ Ψᵣ} (ql qr : Quantity)
         → W⇒ L e (A + B) ts Ψs → W⇒ (L ▹ xl ∶ A) el Cl tl (ql ∷ Ψₗ) → W⇒ (L ▹ xr ∶ B) er Cr tr (qr ∷ Ψᵣ) → Cl ⊔ Cr ≔ C
         → W⇒ L (RDestruct e xl el xr er) C (case ql qr ts (coerce Cl C tl) (coerce Cr C tr)) (Ψs +ᵘ (Ψₗ ⊔ᵘ Ψᵣ))
  w-case ql qr (ds , us) (dl , ul) (dr , ur) j = SU.s-case ql qr ds dl dr j , u-case us ul ur

  w-binop : ∀ {op e₁ e₂ A t₁ t₂ Ψ₁ Ψ₂} (h : Has A (theory (binSym op))) → W⇒ L e₁ ⌜ A ⌝ⁿ t₁ Ψ₁ → W⇒ L e₂ ⌜ A ⌝ⁿ t₂ Ψ₂
          → W⇒ L (RBinOp op e₁ e₂) (symCod A (shape (binSym op))) (prim (num h (symbol (binSym op))) (pair t₁ t₂)) (Ψ₁ +ᵘ Ψ₂)
  w-binop h (d₁ , u₁) (d₂ , u₂) = SU.s-binop h d₁ d₂ , u-binop u₁ u₂


  w-app : ∀ {f x A B q π tf tx Ψ₁ Ψ₂} → ¬ PartialCombinator f → ¬ CheckHead f
        → W⇒ L f (A ⇒[ mk-kind q π ] B) tf Ψ₁ → W⇐ L x A tx Ψ₂ → W⇒ L (RApp f x) (𝕋 π B) (appᵀ π tf tx) (Ψ₁ +ᵘ (q *ᵘ Ψ₂))
  w-app pc ch (df , uf) (dx , ux) = SU.s-app pc ch df dx , u-app uf ux

  w-app-spine : ∀ {f x X T tf tx Ψ₁ Ψ₂} → CheckHead f
              → W⇒ L x X tx Ψ₂ → W↦ L f X pure T tf Ψ₁ → W⇒ L (RApp f x) T (app tf tx) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-app-spine ch (dx , ux) (df , uf) = SU.s-app-spine ch dx df , u-app-spine ux uf

  ------------------------------------------------------------------
  -- Checking
  ------------------------------------------------------------------

  w-map : ∀ {g k A π B t} → Morphism Δ g k A π B t → W⇐ L (RGen g) (A ⇒⟨ π ⟩ B) t zeroUsage
  w-map mo = SU.c-map mo , u-map

  w-map-app : ∀ {g k e A B tg t Ψ} → FromCodomain (kind g) → Morphism Δ g k A pure B tg → W⇐ L e A t Ψ
            → W⇐ L (RApp (RGen g) e) B (app tg t) (zeroUsage +ᵘ (Many *ᵘ Ψ))
  w-map-app fc mo (d , u) = SU.c-map-app fc mo d , u-map-app u

  w-compose-g : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → DomainForm g → W↦ L g A π B tg Ψ₂ → W⇐ L f (B ⇒⟨ π ⟩ C) tf Ψ₁
              → W⇐ L (RApp (RApp (RGen Gen.compose) f) g) (A ⇒⟨ π ⟩ C) (composeᶜ A π tf tg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-compose-g df′ (dg , ug) (df , uf) = SU.c-compose-g df′ dg df , u-compose-g ug uf

  w-compose-f : ∀ {f g A B C C′ π π′ tf tg Ψ₁ Ψ₂} → ¬ DomainForm g
              → W⇒ L f (B ⇒⟨ π′ ⟩ C′) tf Ψ₁ → (B ⇒⟨ π′ ⟩ C′) <: (B ⇒⟨ π ⟩ C) → W⇐ L g (A ⇒⟨ π ⟩ B) tg Ψ₂
              → W⇐ L (RApp (RApp (RGen Gen.compose) f) g) (A ⇒⟨ π ⟩ C)
                   (composeᶜ A π (coerce (B ⇒⟨ π′ ⟩ C′) (B ⇒⟨ π ⟩ C) tf) tg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-compose-f ndf (df , uf) p (dg , ug) = SU.c-compose-f ndf df p dg , u-compose-f uf ug

  w-case′ : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W⇐ L f (A ⇒⟨ π ⟩ C) tf Ψ₁ → W⇐ L g (B ⇒⟨ π ⟩ C) tg Ψ₂
          → W⇐ L (RApp (RApp (RGen Gen.case) f) g) ((A + B) ⇒⟨ π ⟩ C) (caseᶜ A B π tf tg) (Ψ₁ +ᵘ Ψ₂)
  w-case′ (df , uf) (dg , ug) = SU.c-case df dg , u-case uf ug

  w-pair′ : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W⇐ L f (A ⇒⟨ π ⟩ B) tf Ψ₁ → W⇐ L g (A ⇒⟨ π ⟩ C) tg Ψ₂
          → W⇐ L (RApp (RApp (RGen Gen.pair) f) g) (A ⇒⟨ π ⟩ (B * C)) (pairᶜ A π tf tg) (Ψ₁ +ᵘ Ψ₂)
  w-pair′ (df , uf) (dg , ug) = SU.c-pair df dg , u-pair uf ug

  w-curry : ∀ {f A B C π₀ π t Ψ} → W⇐ L f ((A * B) ⇒⟨ π ⟩ C) t Ψ
          → W⇐ L (RApp (RGen Gen.curry) f) (A ⇒⟨ π₀ ⟩ (B ⇒⟨ π ⟩ C)) (curryᶜ A B π₀ π t) Ψ
  w-curry (d , u) = SU.c-curry d , u-curry u

  w-cata : ∀ {alg F A π t Ψ} → WFFun Δ F → W⇐ L alg (⟦ F ⟧F A ⇒⟨ π ⟩ A) t Ψ
         → W⇐ L (RApp (RGen Gen.cata) alg) (μ F ⇒⟨ π ⟩ A) (cataᶜ F π t) (Many *ᵘ Ψ)
  w-cata w (d , u) = SU.c-cata w d , u-cata u

  w-ana : ∀ {c A π₀ X G ρ k t Ψ} → Final Δ A π₀ X G ρ k → W⇐ L c (A ⇒⟨ ρ ⟩ G A) t Ψ
        → W⇐ L (RApp (RGen Gen.ana) c) (A ⇒⟨ π₀ ⟩ X) (k t) (Many *ᵘ Ψ)
  w-ana fi (d , u) = SU.c-ana fi d , u-ana u

  w-sub : ∀ {e A B t Ψ} → ¬ OwnCheck e → W⇒ L e A t Ψ → A <: B → W⇐ L e B (coerce A B t) Ψ
  w-sub noc (d , u) p = SU.c-sub noc d p , u-sub u

  w-lam : ∀ {x body A B q q′ π t Ψ} → (q′ ≤qᵇ q) ≡ true → W⇐ (L ▹ x ∶ A) body B t (q′ ∷ Ψ)
        → W⇐ L (RLam x body) (A ⇒[ mk-kind q π ] B) (lam A q π t) Ψ
  w-lam ≤p (d , u) = SU.c-lam d , u-lam ≤p u

  w-pair-lit : ∀ {a b A B ta tb Ψ₁ Ψ₂} → W⇐ L a A ta Ψ₁ → W⇐ L b B tb Ψ₂ → W⇐ L (RPair a b) (A * B) (pair ta tb) (Ψ₁ +ᵘ Ψ₂)
  w-pair-lit (da , ua) (db , ub) = SU.c-pair-lit da db , u-pair-lit ua ub

  w-poly : ∀ {c} (d : Fin s) {ok : Ok d} → nm d ≡ c → 0 < arity (S !! d) → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
         → W⇐ L (RResolved c) (type (S !! d) ⟨ τ ⟩) (ref d τ) zeroUsage
  w-poly d {ok} e a τ r = SU.c-poly d e a τ r , u-poly {ok = ok}

  ------------------------------------------------------------------
  -- An arrow out of a given domain
  ------------------------------------------------------------------

  w-infer : ∀ {g A A′ B π π′ t Ψ} → W⇒ L g (A′ ⇒⟨ π′ ⟩ B) t Ψ → A <: A′ → π′ ⊑π π
          → W↦ L g A π B (coerce (A′ ⇒⟨ π′ ⟩ B) (A ⇒⟨ π ⟩ B) t) Ψ
  w-infer (d , u) p o = SU.d-infer d p o , u-infer u

  w-poly↦ : ∀ {c} (d : Fin s) {ok : Ok d} → nm d ≡ c → 0 < arity (S !! d)
          → ∀ {sd sc π′ A B π} → type (S !! d) ≡ sd ⇒⟨ π′ ⟩ sc → (∀ i → Occurs i sc → Occurs i sd)
          → (τ : TySub (arity (S !! d)) m) → Respects (kinds (S !! d)) Δ τ
          → sd ⟨ τ ⟩ ≡ A → sc ⟨ τ ⟩ ≡ B → π′ ⊑π π
          → W↦ L (RResolved c) A π B (coerce (A ⇒⟨ π′ ⟩ B) (A ⇒⟨ π ⟩ B) (ref d τ)) zeroUsage
  w-poly↦ d {ok} e a ty oc τ r ea eb o = SU.d-poly d e a ty oc τ r ea eb o , u-poly {ok = ok}

  w-lam↦ : ∀ {x body A B π t q′ Ψ} → W⇒ (L ▹ x ∶ A) body B t (q′ ∷ Ψ) → W↦ L (RLam x body) A π B (lam A Many π t) Ψ
  w-lam↦ (d , u) = SU.d-lam d , u-lam u

  w-compose↦ : ∀ {f g A M B π tf tg Ψ₁ Ψ₂} → W↦ L g A π M tg Ψ₂ → W↦ L f M π B tf Ψ₁
             → W↦ L (RApp (RApp (RGen Gen.compose) f) g) A π B (composeᶜ A π tf tg) (Ψ₁ +ᵘ (Many *ᵘ Ψ₂))
  w-compose↦ (dg , ug) (df , uf) = SU.d-compose dg df , u-compose ug uf

  w-map↦ : ∀ {g k A π B t} → FromDomain (kind g) → (mo : Morphism Δ g k A π B t)
         → (∀ {k′ B′} {t′ : Tm S m n} → Morphism Δ g k′ A π B′ t′ → B <:ᶜ B′)
         → W↦ L (RGen g) A π B t zeroUsage
  w-map↦ fd mo least = SU.d-map fd mo least , u-map

  w-case↦ : ∀ {f g A B Cf Cg C π tf tg Ψ₁ Ψ₂} → W↦ L f A π Cf tf Ψ₁ → W↦ L g B π Cg tg Ψ₂ → Cf ⊔ Cg ≔ C
          → W↦ L (RApp (RApp (RGen Gen.case) f) g) (A + B) π C
               (caseᶜ A B π (coerce (A ⇒⟨ π ⟩ Cf) (A ⇒⟨ π ⟩ C) tf) (coerce (B ⇒⟨ π ⟩ Cg) (B ⇒⟨ π ⟩ C) tg)) (Ψ₁ +ᵘ Ψ₂)
  w-case↦ (df , uf) (dg , ug) j = SU.d-case df dg j , u-case uf ug

  w-pair↦ : ∀ {f g A B C π tf tg Ψ₁ Ψ₂} → W↦ L f A π B tf Ψ₁ → W↦ L g A π C tg Ψ₂
          → W↦ L (RApp (RApp (RGen Gen.pair) f) g) A π (B * C) (pairᶜ A π tf tg) (Ψ₁ +ᵘ Ψ₂)
  w-pair↦ (df , uf) (dg , ug) = SU.d-pair df dg , u-pair uf ug

  w-cata↦ : ∀ {alg F A₁ A π′ π t Ψ} → WFFun Δ F → W⇒ L alg (A₁ ⇒⟨ π′ ⟩ A) t Ψ → ⟦ F ⟧F A <: A₁ → π′ ⊑π π
          → W↦ L (RApp (RGen Gen.cata) alg) (μ F) π A
               (cataᶜ F π (coerce (A₁ ⇒⟨ π′ ⟩ A) (⟦ F ⟧F A ⇒⟨ π ⟩ A) t)) (Many *ᵘ Ψ)
  w-cata↦ w (d , u) p o = SU.d-cata w d p o , u-cata u
