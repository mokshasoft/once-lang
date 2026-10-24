-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.Annotate — a Spec derivation, typed in the core,
-- is one the checker annotates (plan 0.122 §5.6, stage f).
--
-- The Spec's surface rules leave linearity to the core typing of the term
-- they name; the checker counts usage as it goes (`TypeCheck.Use`). Read
-- back from a core typing of the term (`CoreInv`, `GenInv`), each part of
-- the expression is used at most as the whole's typing allows, so the
-- derivation carries a `Use` below that typing's usage — after one change:
-- a `let`'s and a `case`'s binder take the quantity their body uses (the
-- checker's), where the Spec's derivation may state any larger one. So the
-- result is a derivation of the same expression at the same type, its own
-- term, annotated (a declaration read at its FFI declaration, the same
-- type).
--
-- What a reference asks of the scope is asked of the parameters: a
-- definition referenced (never `main`, `RX`) is one the checker finds
-- (`ok-def`), a declaration is an honest, concrete FFI declaration the
-- checker's signature holds (`ok-sig`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Once.Spec.Name using (CanonicalName; canonical; NotGenerator)
open import Once.Spec.Signature using (Signature; _∶_; ⌜_⌝ᵈ)
open import Once.Spec.Type using (Type; KCtx)
open import Once.Internal.Type.WellFormed using (IsConcrete)
open import Once.Internal.Type.Honest using (HonestFFI)
open import Once.Internal.Core.Decl using (declS)
import Once.Spec.Core.Syntax as SC

module Once.Adequacy.SpecFront.Annotate
  (Σ : Signature) {s : ℕ} (S : SC.Defs s) (nm : Fin s → CanonicalName)
  (Ok : Fin s → Set) (OkS : CanonicalName → Type → Set) {m : ℕ} (Δ : KCtx m)
  -- a definition a source names (not `main`) is one the checker finds
  (ok-def : ∀ {c} (d : Fin s) → nm d ≡ c → c ≢ canonical ("main" ∷ []) → Ok d)
  -- a declaration of Σ is an honest, concrete FFI declaration of the checker's signature
  -- (its declaration, at the type the Spec reads)
  (ok-sig : ∀ {c t} → NotGenerator c → (c ∶ t) ∈ Σ
          → Σ[ T ∈ Type ] ((c ∶ declS T) ∈ Σ) × (⌜ t ⌝ᵈ ≡ ⌜ declS T ⌝ᵈ) × OkS c T × IsConcrete T × HonestFFI T)
  where

open import Data.Nat using (suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (Quantity; Zero; One; Many; Purity; pure; act; eff; mk-kind; fin;
  _≤q_; 0≤q; 1≤1; 1≤ω; ω≤ω)
open import Once.Spec.Type using (Ty; Int; Float; Unit; Void; _*_; _+_; _⇒[_]_; μ; ν; ⟦_⟧F)
open import Once.Spec.Context using (Usage; []; _∷_; zeroUsage; singleUse; _+ᵘ_; _*ᵘ_; _⊑ᵘ_; _⊑∷_)
import Once.Spec.Context as SCx
open import Once.Internal.Context using (_⊔ᵘ_)
import Once.Type.Grade
open import Once.Spec.Core.Syntax using (Tm; primCod)
open import Once.Spec.Surface.Syntax using (Expr)
open import Once.Spec.Core.Typing Σ S using (_⊩_⊢[_]_∷_!_)
import Once.Spec.Surface.Typing Σ S nm as SU
open import Once.TypeCheck.Use Σ S nm Ok OkS Δ
open import Once.Adequacy.SpecFront.Expr using (RX; x-local; x-res; x-lam; x-let; x-destruct; x-int; x-float; x-unit;
  x-annot; x-pair; x-neg; x-binop; x-app)
open import Once.Adequacy.SpecFront.CoreInv Σ S {Δ = Δ}
open import Once.Adequacy.SpecFront.GenInv Σ S {Δ = Δ}
open import Once.Metatheory.TermModel.Usage using (⊑ᵘ-refl; ⊑ᵘ-+; ⊑ᵘ-*ʳ; ⊑ᵘ-*ˡ; One*ᵘ)

private
  _⇒⟨_⟩_ : Ty m → Purity → Ty m → Ty m
  A ⇒⟨ π ⟩ B = A ⇒[ mk-kind Many π ] B

------------------------------------------------------------------------
-- What an annotated derivation gives
------------------------------------------------------------------------

record A⇒ {n} (L : SU.Locals m n) (e : Expr) (A : Ty m) (Φ : Usage n) : Set where
  constructor a⇒
  field
    {t} : Tm S m n
    der : L ⊢ e ⇒ A ↝ t
    {Ψ} : Usage n
    use : Use⇒ der Ψ
    le  : Ψ ⊑ᵘ Φ

record A⇐ {n} (L : SU.Locals m n) (e : Expr) (A : Ty m) (Φ : Usage n) : Set where
  constructor a⇐
  field
    {t} : Tm S m n
    der : L ⊢ e ⇐ A ↝ t
    {Ψ} : Usage n
    use : Use⇐ der Ψ
    le  : Ψ ⊑ᵘ Φ

record A↦ {n} (L : SU.Locals m n) (e : Expr) (A : Ty m) (π : Purity) (B : Ty m) (Φ : Usage n) : Set where
  constructor a↦
  field
    {t} : Tm S m n
    der : L ⊢ e ⇐ A ⇒[ π ]↦ B ↝ t
    {Ψ} : Usage n
    use : Use↦ der Ψ
    le  : Ψ ⊑ᵘ Φ

------------------------------------------------------------------------
-- Usage
------------------------------------------------------------------------

private
  z⊑ : ∀ {n} (Φ : Usage n) → zeroUsage ⊑ᵘ Φ
  z⊑ []      = []
  z⊑ (q ∷ Φ) = 0≤q ⊑∷ z⊑ Φ

  ≤q-refl : ∀ q → q ≤q q
  ≤q-refl Zero = 0≤q
  ≤q-refl One  = 1≤1
  ≤q-refl Many = ω≤ω

  ≤q-≡ : ∀ {p q} → p ≡ q → p ≤q q
  ≤q-≡ {p} refl = ≤q-refl p

  -- a usage order, decided
  ≤q-L : ∀ p q → p ≤q q → (p Once.Type.Grade.≤qᵇ q) ≡ true
  ≤q-L Zero q    _ = refl
  ≤q-L One  One  _ = refl
  ≤q-L One  Many _ = refl
  ≤q-L Many Many _ = refl
  ≤q-L One  Zero ()
  ≤q-L Many Zero ()
  ≤q-L Many One  ()

  ⊑-head : ∀ {n p q} {Ψ Φ : Usage n} → (p ∷ Ψ) ⊑ᵘ (q ∷ Φ) → p ≤q q
  ⊑-head (h ⊑∷ _) = h

  ⊑-tail : ∀ {n p q} {Ψ Φ : Usage n} → (p ∷ Ψ) ⊑ᵘ (q ∷ Φ) → Ψ ⊑ᵘ Φ
  ⊑-tail (_ ⊑∷ t) = t

  -- an application's usage: the function's, and the argument's scaled
  app⊑ : ∀ {n} {Ψ₁ Ψ₂ Φ₁ Φ₂ : Usage n} {q q′} → Ψ₁ ⊑ᵘ Φ₁ → Ψ₂ ⊑ᵘ Φ₂ → q ≤q q′ → Ψ₁ +ᵘ q *ᵘ Ψ₂ ⊑ᵘ Φ₁ +ᵘ q′ *ᵘ Φ₂
  app⊑ {Φ₂ = Φ₂} {q} u₁ u₂ le = ⊑ᵘ-+ u₁ (⊑ᵘ-trans (⊑ᵘ-*ʳ q u₂) (⊑ᵘ-*ˡ Φ₂ le))

  -- a generator applied: `Many` uses of its argument, no other
  gen⊑ : ∀ {n} {Ψ Φ Φ₁ Φ₂ : Usage n} {q} → Ψ ⊑ᵘ Φ₂ → q ≡ Many → Φ₁ +ᵘ q *ᵘ Φ₂ ⊑ᵘ Φ → zeroUsage +ᵘ Many *ᵘ Ψ ⊑ᵘ Φ
  gen⊑ {Φ₁ = Φ₁} u refl w = ⊑ᵘ-trans (app⊑ (z⊑ Φ₁) u ω≤ω) w

  many⊑ : ∀ {n} {Ψ Φ₁ Φ : Usage n} → Ψ ⊑ᵘ Φ₁ → Many *ᵘ Φ₁ ⊑ᵘ Φ → Many *ᵘ Ψ ⊑ᵘ Φ
  many⊑ u w = ⊑ᵘ-trans (⊑ᵘ-*ʳ Many u) w

  one⊑ : ∀ {n} {Ψ₁ Ψ₂ Φ₁ Φ₂ Φ : Usage n} → Ψ₁ ⊑ᵘ Φ₁ → Ψ₂ ⊑ᵘ Φ₂ → Φ₁ +ᵘ One *ᵘ Φ₂ ⊑ᵘ Φ → Ψ₁ +ᵘ Ψ₂ ⊑ᵘ Φ
  one⊑ {Φ₂ = Φ₂} u₁ u₂ w = ⊑ᵘ-trans (⊑ᵘ-+ u₁ u₂) (subst (λ Z → _ +ᵘ Z ⊑ᵘ _) (One*ᵘ Φ₂) w)

  one⊑′ : ∀ {n} {Ψ Φ₁ Φ : Usage n} → Ψ ⊑ᵘ Φ₁ → One *ᵘ Φ₁ ⊑ᵘ Φ → Ψ ⊑ᵘ Φ
  one⊑′ {Φ₁ = Φ₁} u w = ⊑ᵘ-trans u (subst (_⊑ᵘ _) (One*ᵘ Φ₁) w)

  -- the branches' join, below a bound of both
  ⊔q-least : ∀ p q {r} → p ≤q r → q ≤q r → (p Once.Type.Grade.⊔q q) ≤q r
  ⊔q-least Zero q    _ b = b
  ⊔q-least One  Zero a _ = a
  ⊔q-least One  One  a _ = a
  ⊔q-least One  Many _ b = b
  ⊔q-least Many q    a _ = a

  ⊔⊑ : ∀ {n} {Ψl Ψr Φ : Usage n} → Ψl ⊑ᵘ Φ → Ψr ⊑ᵘ Φ → (Ψl ⊔ᵘ Ψr) ⊑ᵘ Φ
  ⊔⊑ {Ψl = []}     {[]}     []         []         = []
  ⊔⊑ {Ψl = p ∷ Ψl} {q ∷ Ψr} (a ⊑∷ as) (b ⊑∷ bs) = ⊔q-least p q a b ⊑∷ ⊔⊑ as bs

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

private
  arr-inj : ∀ {A B A′ B′ : Ty m} {q q′ π π′}
          → (A ⇒[ mk-kind q π ] B) ≡ (A′ ⇒[ mk-kind q′ π′ ] B′) → (A ≡ A′) × (q ≡ q′) × (π ≡ π′) × (B ≡ B′)
  arr-inj refl = refl , refl , refl , refl

  sum-inj : ∀ {A B A′ B′ : Ty m} → (A + B) ≡ (A′ + B′) → (A ≡ A′) × (B ≡ B′)
  sum-inj refl = refl , refl

  cod-eq : ∀ {Z A B A′ B′ : Ty m} {q q′ π π′}
         → Z ≡ A ⇒[ mk-kind q π ] B → Z ≡ A′ ⇒[ mk-kind q′ π′ ] B′ → B ≡ B′
  cod-eq refl e = proj₂ (proj₂ (proj₂ (arr-inj e)))

  grd-eq : ∀ {A B A′ B′ : Ty m} {q q′ π π′}
         → A ⇒[ mk-kind q π ] B ≡ A′ ⇒[ mk-kind q′ π′ ] B′ → π ≡ π′
  grd-eq e = proj₁ (proj₂ (proj₂ (arr-inj e)))

  cod-cong : ∀ {A B B′ : Ty m} {k} → B ≡ B′ → (A ⇒[ k ] B) ≡ (A ⇒[ k ] B′)
  cod-cong refl = refl

  fin-inj : ∀ {f g} → fin f ≡ fin g → f ≡ g
  fin-inj refl = refl

  ty-ctx : ∀ {n} {Γ : SCx.Ctx m n} {A A′ Ψ t B π} → A ≡ A′
         → Δ ⊩ (Γ SCx.▸ A) ⊢[ Ψ ] t ∷ B ! π → Δ ⊩ (Γ SCx.▸ A′) ⊢[ Ψ ] t ∷ B ! π
  ty-ctx refl d = d

  ia-cod : ∀ {op p} → SU.IntArith op p → primCod {m} p ≡ Int
  ia-cod SU.ia-add = refl
  ia-cod SU.ia-sub = refl
  ia-cod SU.ia-mul = refl
  ia-cod SU.ia-div = refl
  ia-cod SU.ia-mod = refl

  fa-cod : ∀ {op p} → SU.FloatArith op p → primCod {m} p ≡ Float
  fa-cod SU.fa-add = refl
  fa-cod SU.fa-sub = refl
  fa-cod SU.fa-mul = refl
  fa-cod SU.fa-div = refl

  cmp-cod : ∀ {op p} → SU.Compare op p → primCod {m} p ≡ Unit + Unit
  cmp-cod SU.cmp-lt = refl
  cmp-cod SU.cmp-le = refl
  cmp-cod SU.cmp-gt = refl
  cmp-cod SU.cmp-ge = refl
  cmp-cod SU.cmp-eq = refl
  cmp-cod SU.cmp-ne = refl

------------------------------------------------------------------------
-- References
------------------------------------------------------------------------

private
  module _ {n} {L : SU.Locals m n} where

    sigop-at : ∀ {c t Φ} (ng : NotGenerator c)
             → Σ[ T ∈ Type ] ((c ∶ declS T) ∈ Σ) × (⌜ t ⌝ᵈ ≡ ⌜ declS T ⌝ᵈ) × OkS c T × IsConcrete T × HonestFFI T
             → A⇒ L (Once.Spec.Surface.Syntax.RResolved c) ⌜ t ⌝ᵈ Φ
    sigop-at {c} {Φ = Φ} ng (T , mem , e , ok , k , h) =
      subst (λ Z → A⇒ L (Once.Spec.Surface.Syntax.RResolved c) Z Φ) (sym e) (a⇒ (SU.s-sigop ng mem) (u-sigop {ok = ok} k h) (z⊑ Φ))

------------------------------------------------------------------------
-- The annotation
------------------------------------------------------------------------

mutual
  ann⇒ : ∀ {n bnd} {L : SU.Locals m n} {e e′ A t}
       → L ⊢ e′ ⇒ A ↝ t → RX bnd e e′
       → ∀ {Φ X π} → Δ ⊩ ctxOf L ⊢[ Φ ] t ∷ X ! π → (X ≡ A) × A⇒ L e′ A Φ
  ann⇐ : ∀ {n bnd} {L : SU.Locals m n} {e e′ A t}
       → L ⊢ e′ ⇐ A ↝ t → RX bnd e e′
       → ∀ {Φ X π} → Δ ⊩ ctxOf L ⊢[ Φ ] t ∷ X ! π → (X ≡ A) × A⇐ L e′ A Φ
  ann↦ : ∀ {n bnd} {L : SU.Locals m n} {e e′ A π B t}
       → L ⊢ e′ ⇐ A ⇒[ π ]↦ B ↝ t → RX bnd e e′
       → ∀ {Φ X π₀} → Δ ⊩ ctxOf L ⊢[ Φ ] t ∷ X ! π₀ → (X ≡ A ⇒⟨ π ⟩ B) × A↦ L e′ A π B Φ

  ----------------------------------------------------------------------
  -- Synthesis
  ----------------------------------------------------------------------

  ann⇒ (SU.s-int i) x-int {Φ} T = inv-lit-int T , a⇒ (SU.s-int i) u-int (z⊑ Φ)
  ann⇒ (SU.s-float i f l) x-float {Φ} T = inv-lit-float T , a⇒ (SU.s-float i f l) u-float (z⊑ Φ)
  ann⇒ SU.s-unit x-unit {Φ} T = inv-unit T , a⇒ SU.s-unit u-unit (z⊑ Φ)
  ann⇒ SU.s-unit-g (x-res _) {Φ} T = inv-unit T , a⇒ SU.s-unit-g u-unit-g (z⊑ Φ)
  ann⇒ (SU.s-var v) (x-local _) T =
    trans (proj₁ (inv-var T)) (lookup-at v) , a⇒ (SU.s-var v) u-var (proj₂ (inv-var T))
  ann⇒ (SU.s-sigop {t = t} ng mem) (x-res _) T = inv-sigop T , sigop-at {t = t} ng (ok-sig ng mem)
  ann⇒ (SU.s-def d e τ ar) (x-res nm′) {Φ} T = inv-ref T , a⇒ (SU.s-def d e τ ar) (u-def {ok = ok-def d e nm′}) (z⊑ Φ)
  ann⇒ (SU.s-annot d) (x-annot x) T =
    let (eq , a⇐ der u w) = ann⇐ d x T in eq , a⇒ (SU.s-annot der) (u-annot u) w
  ann⇒ (SU.s-pair da db) (x-pair xa xb) T =
    let p = inv-pair T
        (ea , a⇒ dA uA wA) = ann⇒ da xa (IPair.da p) ; (eb , a⇒ dB uB wB) = ann⇒ db xb (IPair.db p)
    in trans (IPair.ty p) (cong₂ _*_ ea eb) , a⇒ (SU.s-pair dA dB) (u-pair uA uB) (⊑ᵘ-trans (⊑ᵘ-+ wA wB) (IPair.use p))
  ann⇒ (SU.s-neg d) (x-neg x) T =
    let r = inv-prim T ; (_ , a⇒ der u w) = ann⇒ d x (IPrim.dt r)
    in IPrim.ty r , a⇒ (SU.s-neg der) (u-neg u) (⊑ᵘ-trans w (IPrim.use r))
  ann⇒ (SU.s-neg-float i f l) (x-neg x-float) {Φ} T = inv-lit-float T , a⇒ (SU.s-neg-float i f l) u-neg-float (z⊑ Φ)
  -- the binder takes the quantity its body uses
  ann⇒ (SU.s-let q d₁ d₂) (x-let x₁ x₂) T =
    let r = inv-let T ; (e₁ , a⇒ D₁ u₁ w₁) = ann⇒ d₁ x₁ (ILet.de r)
    in let-go r e₁ D₁ u₁ w₁ (ann⇒ d₂ x₂ (ty-ctx e₁ (ILet.db r)))
    where
      let-go : ∀ {n} {L : SU.Locals m n} {x e₁ e₂ A B t₁ t₂ Φ X} (r : ILet {Γ = ctxOf L} Φ q t₁ t₂ X)
             → ILet.A r ≡ A → ∀ {t₁′} (D₁ : L ⊢ e₁ ⇒ A ↝ t₁′) → ∀ {Ψ₁} → Use⇒ D₁ Ψ₁ → Ψ₁ ⊑ᵘ ILet.Φ₁ r
             → (X ≡ B) × A⇒ (L SU.▹ x ∶ A) e₂ B (q ∷ ILet.Φ₂ r)
             → (X ≡ B) × A⇒ L (Once.Spec.Surface.Syntax.RLet x e₁ e₂) B Φ
      let-go r _ D₁ u₁ w₁ (e₂ , a⇒ D₂ {q₀ ∷ Ψ₂} u₂ w₂) =
        e₂ , a⇒ (SU.s-let q₀ D₁ D₂) (u-let u₁ u₂) (⊑ᵘ-trans (app⊑ (⊑-tail w₂) w₁ (⊑-head w₂)) (ILet.use r))
  ann⇒ (SU.s-case {Cl = Cl} {Cr = Cr} {C = C} ql qr ds dl dr J) (x-destruct xs xl xr) T =
    let r = inv-case T ; (es , a⇒ Ds us ws) = ann⇒ ds xs (ICase.ds r)
        (eA , eB) = sum-inj es
        cl = inv-coerce (ICase.dl r) ; cr = inv-coerce (ICase.dr r)
    in ICoerce.ty cl
       , branches r Ds us ws (proj₂ (ann⇒ dl xl (ty-ctx eA (ICoerce.dt cl)))) (proj₂ (ann⇒ dr xr (ty-ctx eB (ICoerce.dt cr))))
                  (ICoerce.use cl) (ICoerce.use cr)
    where
      branches : ∀ {n} {L : SU.Locals m n} {e xl el xr er A B ts tl tr Φ X Φl Φr}
                 (r : ICase {Γ = ctxOf L} Φ ql qr ts tl tr X)
               → ∀ {ts′} (Ds : L ⊢ e ⇒ A + B ↝ ts′) → ∀ {Ψs} → Use⇒ Ds Ψs → Ψs ⊑ᵘ ICase.Φs r
               → A⇒ (L SU.▹ xl ∶ A) el Cl Φl → A⇒ (L SU.▹ xr ∶ B) er Cr Φr
               → Φl ⊑ᵘ (ql ∷ ICase.Ψ r) → Φr ⊑ᵘ (qr ∷ ICase.Ψ r)
               → A⇒ L (Once.Spec.Surface.Syntax.RDestruct e xl el xr er) C Φ
      branches r Ds us ws (a⇒ Dl {ql₀ ∷ Ψl} ul wl) (a⇒ Dr {qr₀ ∷ Ψr} ur wr) vl vr =
        a⇒ (SU.s-case {C = C} ql₀ qr₀ Ds Dl Dr J) (u-case us ul ur)
           (⊑ᵘ-trans (⊑ᵘ-+ ws (⊔⊑ (⊑-tail (⊑ᵘ-trans wl vl)) (⊑-tail (⊑ᵘ-trans wr vr)))) (ICase.use r))
  ann⇒ (SU.s-arith ia d₁ d₂) (x-binop x₁ x₂) T =
    let r = inv-prim T ; p = inv-pair (IPrim.dt r)
        (_ , a⇒ D₁ u₁ w₁) = ann⇒ d₁ x₁ (IPair.da p) ; (_ , a⇒ D₂ u₂ w₂) = ann⇒ d₂ x₂ (IPair.db p)
    in trans (IPrim.ty r) (ia-cod ia)
       , a⇒ (SU.s-arith ia D₁ D₂) (u-arith u₁ u₂) (⊑ᵘ-trans (⊑ᵘ-+ w₁ w₂) (⊑ᵘ-trans (IPair.use p) (IPrim.use r)))
  ann⇒ (SU.s-arith-float fa d₁ d₂) (x-binop x₁ x₂) T =
    let r = inv-prim T ; p = inv-pair (IPrim.dt r)
        (_ , a⇒ D₁ u₁ w₁) = ann⇒ d₁ x₁ (IPair.da p) ; (_ , a⇒ D₂ u₂ w₂) = ann⇒ d₂ x₂ (IPair.db p)
    in trans (IPrim.ty r) (fa-cod fa)
       , a⇒ (SU.s-arith-float fa D₁ D₂) (u-arith-float u₁ u₂) (⊑ᵘ-trans (⊑ᵘ-+ w₁ w₂) (⊑ᵘ-trans (IPair.use p) (IPrim.use r)))
  ann⇒ (SU.s-arith-float-il fa d₁ d₂) (x-binop x₁ x₂) T =
    let r = inv-prim T ; p = inv-pair (IPrim.dt r) ; w = inv-prim (IPair.da p)
        (_ , a⇒ D₁ u₁ w₁) = ann⇒ d₁ x₁ (IPrim.dt w) ; (_ , a⇒ D₂ u₂ w₂) = ann⇒ d₂ x₂ (IPair.db p)
    in trans (IPrim.ty r) (fa-cod fa)
       , a⇒ (SU.s-arith-float-il fa D₁ D₂) (u-arith-float-il u₁ u₂)
            (⊑ᵘ-trans (⊑ᵘ-+ (⊑ᵘ-trans w₁ (IPrim.use w)) w₂) (⊑ᵘ-trans (IPair.use p) (IPrim.use r)))
  ann⇒ (SU.s-arith-float-ir fa d₁ d₂) (x-binop x₁ x₂) T =
    let r = inv-prim T ; p = inv-pair (IPrim.dt r) ; w = inv-prim (IPair.db p)
        (_ , a⇒ D₁ u₁ w₁) = ann⇒ d₁ x₁ (IPair.da p) ; (_ , a⇒ D₂ u₂ w₂) = ann⇒ d₂ x₂ (IPrim.dt w)
    in trans (IPrim.ty r) (fa-cod fa)
       , a⇒ (SU.s-arith-float-ir fa D₁ D₂) (u-arith-float-ir u₁ u₂)
            (⊑ᵘ-trans (⊑ᵘ-+ w₁ (⊑ᵘ-trans w₂ (IPrim.use w))) (⊑ᵘ-trans (IPair.use p) (IPrim.use r)))
  ann⇒ (SU.s-compare c d₁ d₂) (x-binop x₁ x₂) T =
    let r = inv-prim T ; p = inv-pair (IPrim.dt r)
        (_ , a⇒ D₁ u₁ w₁) = ann⇒ d₁ x₁ (IPair.da p) ; (_ , a⇒ D₂ u₂ w₂) = ann⇒ d₂ x₂ (IPair.db p)
    in trans (IPrim.ty r) (cmp-cod c)
       , a⇒ (SU.s-compare c D₁ D₂) (u-compare u₁ u₂) (⊑ᵘ-trans (⊑ᵘ-+ w₁ w₂) (⊑ᵘ-trans (IPair.use p) (IPrim.use r)))
  ann⇒ (SU.s-id-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (idᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-id-app D) (u-id-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-fst-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (fstᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-fst-app D) (u-fst-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-snd-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (sndᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-snd-app D) (u-snd-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-terminal-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (terminalᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-terminal-app D) (u-terminal-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-apply-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (applyᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-apply-app D) (u-apply-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-apply-eff-app g d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (applyEffᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-apply-eff-app g D) (u-apply-eff-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-Out-app wf d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (outᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-Out-app wf D) (u-Out-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-Out-act-app wf d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (outActᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇒ (SU.s-Out-act-app wf D) (u-Out-act-app u) (gen⊑ w eq (IApp.use a))
  ann⇒ (SU.s-app ns df dx) (x-app xf xx) T =
    let a = inv-app T ; (ef , a⇒ DF uF wF) = ann⇒ df xf (IApp.df a) ; (_ , eq , _ , eX) = arr-inj ef
        (_ , a⇐ DX uX wX) = ann⇐ dx xx (IApp.dx a)
    in eX , a⇒ (SU.s-app ns DF DX) (u-app uF uX) (⊑ᵘ-trans (app⊑ wF wX (≤q-≡ (sym eq))) (IApp.use a))
  ann⇒ (SU.s-effApp ns g df dx) (x-app xf xx) T =
    let (A₁ , q , πa , B₀ , πf , πx , Φf , Φx , dF , dX , use , eX) = effApp-inv T
        (ef , a⇒ DF uF wF) = ann⇒ df xf dF ; (_ , eq , _ , eB) = arr-inj ef
        (_ , a⇐ DX uX wX) = ann⇐ dx xx dX
    in trans eX (cod-cong eB) , a⇒ (SU.s-effApp ns g DF DX) (u-effApp uF uX) (⊑ᵘ-trans (app⊑ wF wX (≤q-≡ (sym eq))) use)
  ann⇒ (SU.s-app-spine ns dx df) (x-app xf xx) T =
    let a = inv-app T ; (_ , a⇒ DX uX wX) = ann⇒ dx xx (IApp.dx a)
        (ef , a↦ DF uF wF) = ann↦ df xf (IApp.df a) ; (_ , eq , _ , eT) = arr-inj ef
    in eT , a⇒ (SU.s-app-spine ns DX DF) (u-app-spine uX uF) (⊑ᵘ-trans (app⊑ wF wX (≤q-≡ (sym eq))) (IApp.use a))

  ----------------------------------------------------------------------
  -- Checking
  ----------------------------------------------------------------------

  ann⇐ SU.c-id (x-res _) {Φ} T = idᶜ-ty T , a⇐ SU.c-id u-id (z⊑ Φ)
  ann⇐ SU.c-fst (x-res _) {Φ} T = fstᶜ-ty T , a⇐ SU.c-fst u-fst (z⊑ Φ)
  ann⇐ SU.c-snd (x-res _) {Φ} T = sndᶜ-ty T , a⇐ SU.c-snd u-snd (z⊑ Φ)
  ann⇐ SU.c-terminal (x-res _) {Φ} T = terminalᶜ-ty T , a⇐ SU.c-terminal u-terminal (z⊑ Φ)
  ann⇐ SU.c-initial (x-res _) {Φ} T = initialᶜ-ty T , a⇐ SU.c-initial u-initial (z⊑ Φ)
  ann⇐ SU.c-inl (x-res _) {Φ} T = inlᶜ-ty T , a⇐ SU.c-inl u-inl (z⊑ Φ)
  ann⇐ SU.c-inr (x-res _) {Φ} T = inrᶜ-ty T , a⇐ SU.c-inr u-inr (z⊑ Φ)
  ann⇐ (SU.c-compose-g dg df) (x-app (x-app (x-res _) xf) xg) T =
    let (r , M , q , πa , C₀ , eF , eX) = compose-inv T
        (_ , a↦ DG uG wG) = ann↦ dg xg (Two.dg r) ; (ef , a⇐ DF uF wF) = ann⇐ df xf (Two.df r)
    in trans eX (cod-cong (cod-eq eF ef))
       , a⇐ (SU.c-compose-g DG DF) (u-compose-g uG uF) (⊑ᵘ-trans (app⊑ wF wG ω≤ω) (Two.use r))
  ann⇐ (SU.c-compose-f df sub dg) (x-app (x-app (x-res _) xf) xg) T =
    let (r , M , q , πa , C₀ , eF , eX) = compose-inv T ; cf = inv-coerce (Two.df r)
        (_ , a⇒ DF uF wF) = ann⇒ df xf (ICoerce.dt cf) ; (_ , a⇐ DG uG wG) = ann⇐ dg xg (Two.dg r)
    in trans eX (cod-cong (cod-eq eF (ICoerce.ty cf)))
       , a⇐ (SU.c-compose-f DF sub DG) (u-compose-f uF uG) (⊑ᵘ-trans (app⊑ (⊑ᵘ-trans wF (ICoerce.use cf)) wG ω≤ω) (Two.use r))
  ann⇐ (SU.c-case df dg) (x-app (x-app (x-res _) xf) xg) T =
    let (r , C₀ , (_ , _ , _ , eF) , _ , eX) = case-inv T
        (ef , a⇐ DF uF wF) = ann⇐ df xf (Two.df r) ; (_ , a⇐ DG uG wG) = ann⇐ dg xg (Two.dg r)
    in trans eX (cod-cong (cod-eq eF ef)) , a⇐ (SU.c-case DF DG) (u-case uF uG) (one⊑ wF wG (Two.use r))
  ann⇐ (SU.c-pair df dg) (x-app (x-app (x-res _) xf) xg) T =
    let (r , B₀ , C₀ , (_ , _ , _ , eF) , (_ , _ , _ , eG) , eX) = pair-inv T
        (ef , a⇐ DF uF wF) = ann⇐ df xf (Two.df r) ; (eg , a⇐ DG uG wG) = ann⇐ dg xg (Two.dg r)
    in trans eX (cod-cong (cong₂ _*_ (cod-eq eF ef) (cod-eq eG eg)))
       , a⇐ (SU.c-pair DF DG) (u-pair uF uG) (one⊑ wF wG (Two.use r))
  ann⇐ (SU.c-curry df) (x-app (x-res _) xf) T =
    let (r , M , q , πa , C₀ , eF , eX) = curry-inv T ; (ef , a⇐ DF uF wF) = ann⇐ df xf (One′.df r)
    in trans eX (cod-cong (cod-cong (cod-eq eF ef))) , a⇐ (SU.c-curry DF) (u-curry uF) (one⊑′ wF (One′.use r))
  ann⇐ (SU.c-cata wf dalg) (x-app (x-res _) xa) T =
    let (r , A₀ , π₁ , eF , eX) = cata-inv T ; (ef , a⇐ DA uA wA) = ann⇐ dalg xa (One′.df r)
    in trans eX (cod-cong (cod-eq eF ef)) , a⇐ (SU.c-cata wf DA) (u-cata uA) (many⊑ wA (One′.use r))
  ann⇐ (SU.c-ana le wf dc) (x-app (x-res _) xc) T =
    let (f₀ , A₁ , πc , Φc , dc′ , use , eX) = ana-inv T ; (ec , a⇐ DC uC wC) = ann⇐ dc xc dc′
    in trans eX (cong (λ g → _ ⇒⟨ _ ⟩ ν _ g) (fin-inj (grd-eq ec))) , a⇐ (SU.c-ana le wf DC) (u-ana uC) (many⊑ wC use)
  ann⇐ (SU.c-loop dc) (x-app (x-res _) xc) T =
    let (r , A₁ , B₀ , eF , eX) = loop-inv T ; (ef , a⇐ DC uC wC) = ann⇐ dc xc (One′.df r)
    in trans eX (cod-cong (proj₁ (sum-inj (cod-eq eF ef)))) , a⇐ (SU.c-loop DC) (u-loop uC) (many⊑ wC (One′.use r))
  ann⇐ (SU.c-sub ds sub) x T =
    let c = inv-coerce T ; (_ , a⇒ D u w) = ann⇒ ds x (ICoerce.dt c)
    in ICoerce.ty c , a⇐ (SU.c-sub D sub) (u-sub u) (⊑ᵘ-trans w (ICoerce.use c))
  ann⇐ (SU.c-lam {q = q} db) (x-lam xb) T =
    let l = inv-lam T in lam-go l (ann⇐ db xb (ILam.body l))
    where
      lam-go : ∀ {n} {L : SU.Locals m n} {x body A B π t Φ X} (l : ILam {Γ = ctxOf L} Φ A q π t X)
             → (ILam.B l ≡ B) × A⇐ (L SU.▹ x ∶ A) body B (ILam.q′ l ∷ ILam.Ψ l)
             → (X ≡ A ⇒[ mk-kind q π ] B) × A⇐ L (Once.Spec.Surface.Syntax.RLam x body) (A ⇒[ mk-kind q π ] B) Φ
      lam-go l (eB , a⇐ D {q₀ ∷ Ψ₀} u w) =
        trans (ILam.ty l) (cod-cong eB)
        , a⇐ (SU.c-lam D) (u-lam (≤q-L q₀ q (≤q-trans (⊑-head w) (ILam.le l))) u) (⊑ᵘ-trans (⊑-tail w) (ILam.use l))
  ann⇐ (SU.c-pair-lit da db) (x-pair xa xb) T =
    let p = inv-pair T
        (ea , a⇐ DA uA wA) = ann⇐ da xa (IPair.da p) ; (eb , a⇐ DB uB wB) = ann⇐ db xb (IPair.db p)
    in trans (IPair.ty p) (cong₂ _*_ ea eb) , a⇐ (SU.c-pair-lit DA DB) (u-pair-lit uA uB) (⊑ᵘ-trans (⊑ᵘ-+ wA wB) (IPair.use p))
  ann⇐ (SU.c-In-app wf d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (inᶜ-ty (IApp.df a)) ; (_ , a⇐ D u w) = ann⇐ d x (IApp.dx a)
    in eX , a⇐ (SU.c-In-app wf D) (u-In-app u) (gen⊑ w eq (IApp.use a))
  ann⇐ (SU.c-apply-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (applyᶜ-ty (IApp.df a)) ; (_ , a⇒ D u w) = ann⇒ d x (IApp.dx a)
    in eX , a⇐ (SU.c-apply-app D) (u-apply-app u) (gen⊑ w eq (IApp.use a))
  ann⇐ (SU.c-inl-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (inlᶜ-ty (IApp.df a)) ; (_ , a⇐ D u w) = ann⇐ d x (IApp.dx a)
    in eX , a⇐ (SU.c-inl-app D) (u-inl-app u) (gen⊑ w eq (IApp.use a))
  ann⇐ (SU.c-inr-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (inrᶜ-ty (IApp.df a)) ; (_ , a⇐ D u w) = ann⇐ d x (IApp.dx a)
    in eX , a⇐ (SU.c-inr-app D) (u-inr-app u) (gen⊑ w eq (IApp.use a))
  ann⇐ (SU.c-initial-app d) (x-app (x-res _) x) T =
    let a = inv-app T ; (_ , eq , _ , eX) = arr-inj (initialᶜ-ty (IApp.df a)) ; (_ , a⇐ D u w) = ann⇐ d x (IApp.dx a)
    in eX , a⇐ (SU.c-initial-app D) (u-initial-app u) (gen⊑ w eq (IApp.use a))
  ann⇐ (SU.c-poly d e pos τ resp) (x-res nm′) {Φ} T =
    inv-ref T , a⇐ (SU.c-poly d e pos τ resp) (u-poly {ok = ok-def d e nm′}) (z⊑ Φ)

  ----------------------------------------------------------------------
  -- An arrow out of a given domain
  ----------------------------------------------------------------------

  ann↦ (SU.d-infer dg sub le) x T =
    let c = inv-coerce T ; (_ , a⇒ D u w) = ann⇒ dg x (ICoerce.dt c)
    in ICoerce.ty c , a↦ (SU.d-infer D sub le) (u-infer u) (⊑ᵘ-trans w (ICoerce.use c))
  ann↦ (SU.d-poly d e pos eT occ τ resp eA eB le) (x-res nm′) {Φ} T =
    ICoerce.ty (inv-coerce T) , a↦ (SU.d-poly d e pos eT occ τ resp eA eB le) (u-poly {ok = ok-def d e nm′}) (z⊑ Φ)
  ann↦ (SU.d-lam db) (x-lam xb) T =
    let l = inv-lam T in lam-go l (ann⇒ db xb (ILam.body l))
    where
      lam-go : ∀ {n} {L : SU.Locals m n} {x body A B π t Φ X} (l : ILam {Γ = ctxOf L} Φ A Many π t X)
             → (ILam.B l ≡ B) × A⇒ (L SU.▹ x ∶ A) body B (ILam.q′ l ∷ ILam.Ψ l)
             → (X ≡ A ⇒⟨ π ⟩ B) × A↦ L (Once.Spec.Surface.Syntax.RLam x body) A π B Φ
      lam-go l (eB , a⇒ D {q₀ ∷ Ψ₀} u w) =
        trans (ILam.ty l) (cod-cong eB) , a↦ (SU.d-lam D) (u-lam u) (⊑ᵘ-trans (⊑-tail w) (ILam.use l))
  ann↦ (SU.d-compose dg df) (x-app (x-app (x-res _) xf) xg) T =
    let (r , M , q , πa , C₀ , eF , eX) = compose-inv T
        (_ , a↦ DG uG wG) = ann↦ dg xg (Two.dg r) ; (ef , a↦ DF uF wF) = ann↦ df xf (Two.df r)
    in trans eX (cod-cong (cod-eq eF ef))
       , a↦ (SU.d-compose DG DF) (u-compose uG uF) (⊑ᵘ-trans (app⊑ wF wG ω≤ω) (Two.use r))
  ann↦ SU.d-id (x-res _) {Φ} T = idᶜ-ty T , a↦ SU.d-id u-id (z⊑ Φ)
  ann↦ SU.d-fst (x-res _) {Φ} T = fstᶜ-ty T , a↦ SU.d-fst u-fst (z⊑ Φ)
  ann↦ SU.d-snd (x-res _) {Φ} T = sndᶜ-ty T , a↦ SU.d-snd u-snd (z⊑ Φ)
  ann↦ SU.d-terminal (x-res _) {Φ} T = terminalᶜ-ty T , a↦ SU.d-terminal u-terminal (z⊑ Φ)
  ann↦ SU.d-initial (x-res _) {Φ} T = initialᶜ-ty T , a↦ SU.d-initial u-initial (z⊑ Φ)
  ann↦ (SU.d-case df dg J) (x-app (x-app (x-res _) xf) xg) T =
    let (r , C₀ , (_ , _ , _ , eF) , _ , eX) = case-inv T
        cf = inv-coerce (Two.df r) ; cg = inv-coerce (Two.dg r)
        (_ , a↦ DF uF wF) = ann↦ df xf (ICoerce.dt cf) ; (_ , a↦ DG uG wG) = ann↦ dg xg (ICoerce.dt cg)
    in trans eX (cod-cong (cod-eq eF (ICoerce.ty cf)))
       , a↦ (SU.d-case DF DG J) (u-case uF uG) (one⊑ (⊑ᵘ-trans wF (ICoerce.use cf)) (⊑ᵘ-trans wG (ICoerce.use cg)) (Two.use r))
  ann↦ (SU.d-pair df dg) (x-app (x-app (x-res _) xf) xg) T =
    let (r , B₀ , C₀ , (_ , _ , _ , eF) , (_ , _ , _ , eG) , eX) = pair-inv T
        (ef , a↦ DF uF wF) = ann↦ df xf (Two.df r) ; (eg , a↦ DG uG wG) = ann↦ dg xg (Two.dg r)
    in trans eX (cod-cong (cong₂ _*_ (cod-eq eF ef) (cod-eq eG eg)))
       , a↦ (SU.d-pair DF DG) (u-pair uF uG) (one⊑ wF wG (Two.use r))
  ann↦ (SU.d-cata wf da) (x-app (x-res _) xa) T =
    let (r , A₀ , π₁ , eF , eX) = cata-inv T ; (ef , a⇒ DA uA wA) = ann⇒ da xa (One′.df r)
    in trans eX (cod-cong (cod-eq eF ef)) , a↦ (SU.d-cata wf DA) (u-cata uA) (many⊑ wA (One′.use r))
