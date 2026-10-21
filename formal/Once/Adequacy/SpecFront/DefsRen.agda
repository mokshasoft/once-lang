-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- Once.Adequacy.SpecFront.DefsRen — the Spec's typing does not depend on the
-- order a schema lists its variables in (plan 0.121 `complete`).
--
-- A schema numbers its type variables, and the Spec leaves the numbering
-- free (`SchemaOf`: any distinct names). Two definitions tables whose
-- schemas agree up to renumbering (`Ren`, `SchemaRen.SchRen`: each instance of
-- `S₁`'s schema is one of `S₂`'s, renumbered by `ρ`) type the same
-- expressions, at the same types: a derivation over `S₁` is one over `S₂`,
-- of its term with each reference's instance renumbered (`rn`) — the core
-- judgment (`core`) and the surface one (`syn`, `chk`, `dom`).
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _<_)
open import Data.Fin using (Fin)
open import Once.Spec.Signature using (Signature)
open import Once.Spec.Name using (CanonicalName)
open import Once.Spec.Core.Syntax using (Defs; _!!_; module Schema)

module Once.Adequacy.SpecFront.DefsRen
  (Σ : Signature) {s : ℕ} (S₁ S₂ : Defs s) (nm : Fin s → CanonicalName)
  (ρ : ∀ d → Fin (Schema.arity (S₂ !! d)) → Fin (Schema.arity (S₁ !! d))) where

open import Data.Fin using (zero; suc)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Once.Spec.Grade using (Purity; mk-kind; Many)
open import Once.Spec.Type using (Ty; KCtx; TySub; Respects; _⟨_⟩; Occurs; _⇒[_]_)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived
open import Once.Adequacy.SpecFront.SchemaRen using (SchRen)
import Once.Spec.Surface.Syntax
import Relation.Nullary
open Schema using (arity; kinds; type)
import Once.Spec.Core.Typing Σ S₁ as C₁
import Once.Spec.Core.Typing Σ S₂ as C₂
import Once.Spec.Surface.Typing Σ S₁ nm as U₁
import Once.Spec.Surface.Typing Σ S₂ nm as U₂

------------------------------------------------------------------------
-- The terms
------------------------------------------------------------------------

-- each reference's instance, renumbered
rn : ∀ {m n} → Tm S₁ m n → Tm S₂ m n
rn (var i)             = var i
rn (lam A q π t)       = lam A q π (rn t)
rn (app f x)           = app (rn f) (rn x)
rn (let′ q e b)        = let′ q (rn e) (rn b)
rn unit                = unit
rn (pair a b)          = pair (rn a) (rn b)
rn (fst p)             = fst (rn p)
rn (snd p)             = snd (rn p)
rn (inl B a)           = inl B (rn a)
rn (inr A b)           = inr A (rn b)
rn (case qℓ qr e l r)  = case qℓ qr (rn e) (rn l) (rn r)
rn (absurd A e)        = absurd A (rn e)
rn (roll F t)          = roll F (rn t)
rn (fold F alg t)      = fold F (rn alg) (rn t)
rn (unfold F c a)      = unfold F (rn c) (rn a)
rn (out t)             = out (rn t)
rn (iter f a)          = iter (rn f) (rn a)
rn (coerce A B t)      = coerce A B (rn t)
rn (lit l)             = lit l
rn (prim p t)          = prim p (rn t)
rn (sigop c t)         = sigop c t
rn (ref d τ)           = ref d (λ i → τ (ρ d i))

module _ {m : ℕ} where
  -- …which commutes with renaming the term's variables
  rn-ren : ∀ {n n′} (σ : Fin n → Fin n′) (t : Tm S₁ m n) → rn (ren σ t) ≡ ren σ (rn t)
  rn-ren σ (var i)             = refl
  rn-ren σ (lam A q π t)       = cong (lam A q π) (rn-ren (ext {S = S₁} {m = m} σ) t)
  rn-ren σ (app f x)           = cong₂ app (rn-ren σ f) (rn-ren σ x)
  rn-ren σ (let′ q e b)        = cong₂ (let′ q) (rn-ren σ e) (rn-ren (ext {S = S₁} {m = m} σ) b)
  rn-ren σ unit                = refl
  rn-ren σ (pair a b)          = cong₂ pair (rn-ren σ a) (rn-ren σ b)
  rn-ren σ (fst p)             = cong fst (rn-ren σ p)
  rn-ren σ (snd p)             = cong snd (rn-ren σ p)
  rn-ren σ (inl B a)           = cong (inl B) (rn-ren σ a)
  rn-ren σ (inr A b)           = cong (inr A) (rn-ren σ b)
  rn-ren σ (case qℓ qr e l r)  =
    trans (cong₂ (λ x y → case qℓ qr x y (rn (ren (ext {S = S₁} {m = m} σ) r))) (rn-ren σ e) (rn-ren (ext {S = S₁} {m = m} σ) l))
          (cong (case qℓ qr (ren σ (rn e)) (ren (ext {S = S₁} {m = m} σ) (rn l))) (rn-ren (ext {S = S₁} {m = m} σ) r))
  rn-ren σ (absurd A e)        = cong (absurd A) (rn-ren σ e)
  rn-ren σ (roll F t)          = cong (roll F) (rn-ren σ t)
  rn-ren σ (fold F alg t)      = cong₂ (fold F) (rn-ren σ alg) (rn-ren σ t)
  rn-ren σ (unfold F c a)      = cong₂ (unfold F) (rn-ren σ c) (rn-ren σ a)
  rn-ren σ (out t)             = cong out (rn-ren σ t)
  rn-ren σ (iter f a)          = cong₂ iter (rn-ren σ f) (rn-ren σ a)
  rn-ren σ (coerce A B t)      = cong (coerce A B) (rn-ren σ t)
  rn-ren σ (lit l)             = refl
  rn-ren σ (prim p t)          = cong (prim p) (rn-ren σ t)
  rn-ren σ (sigop c t)         = refl
  rn-ren σ (ref d τ)           = refl

private
  rn-wk : ∀ {m n} (t : Tm S₁ m n) → rn (wk t) ≡ wk (rn t)
  rn-wk = rn-ren suc

-- The derived combinators with subterms.
rn-compose : ∀ {m n} A π (f g : Tm S₁ m n) → rn (composeᶜ A π f g) ≡ composeᶜ A π (rn f) (rn g)
rn-compose A π f g = cong (λ x → let′ _ (rn f) (let′ _ x _)) (rn-wk g)

rn-pair : ∀ {m n} A π (f g : Tm S₁ m n) → rn (pairᶜ A π f g) ≡ pairᶜ A π (rn f) (rn g)
rn-pair A π f g = cong (λ x → let′ _ (rn f) (let′ _ x _)) (rn-wk g)

rn-case : ∀ {m n} A B π (f g : Tm S₁ m n) → rn (caseᶜ A B π f g) ≡ caseᶜ A B π (rn f) (rn g)
rn-case A B π f g = cong (λ x → let′ _ (rn f) (let′ _ x _)) (rn-wk g)

rn-ana : ∀ {m n} F A π (c : Tm S₁ m n) → rn (anaᶜ F A π c) ≡ anaᶜ F A π (rn c)
rn-ana F A π c = cong (λ x → lam _ _ _ (unfold F x _)) (rn-wk c)

rn-effApp : ∀ {m n} π (f x : Tm S₁ m n) → rn (effAppᶜ π f x) ≡ effAppᶜ π (rn f) (rn x)
rn-effApp π f x = cong₂ (λ a b → lam _ _ _ (app a b)) (rn-wk f) (rn-wk x)

------------------------------------------------------------------------
-- The schemas, agreeing up to renumbering
------------------------------------------------------------------------

-- The tables agree up to renumbering, schema by schema.
Ren : Set
Ren = ∀ d → SchRen (S₁ !! d) (S₂ !! d) (ρ d)

module _ (R : Ren) where
  private
    ty : ∀ d {m} (τ : TySub (arity (S₁ !! d)) m) → type (S₂ !! d) ⟨ (λ i → τ (ρ d i)) ⟩ ≡ type (S₁ !! d) ⟨ τ ⟩
    ty d = SchRen.ty (R d)
    resp : ∀ d {m} {Δ : KCtx m} (τ : TySub (arity (S₁ !! d)) m)
         → Respects (kinds (S₁ !! d)) Δ τ → Respects (kinds (S₂ !! d)) Δ (λ i → τ (ρ d i))
    resp d = SchRen.resp (R d)
    ground : ∀ d → arity (S₁ !! d) ≡ 0 → arity (S₂ !! d) ≡ 0
    ground d = SchRen.ground (R d)
    open′ : ∀ d → 0 < arity (S₁ !! d) → 0 < arity (S₂ !! d)
    open′ d = SchRen.open′ (R d)

  ------------------------------------------------------------------------
  -- The core judgment
  ------------------------------------------------------------------------

  core : ∀ {m} {Δ : KCtx m} {n} {Γ Ψ t A π} → C₁._⊩_⊢[_]_∷_!_ Δ {n} Γ Ψ t A π → C₂._⊩_⊢[_]_∷_!_ Δ Γ Ψ (rn t) A π
  core (C₁.⊢var i)               = C₂.⊢var i
  core (C₁.⊢lam q D)             = C₂.⊢lam q (core D)
  core (C₁.⊢app D E)             = C₂.⊢app (core D) (core E)
  core (C₁.⊢let D E)             = C₂.⊢let (core D) (core E)
  core C₁.⊢unit                  = C₂.⊢unit
  core (C₁.⊢pair D E)            = C₂.⊢pair (core D) (core E)
  core (C₁.⊢fst D)               = C₂.⊢fst (core D)
  core (C₁.⊢snd D)               = C₂.⊢snd (core D)
  core (C₁.⊢inl D)               = C₂.⊢inl (core D)
  core (C₁.⊢inr D)               = C₂.⊢inr (core D)
  core (C₁.⊢case D E F)          = C₂.⊢case (core D) (core E) (core F)
  core (C₁.⊢absurd D)            = C₂.⊢absurd (core D)
  core (C₁.⊢roll w D)            = C₂.⊢roll w (core D)
  core (C₁.⊢fold w D E)          = C₂.⊢fold w (core D) (core E)
  core (C₁.⊢unfold w D E)        = C₂.⊢unfold w (core D) (core E)
  core (C₁.⊢out w D)             = C₂.⊢out w (core D)
  core (C₁.⊢iter D E)            = C₂.⊢iter (core D) (core E)
  core (C₁.⊢coerce s D)          = C₂.⊢coerce s (core D)
  core C₁.⊢lit-int               = C₂.⊢lit-int
  core C₁.⊢lit-float             = C₂.⊢lit-float
  core (C₁.⊢prim p D)            = C₂.⊢prim p (core D)
  core (C₁.⊢sigop M)             = C₂.⊢sigop M
  core {Δ = Δ} {Γ = Γ} (C₁.⊢ref d τ r) =
    subst (λ A → C₂._⊩_⊢[_]_∷_!_ Δ Γ _ (ref d (λ i → τ (ρ d i))) A _) (ty d τ) (C₂.⊢ref d _ (resp d τ r))
  core (C₁.⊢sub-use u D)         = C₂.⊢sub-use u (core D)
  core (C₁.⊢sub-eff e D)         = C₂.⊢sub-eff e (core D)

  ------------------------------------------------------------------------
  -- The surface judgment
  ------------------------------------------------------------------------

  -- (the judgment's auxiliary types are the module's own, one per table)
  lc : ∀ {m n} → U₁.Locals m n → U₂.Locals m n
  lc U₁.∅           = U₂.∅
  lc (L U₁.▹ x ∶ A) = lc L U₂.▹ x ∶ A

  private
    lv : ∀ {m n} {L : U₁.Locals m n} {x A i} → U₁._∋_⦂_at_ L x A i → U₂._∋_⦂_at_ (lc L) x A i
    lv U₁.here          = U₂.here
    lv (U₁.there ne v)  = U₂.there ne (lv v)

    ia : ∀ {op p} → U₁.IntArith op p → U₂.IntArith op p
    ia U₁.ia-add = U₂.ia-add
    ia U₁.ia-sub = U₂.ia-sub
    ia U₁.ia-mul = U₂.ia-mul
    ia U₁.ia-div = U₂.ia-div
    ia U₁.ia-mod = U₂.ia-mod

    fa : ∀ {op p} → U₁.FloatArith op p → U₂.FloatArith op p
    fa U₁.fa-add = U₂.fa-add
    fa U₁.fa-sub = U₂.fa-sub
    fa U₁.fa-mul = U₂.fa-mul
    fa U₁.fa-div = U₂.fa-div

    cm : ∀ {op p} → U₁.Compare op p → U₂.Compare op p
    cm U₁.cmp-lt = U₂.cmp-lt
    cm U₁.cmp-le = U₂.cmp-le
    cm U₁.cmp-gt = U₂.cmp-gt
    cm U₁.cmp-ge = U₂.cmp-ge
    cm U₁.cmp-eq = U₂.cmp-eq
    cm U₁.cmp-ne = U₂.cmp-ne

    sh : ∀ {f} → Relation.Nullary.¬ U₁.SpecialHead f → Relation.Nullary.¬ U₂.SpecialHead f
    sh n (U₂.sh-gen g)  = n (U₁.sh-gen g)
    sh n U₂.sh-pair     = n U₁.sh-pair
    sh n U₂.sh-compose  = n U₁.sh-compose
    sh n U₂.sh-case     = n U₁.sh-case

  module _ {m : ℕ} {Δ : KCtx m} where
    syn : ∀ {n} {L : U₁.Locals m n} {e A t} → U₁._⊢_⇒_↝_ Δ L e A t → U₂._⊢_⇒_↝_ Δ (lc L) e A (rn t)
    chk : ∀ {n} {L : U₁.Locals m n} {e A t} → U₁._⊢_⇐_↝_ Δ L e A t → U₂._⊢_⇐_↝_ Δ (lc L) e A (rn t)
    dom : ∀ {n} {L : U₁.Locals m n} {e A π B t} → U₁._⊢_⇐_⇒[_]↦_↝_ Δ L e A π B t → U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) e A π B (rn t)

    syn (U₁.s-int i)                 = U₂.s-int i
    syn (U₁.s-float i f l)           = U₂.s-float i f l
    syn U₁.s-unit                    = U₂.s-unit
    syn U₁.s-unit-g                  = U₂.s-unit-g
    syn (U₁.s-var v)                 = U₂.s-var (lv v)
    syn (U₁.s-sigop g M)             = U₂.s-sigop g M
    syn {L = L} (U₁.s-def {c} d e τ z) =
      subst (λ A → U₂._⊢_⇒_↝_ Δ (lc L) (Once.Spec.Surface.Syntax.RResolved c) A (ref d (λ i → τ (ρ d i)))) (ty d τ)
            (U₂.s-def d e _ (ground d z))
    syn (U₁.s-annot D)               = U₂.s-annot (chk D)
    syn (U₁.s-pair D E)              = U₂.s-pair (syn D) (syn E)
    syn (U₁.s-neg D)                 = U₂.s-neg (syn D)
    syn (U₁.s-neg-float i f l)       = U₂.s-neg-float i f l
    syn (U₁.s-let q D E)             = U₂.s-let q (syn D) (syn E)
    syn (U₁.s-case ql qr D E F j)    = U₂.s-case ql qr (syn D) (syn E) (syn F) j
    syn (U₁.s-arith a D E)           = U₂.s-arith (ia a) (syn D) (syn E)
    syn (U₁.s-arith-float a D E)     = U₂.s-arith-float (fa a) (syn D) (syn E)
    syn (U₁.s-arith-float-il a D E)  = U₂.s-arith-float-il (fa a) (syn D) (syn E)
    syn (U₁.s-arith-float-ir a D E)  = U₂.s-arith-float-ir (fa a) (syn D) (syn E)
    syn (U₁.s-compare c D E)         = U₂.s-compare (cm c) (syn D) (syn E)
    syn (U₁.s-id-app D)              = U₂.s-id-app (syn D)
    syn (U₁.s-fst-app D)             = U₂.s-fst-app (syn D)
    syn (U₁.s-snd-app D)             = U₂.s-snd-app (syn D)
    syn (U₁.s-terminal-app D)        = U₂.s-terminal-app (syn D)
    syn (U₁.s-apply-app D)           = U₂.s-apply-app (syn D)
    syn (U₁.s-apply-eff-app g D)     = U₂.s-apply-eff-app g (syn D)
    syn (U₁.s-Out-app w D)           = U₂.s-Out-app w (syn D)
    syn (U₁.s-Out-act-app w D)       = U₂.s-Out-act-app w (syn D)
    syn (U₁.s-app h D E)             = U₂.s-app (sh h) (syn D) (chk E)
    syn {L = L} (U₁.s-effApp {f} {x} {A} {B} {π} {tf} {tx} h g D E) =
      subst (U₂._⊢_⇒_↝_ Δ (lc L) (Once.Spec.Surface.Syntax.RApp f x) _) (sym (rn-effApp π tf tx)) (U₂.s-effApp (sh h) g (syn D) (chk E))
    syn (U₁.s-app-spine h D E)       = U₂.s-app-spine (sh h) (syn D) (dom E)

    chk U₁.c-id                      = U₂.c-id
    chk U₁.c-fst                     = U₂.c-fst
    chk U₁.c-snd                     = U₂.c-snd
    chk U₁.c-terminal                = U₂.c-terminal
    chk U₁.c-initial                 = U₂.c-initial
    chk U₁.c-inl                     = U₂.c-inl
    chk U₁.c-inr                     = U₂.c-inr
    chk {L = L} (U₁.c-compose-g {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-compose A π tf tg)) (U₂.c-compose-g (dom D) (chk E))
    chk {L = L} (U₁.c-compose-f {f} {g} {A} {B} {C} {C′} {π} {π′} {tf} {tg} D s E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-compose A π (coerce _ _ tf) tg)) (U₂.c-compose-f (syn D) s (chk E))
    chk {L = L} (U₁.c-case {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-case A B π tf tg)) (U₂.c-case (chk D) (chk E))
    chk {L = L} (U₁.c-pair {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-pair A π tf tg)) (U₂.c-pair (chk D) (chk E))
    chk (U₁.c-curry D)               = U₂.c-curry (chk D)
    chk (U₁.c-cata w D)              = U₂.c-cata w (chk D)
    chk {L = L} (U₁.c-ana {c} {F} {A} {π₀} {f} {t} le w D) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-ana F A π₀ t)) (U₂.c-ana le w (chk D))
    chk (U₁.c-loop D)                = U₂.c-loop (chk D)
    chk (U₁.c-sub D s)               = U₂.c-sub (syn D) s
    chk (U₁.c-lam D)                 = U₂.c-lam (chk D)
    chk (U₁.c-pair-lit D E)          = U₂.c-pair-lit (chk D) (chk E)
    chk (U₁.c-In-app w D)            = U₂.c-In-app w (chk D)
    chk (U₁.c-apply-app D)           = U₂.c-apply-app (syn D)
    chk (U₁.c-inl-app D)             = U₂.c-inl-app (chk D)
    chk (U₁.c-inr-app D)             = U₂.c-inr-app (chk D)
    chk (U₁.c-initial-app D)         = U₂.c-initial-app (chk D)
    chk {L = L} (U₁.c-poly {c} d e p τ r) =
      subst (λ A → U₂._⊢_⇐_↝_ Δ (lc L) (Once.Spec.Surface.Syntax.RResolved c) A (ref d (λ i → τ (ρ d i)))) (ty d τ)
            (U₂.c-poly d e (open′ d p) _ (resp d τ r))

    dom (U₁.d-infer D s g)           = U₂.d-infer (syn D) s g
    dom (U₁.d-poly d e p eq occ τ r ea eb g) =
      let (sd₂ , sc₂ , eq₂ , occ₂ , esd , esc) = SchRen.arrow (R d) eq occ
      in U₂.d-poly d e (open′ d p) eq₂ occ₂ _ (resp d τ r) (trans (esd τ) ea) (trans (esc τ) eb) g
    dom (U₁.d-lam D)                 = U₂.d-lam (syn D)
    dom {L = L} (U₁.d-compose {f} {g} {A} {M} {B} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) _ _ _ _) (sym (rn-compose A π tf tg)) (U₂.d-compose (dom D) (dom E))
    dom U₁.d-id                      = U₂.d-id
    dom U₁.d-fst                     = U₂.d-fst
    dom U₁.d-snd                     = U₂.d-snd
    dom U₁.d-terminal                = U₂.d-terminal
    dom U₁.d-initial                 = U₂.d-initial
    dom {L = L} (U₁.d-case {f} {g} {A} {B} {Cf} {Cg} {C} {π} {tf} {tg} D E j) =
      subst (U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) _ _ _ _) (sym (rn-case A B π (coerce _ _ tf) (coerce _ _ tg))) (U₂.d-case (dom D) (dom E) j)
    dom {L = L} (U₁.d-pair {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) _ _ _ _) (sym (rn-pair A π tf tg)) (U₂.d-pair (dom D) (dom E))
    dom (U₁.d-cata w D)              = U₂.d-cata w (syn D)
