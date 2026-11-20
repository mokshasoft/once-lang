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
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Once.Spec.Grade using (mk-kind; Many; pure; act; eff; pureᶠ; actᶠ)
open import Once.Spec.Type using (Ty; Fun; KCtx; TySub; Respects; _⟨_⟩; _⟨_⟩F; Occurs; OccursF; _⇒[_]_; var; _*_; _+_; μ; ν; K; _⊕_; _⊗_;
  o-var; o-*ˡ; o-*ʳ; o-+ˡ; o-+ʳ; o-⇒ˡ; o-⇒ʳ; o-μ; o-ν; o-K; o-⊕ˡ; o-⊕ʳ; o-⊗ˡ; o-⊗ʳ)
open import Data.Nat using (s≤s; z≤n)
import Data.Fin
import Once.Spec.Surface.Generators as Gn
open import Once.Adequacy.SpecFront.TyRen Σ S₁ nm using (⟨⟩-id)
open import Once.Spec.Core.Syntax
open import Once.Spec.Core.Derived
open import Once.Adequacy.SpecFront.SchemaRen using (SchRen)
import Once.Spec.Surface.Syntax
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

------------------------------------------------------------------------
-- Occurrences under a renaming of the variables
------------------------------------------------------------------------

module _ {a b} (r : Fin a → Fin b) where
  private
    vr : TySub a b
    vr j = var (r j)
  mutual
    occ-fwd : ∀ {j} (A : Ty a) → Occurs j A → Occurs (r j) (A ⟨ vr ⟩)
    occ-fwd (var _)      o-var    = o-var
    occ-fwd (A * B)      (o-*ˡ o) = o-*ˡ (occ-fwd A o)
    occ-fwd (A * B)      (o-*ʳ o) = o-*ʳ (occ-fwd B o)
    occ-fwd (A + B)      (o-+ˡ o) = o-+ˡ (occ-fwd A o)
    occ-fwd (A + B)      (o-+ʳ o) = o-+ʳ (occ-fwd B o)
    occ-fwd (A ⇒[ k ] B) (o-⇒ˡ o) = o-⇒ˡ (occ-fwd A o)
    occ-fwd (A ⇒[ k ] B) (o-⇒ʳ o) = o-⇒ʳ (occ-fwd B o)
    occ-fwd (μ F)        (o-μ o)  = o-μ (occF-fwd F o)
    occ-fwd (ν F f)      (o-ν o)  = o-ν (occF-fwd F o)
    occF-fwd : ∀ {j} (F : Fun a) → OccursF j F → OccursF (r j) (F ⟨ vr ⟩F)
    occF-fwd (K A)   (o-K o)  = o-K (occ-fwd A o)
    occF-fwd (F ⊕ G) (o-⊕ˡ o) = o-⊕ˡ (occF-fwd F o)
    occF-fwd (F ⊕ G) (o-⊕ʳ o) = o-⊕ʳ (occF-fwd G o)
    occF-fwd (F ⊗ G) (o-⊗ˡ o) = o-⊗ˡ (occF-fwd F o)
    occF-fwd (F ⊗ G) (o-⊗ʳ o) = o-⊗ʳ (occF-fwd G o)
  mutual
    occ-back : ∀ {i} (A : Ty a) → Occurs i (A ⟨ vr ⟩) → Σ[ j ∈ Fin a ] (r j ≡ i) × Occurs j A
    occ-back (var j)      o-var    = j , refl , o-var
    occ-back (A * B)      (o-*ˡ o) = let (j , e , o′) = occ-back A o in j , e , o-*ˡ o′
    occ-back (A * B)      (o-*ʳ o) = let (j , e , o′) = occ-back B o in j , e , o-*ʳ o′
    occ-back (A + B)      (o-+ˡ o) = let (j , e , o′) = occ-back A o in j , e , o-+ˡ o′
    occ-back (A + B)      (o-+ʳ o) = let (j , e , o′) = occ-back B o in j , e , o-+ʳ o′
    occ-back (A ⇒[ k ] B) (o-⇒ˡ o) = let (j , e , o′) = occ-back A o in j , e , o-⇒ˡ o′
    occ-back (A ⇒[ k ] B) (o-⇒ʳ o) = let (j , e , o′) = occ-back B o in j , e , o-⇒ʳ o′
    occ-back (μ F)        (o-μ o)  = let (j , e , o′) = occF-back F o in j , e , o-μ o′
    occ-back (ν F f)      (o-ν o)  = let (j , e , o′) = occF-back F o in j , e , o-ν o′
    occF-back : ∀ {i} (F : Fun a) → OccursF i (F ⟨ vr ⟩F) → Σ[ j ∈ Fin a ] (r j ≡ i) × OccursF j F
    occF-back (K A)   (o-K o)  = let (j , e , o′) = occ-back A o in j , e , o-K o′
    occF-back (F ⊕ G) (o-⊕ˡ o) = let (j , e , o′) = occF-back F o in j , e , o-⊕ˡ o′
    occF-back (F ⊕ G) (o-⊕ʳ o) = let (j , e , o′) = occF-back G o in j , e , o-⊕ʳ o′
    occF-back (F ⊗ G) (o-⊗ˡ o) = let (j , e , o′) = occF-back F o in j , e , o-⊗ˡ o′
    occF-back (F ⊗ G) (o-⊗ʳ o) = let (j , e , o′) = occF-back G o in j , e , o-⊗ʳ o′

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


    -- an entry with variables in one table has them in the other
    pos : ∀ {k} → Fin k → 0 < k
    pos zero    = s≤s z≤n
    pos (suc _) = s≤s z≤n
    lt-back : ∀ d → 0 < arity (S₂ !! d) → 0 < arity (S₁ !! d)
    lt-back d p = pos (ρ d (Data.Fin.fromℕ< p))

    vρ : ∀ d → TySub (arity (S₂ !! d)) (arity (S₁ !! d))
    vρ d j = var (ρ d j)

    -- `S₂`'s arrow read back in `S₁`: its variables are `ρ`'s images
    arrow⁻ : ∀ d {sd₂ sc₂ π′} → type (S₂ !! d) ≡ sd₂ ⇒[ mk-kind Many π′ ] sc₂ → (∀ j → Occurs j sc₂ → Occurs j sd₂)
           → Σ[ sd ∈ Ty (arity (S₁ !! d)) ] Σ[ sc ∈ Ty (arity (S₁ !! d)) ]
               (type (S₁ !! d) ≡ sd ⇒[ mk-kind Many π′ ] sc) × (∀ i → Occurs i sc → Occurs i sd)
    arrow⁻ d {sd₂} {sc₂} e occ =
      sd₂ ⟨ vρ d ⟩ , sc₂ ⟨ vρ d ⟩ ,
      trans (sym (⟨⟩-id (type (S₁ !! d)))) (trans (sym (ty d var)) (cong (_⟨ vρ d ⟩) e)) ,
      λ i o → let (j , ej , oj) = occ-back (ρ d) sc₂ o in subst (λ k → Occurs k (sd₂ ⟨ vρ d ⟩)) ej (occ-fwd (ρ d) sd₂ (occ j oj))

    -- the forms' classes, in either table (they name a table only through
    -- whether an entry has variables, and its arrow)
    pn12 : ∀ {c} → U₁.PolyName c → U₂.PolyName c
    pn12 (U₁.poly d e lt) = U₂.poly d e (open′ d lt)
    pn21 : ∀ {c} → U₂.PolyName c → U₁.PolyName c
    pn21 (U₂.poly d e lt) = U₁.poly d e (lt-back d lt)
    pfd12 : ∀ {c} → U₁.PolyFromDomain c → U₂.PolyFromDomain c
    pfd12 (U₁.poly-dom d e lt eq occ) =
      let (sd₂ , sc₂ , eq₂ , occ₂ , _ , _) = SchRen.arrow (R d) eq occ in U₂.poly-dom d e (open′ d lt) eq₂ occ₂
    pfd21 : ∀ {c} → U₂.PolyFromDomain c → U₁.PolyFromDomain c
    pfd21 (U₂.poly-dom d e lt eq occ) =
      let (sd , sc , eq₁ , occ₁) = arrow⁻ d eq occ in U₁.poly-dom d e (lt-back d lt) eq₁ occ₁
    pc21 : ∀ {f} → U₂.PartialCombinator f → U₁.PartialCombinator f
    pc21 (U₂.pc-bare ic) = U₁.pc-bare ic
    pc21 (U₂.pc-one ic)  = U₁.pc-one ic
    ch12 : ∀ {f} → U₁.CheckHead f → U₂.CheckHead f
    ch12 U₁.ch-lam         = U₂.ch-lam
    ch12 (U₁.ch-poly pn)   = U₂.ch-poly (pn12 pn)
    ch12 (U₁.ch-map im)    = U₂.ch-map im
    ch12 (U₁.ch-comb₁ ic)  = U₂.ch-comb₁ ic
    ch12 (U₁.ch-comb₂ ic)  = U₂.ch-comb₂ ic
    ch21 : ∀ {f} → U₂.CheckHead f → U₁.CheckHead f
    ch21 U₂.ch-lam         = U₁.ch-lam
    ch21 (U₂.ch-poly pn)   = U₁.ch-poly (pn21 pn)
    ch21 (U₂.ch-map im)    = U₁.ch-map im
    ch21 (U₂.ch-comb₁ ic)  = U₁.ch-comb₁ ic
    ch21 (U₂.ch-comb₂ ic)  = U₁.ch-comb₂ ic
    oc21 : ∀ {e} → U₂.OwnCheck e → U₁.OwnCheck e
    oc21 U₂.oc-pair      = U₁.oc-pair
    oc21 (U₂.oc-map fc)  = U₁.oc-map fc
    sf12 : ∀ {e} → U₁.SynthForm e → U₂.SynthForm e
    sf12 U₁.sf-int          = U₂.sf-int
    sf12 U₁.sf-float        = U₂.sf-float
    sf12 U₁.sf-unit         = U₂.sf-unit
    sf12 U₁.sf-var          = U₂.sf-var
    sf12 (U₁.sf-name n)     = U₂.sf-name (λ pn → n (pn21 pn))
    sf12 (U₁.sf-const k)    = U₂.sf-const k
    sf12 U₁.sf-annot        = U₂.sf-annot
    sf12 (U₁.sf-pair a b)   = U₂.sf-pair (sf12 a) (sf12 b)
    sf12 U₁.sf-neg          = U₂.sf-neg
    sf12 U₁.sf-binop        = U₂.sf-binop
    sf12 U₁.sf-let          = U₂.sf-let
    sf12 U₁.sf-destruct     = U₂.sf-destruct
    sf12 (U₁.sf-app pc oc)  = U₂.sf-app (λ p → pc (pc21 p)) (λ o → oc (oc21 o))
    sf21 : ∀ {e} → U₂.SynthForm e → U₁.SynthForm e
    sf21 U₂.sf-int          = U₁.sf-int
    sf21 U₂.sf-float        = U₁.sf-float
    sf21 U₂.sf-unit         = U₁.sf-unit
    sf21 U₂.sf-var          = U₁.sf-var
    sf21 (U₂.sf-name n)     = U₁.sf-name (λ pn → n (pn12 pn))
    sf21 (U₂.sf-const k)    = U₁.sf-const k
    sf21 U₂.sf-annot        = U₁.sf-annot
    sf21 (U₂.sf-pair a b)   = U₁.sf-pair (sf21 a) (sf21 b)
    sf21 U₂.sf-neg          = U₁.sf-neg
    sf21 U₂.sf-binop        = U₁.sf-binop
    sf21 U₂.sf-let          = U₁.sf-let
    sf21 U₂.sf-destruct     = U₁.sf-destruct
    sf21 (U₂.sf-app pc oc)  = U₁.sf-app (λ p → pc (pc12 p)) (λ o → oc (oc12 o))
      where
        pc12 : ∀ {f} → U₁.PartialCombinator f → U₂.PartialCombinator f
        pc12 (U₁.pc-bare ic) = U₂.pc-bare ic
        pc12 (U₁.pc-one ic)  = U₂.pc-one ic
        oc12 : ∀ {e} → U₁.OwnCheck e → U₂.OwnCheck e
        oc12 U₁.oc-pair      = U₂.oc-pair
        oc12 (U₁.oc-map fc)  = U₂.oc-map fc
    df12 : ∀ {e} → U₁.DomainForm e → U₂.DomainForm e
    df12 (U₁.df-synth sf)     = U₂.df-synth (sf12 sf)
    df12 (U₁.df-lam sb)       = U₂.df-lam (sf12 sb)
    df12 (U₁.df-poly p)       = U₂.df-poly (pfd12 p)
    df12 (U₁.df-map fd)       = U₂.df-map fd
    df12 (U₁.df-compose f g)  = U₂.df-compose (df12 f) (df12 g)
    df12 (U₁.df-case f g)     = U₂.df-case (df12 f) (df12 g)
    df12 (U₁.df-pair f g)     = U₂.df-pair (df12 f) (df12 g)
    df12 (U₁.df-cata sa)      = U₂.df-cata (sf12 sa)
    df21 : ∀ {e} → U₂.DomainForm e → U₁.DomainForm e
    df21 (U₂.df-synth sf)     = U₁.df-synth (sf21 sf)
    df21 (U₂.df-lam sb)       = U₁.df-lam (sf21 sb)
    df21 (U₂.df-poly p)       = U₁.df-poly (pfd21 p)
    df21 (U₂.df-map fd)       = U₁.df-map fd
    df21 (U₂.df-compose f g)  = U₁.df-compose (df21 f) (df21 g)
    df21 (U₂.df-case f g)     = U₁.df-case (df21 f) (df21 g)
    df21 (U₂.df-pair f g)     = U₁.df-pair (df21 f) (df21 g)
    df21 (U₂.df-cata sa)      = U₁.df-cata (sf21 sa)

    -- the table's rows name closed terms, the same in either table
    const-rn : ∀ {m} {Δ : KCtx m} {n g k T t} → Gn.Constant {S = S₁} Δ {n = n} g k T t → Gn.Constant {S = S₂} Δ {n = n} g k T (rn t)
    const-rn Gn.k-unit    = Gn.k-unit
    const-rn Gn.k-toFloat = Gn.k-toFloat
    morph-rn : ∀ {m} {Δ : KCtx m} {n g k A π B t} → Gn.Morphism {S = S₁} Δ {n = n} g k A π B t → Gn.Morphism {S = S₂} Δ {n = n} g k A π B (rn t)
    morph-rn Gn.m-id       = Gn.m-id
    morph-rn Gn.m-fst      = Gn.m-fst
    morph-rn Gn.m-snd      = Gn.m-snd
    morph-rn Gn.m-terminal = Gn.m-terminal
    morph-rn Gn.m-inl      = Gn.m-inl
    morph-rn Gn.m-inr      = Gn.m-inr
    morph-rn Gn.m-initial  = Gn.m-initial
    morph-rn (Gn.m-apply {ρ = pure}) = Gn.m-apply
    morph-rn (Gn.m-apply {ρ = act})  = Gn.m-apply
    morph-rn (Gn.m-apply {ρ = eff})  = Gn.m-apply
    morph-rn (Gn.m-In w)   = Gn.m-In w
    morph-rn (Gn.m-Out {f = pureᶠ} w) = Gn.m-Out w
    morph-rn (Gn.m-Out {f = actᶠ} w)  = Gn.m-Out w
    morph-back : ∀ {m} {Δ : KCtx m} {n g k A π B t} → Gn.Morphism {S = S₂} Δ {n = n} g k A π B t
               → Σ[ t′ ∈ Tm S₁ m n ] Gn.Morphism {S = S₁} Δ {n = n} g k A π B t′
    morph-back Gn.m-id       = _ , Gn.m-id
    morph-back Gn.m-fst      = _ , Gn.m-fst
    morph-back Gn.m-snd      = _ , Gn.m-snd
    morph-back Gn.m-terminal = _ , Gn.m-terminal
    morph-back Gn.m-inl      = _ , Gn.m-inl
    morph-back Gn.m-inr      = _ , Gn.m-inr
    morph-back Gn.m-initial  = _ , Gn.m-initial
    morph-back Gn.m-apply    = _ , Gn.m-apply
    morph-back (Gn.m-In w)   = _ , Gn.m-In w
    morph-back (Gn.m-Out w)  = _ , Gn.m-Out w

  rn-appᵀ : ∀ {m n} π (f x : Tm S₁ m n) → rn (appᵀ π f x) ≡ appᵀ π (rn f) (rn x)
  rn-appᵀ pure f x = refl
  rn-appᵀ act  f x = rn-effApp act f x
  rn-appᵀ eff  f x = rn-effApp eff f x

  module _ {m : ℕ} {Δ : KCtx m} where
    syn : ∀ {n} {L : U₁.Locals m n} {e A t} → U₁._⊢_⇒_↝_ Δ L e A t → U₂._⊢_⇒_↝_ Δ (lc L) e A (rn t)
    chk : ∀ {n} {L : U₁.Locals m n} {e A t} → U₁._⊢_⇐_↝_ Δ L e A t → U₂._⊢_⇐_↝_ Δ (lc L) e A (rn t)
    dom : ∀ {n} {L : U₁.Locals m n} {e A π B t} → U₁._⊢_⇐_⇒[_]↦_↝_ Δ L e A π B t → U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) e A π B (rn t)

    syn (U₁.s-int i)                 = U₂.s-int i
    syn (U₁.s-float sg i f l)        = U₂.s-float sg i f l
    syn U₁.s-unit                    = U₂.s-unit
    syn (U₁.s-const c)               = U₂.s-const (const-rn c)
    syn (U₁.s-var v)                 = U₂.s-var (lv v)
    syn (U₁.s-sigop M)               = U₂.s-sigop M
    syn {L = L} (U₁.s-def {c} d e τ z) =
      subst (λ A → U₂._⊢_⇒_↝_ Δ (lc L) (Once.Spec.Surface.Syntax.RResolved c) A (ref d (λ i → τ (ρ d i)))) (ty d τ)
            (U₂.s-def d e _ (ground d z))
    syn (U₁.s-annot D)               = U₂.s-annot (chk D)
    syn (U₁.s-pair D E)              = U₂.s-pair (syn D) (syn E)
    syn (U₁.s-neg h D)               = U₂.s-neg h (syn D)
    syn (U₁.s-let q D E)             = U₂.s-let q (syn D) (syn E)
    syn (U₁.s-case ql qr D E F j)    = U₂.s-case ql qr (syn D) (syn E) (syn F) j
    syn (U₁.s-binop h D E)           = U₂.s-binop h (syn D) (syn E)
    syn {L = L} (U₁.s-app {f} {x} {A} {B} {q} {π} {tf} {tx} pc ch D E) =
      subst (U₂._⊢_⇒_↝_ Δ (lc L) (Once.Spec.Surface.Syntax.RApp f x) _) (sym (rn-appᵀ π tf tx))
            (U₂.s-app (λ p → pc (pc21 p)) (λ c → ch (ch21 c)) (syn D) (chk E))
    syn (U₁.s-app-spine ch D E)      = U₂.s-app-spine (ch12 ch) (syn D) (dom E)

    chk (U₁.c-map mo)                = U₂.c-map (morph-rn mo)
    chk (U₁.c-map-app fc mo D)       = U₂.c-map-app fc (morph-rn mo) (chk D)
    chk {L = L} (U₁.c-compose-g {f} {g} {A} {B} {C} {π} {tf} {tg} dfg D E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-compose A π tf tg)) (U₂.c-compose-g (df12 dfg) (dom D) (chk E))
    chk {L = L} (U₁.c-compose-f {f} {g} {A} {B} {C} {C′} {π} {π′} {tf} {tg} ndf D s E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-compose A π (coerce _ _ tf) tg)) (U₂.c-compose-f (λ d → ndf (df21 d)) (syn D) s (chk E))
    chk {L = L} (U₁.c-case {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-case A B π tf tg)) (U₂.c-case (chk D) (chk E))
    chk {L = L} (U₁.c-pair {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-pair A π tf tg)) (U₂.c-pair (chk D) (chk E))
    chk (U₁.c-curry D)               = U₂.c-curry (chk D)
    chk (U₁.c-cata w D)              = U₂.c-cata w (chk D)
    chk {L = L} (U₁.c-ana {c} {A} {π₀} {t = t} (Gn.final-ν {F = F} le w) D) =
      subst (U₂._⊢_⇐_↝_ Δ (lc L) _ _) (sym (rn-ana F A π₀ t)) (U₂.c-ana (Gn.final-ν le w) (chk D))
    chk (U₁.c-ana Gn.final-T∞ D)     = U₂.c-ana Gn.final-T∞ (chk D)
    chk (U₁.c-sub noc D s)           = U₂.c-sub (λ o → noc (oc21 o)) (syn D) s
    chk (U₁.c-lam D)                 = U₂.c-lam (chk D)
    chk (U₁.c-pair-lit D E)          = U₂.c-pair-lit (chk D) (chk E)
    chk {L = L} (U₁.c-poly {c} d e p τ r) =
      subst (λ A → U₂._⊢_⇐_↝_ Δ (lc L) (Once.Spec.Surface.Syntax.RResolved c) A (ref d (λ i → τ (ρ d i)))) (ty d τ)
            (U₂.c-poly d e (open′ d p) _ (resp d τ r))

    dom (U₁.d-infer D s g)           = U₂.d-infer (syn D) s g
    dom (U₁.d-poly d e p eq occ τ r ea eb g) =
      let (sd₂ , sc₂ , eq₂ , occ₂ , esd , esc) = SchRen.arrow (R d) eq occ
      in U₂.d-poly d e (open′ d p) eq₂ occ₂ _ (resp d τ r) (trans (esd τ) ea) (trans (esc τ) eb) g
    dom (U₁.d-lam D)                 = U₂.d-lam (syn D)
    dom (U₁.d-map fd mo least)       = U₂.d-map fd (morph-rn mo) (λ mo′ → least (proj₂ (morph-back mo′)))
    dom {L = L} (U₁.d-compose {f} {g} {A} {M} {B} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) _ _ _ _) (sym (rn-compose A π tf tg)) (U₂.d-compose (dom D) (dom E))
    dom {L = L} (U₁.d-case {f} {g} {A} {B} {Cf} {Cg} {C} {π} {tf} {tg} D E j) =
      subst (U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) _ _ _ _) (sym (rn-case A B π (coerce _ _ tf) (coerce _ _ tg))) (U₂.d-case (dom D) (dom E) j)
    dom {L = L} (U₁.d-pair {f} {g} {A} {B} {C} {π} {tf} {tg} D E) =
      subst (U₂._⊢_⇐_⇒[_]↦_↝_ Δ (lc L) _ _ _ _) (sym (rn-pair A π tf tg)) (U₂.d-pair (dom D) (dom E))
    dom (U₁.d-cata w D p o)          = U₂.d-cata w (syn D) p o
