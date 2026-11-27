-- SPIKE: typing over the generic syntax, and ONE typing-preservation lemma
-- for every typed kit (SPIKE-GENERIC-SYNTAX S3, part 2).
--
-- The fragment's rules are written by hand (they are content). The
-- structural lemma is written ONCE: a traversal by any typed syntactic kit
-- preserves typing. Renaming (weakening) and substitution typing are its
-- two instances, the second built from the first. Each rule's case uses
-- only the generic commutation lemmas of `tmp.GenSynKit` (`trav-wk`,
-- `trav-single`, `square`), never a per-former equation.
--
-- Conversion is a parameter, stable under substitution; its stability
-- under any kit follows by simulation (`trav≡sub`).

{-# OPTIONS --safe #-}
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong; subst )
open import Agda.Builtin.List using ( []; _∷_ )
open import DirectedHoTT.Spec.Syntax using ( Cx; ε; _∙; Var; vz; vs )
open import tmp.GenSyn
open import tmp.GenSynFrag

module tmp.GenSynTy
  (_≅_  : ∀ {Γ} → RTy Γ → RTy Γ → Set)
  (≅-sub : ∀ {Γ Δ} (σ : Var Γ → Trav.T K Δ) {A B : RTy Γ} → A ≅ B → Trav.sub K σ A ≅ Trav.sub K σ B)
  where

open Trav K
open import tmp.GenSynKit K

pattern nzero  = con `nzero []
pattern nsuc n = con `nsuc (n ∷ʳ [])
pattern Nat    = con `Nat []

------------------------------------------------------------------------
-- Contexts and the judgments (the fragment's rules, by hand)
------------------------------------------------------------------------

infixl 5 _▹_
data Ctx : Cx → Set where
  ∅   : Ctx ε
  _▹_ : ∀ {Γ} → Ctx Γ → RTy Γ → Ctx (Γ ∙)

infix 4 _∋_∷_ _⊢_∷_ _⊢ty_
data _∋_∷_ : ∀ {Γ} → Ctx Γ → Var Γ → RTy Γ → Set where
  here  : ∀ {Γ} {G : Ctx Γ} {A}       → (G ▹ A) ∋ vz ∷ ren vs A
  there : ∀ {Γ} {G : Ctx Γ} {x A B}   → G ∋ x ∷ A → (G ▹ B) ∋ vs x ∷ ren vs A

-- the step substitution of `natrec`: (n, ih) ⊢ M[suc n / n]
nrs : ∀ {Γ} → Var (Γ ∙) → T ((Γ ∙) ∙)
nrs vz     = nsuc (var (vs vz))
nrs (vs x) = var (vs (vs x))

data _⊢_∷_ : ∀ {Γ} → Ctx Γ → RTm Γ → RTy Γ → Set
data _⊢ty_ : ∀ {Γ} → Ctx Γ → RTy Γ → Set

data _⊢ty_ where
  ty-U   : ∀ {Γ} {G : Ctx Γ} → G ⊢ty U
  ty-Nat : ∀ {Γ} {G : Ctx Γ} → G ⊢ty Nat
  ty-El  : ∀ {Γ} {G : Ctx Γ} {c} → G ⊢ c ∷ U → G ⊢ty El c
  ty-Π   : ∀ {Γ} {G : Ctx Γ} {A B} → G ⊢ty A → (G ▹ A) ⊢ty B → G ⊢ty Π A B

data _⊢_∷_ where
  ⊢var    : ∀ {Γ} {G : Ctx Γ} {x A} → G ∋ x ∷ A → G ⊢ var x ∷ A
  ⊢lam    : ∀ {Γ} {G : Ctx Γ} {A B t} → G ⊢ty A → (G ▹ A) ⊢ t ∷ B → G ⊢ lam t ∷ Π A B
  ⊢app    : ∀ {Γ} {G : Ctx Γ} {A B t u} → G ⊢ t ∷ Π A B → G ⊢ u ∷ A → G ⊢ app t u ∷ sub (single u) B
  ⊢nzero  : ∀ {Γ} {G : Ctx Γ} → G ⊢ nzero ∷ Nat
  ⊢nsuc   : ∀ {Γ} {G : Ctx Γ} {n} → G ⊢ n ∷ Nat → G ⊢ nsuc n ∷ Nat
  ⊢natrec : ∀ {Γ} {G : Ctx Γ} {M z s n}
          → (G ▹ Nat) ⊢ty M
          → G ⊢ z ∷ sub (single nzero) M
          → ((G ▹ Nat) ▹ M) ⊢ s ∷ sub nrs M
          → G ⊢ n ∷ Nat
          → G ⊢ natrec z s n ∷ sub (single n) M
  ⊢conv   : ∀ {Γ} {G : Ctx Γ} {t A B} → G ⊢ t ∷ A → A ≅ B → G ⊢ t ∷ B

cast : ∀ {Γ} {G : Ctx Γ} {t A B} → A ≡ B → G ⊢ t ∷ A → G ⊢ t ∷ B
cast refl d = d

------------------------------------------------------------------------
-- Typed kits, and THE preservation lemma
------------------------------------------------------------------------

record TKit (Kt : Kit) : Set₁ where
  field
    syn    : Syntactic Kt
    _⊢ᵛ_∷_ : ∀ {Δ} → Ctx Δ → Kit.V Kt Δ → RTy Δ → Set
    toTm⊢  : ∀ {Δ} {D : Ctx Δ} {v A}   → D ⊢ᵛ v ∷ A → D ⊢ Kit.toTm Kt v ∷ A
    v0⊢    : ∀ {Δ} {D : Ctx Δ} {A}     → (D ▹ A) ⊢ᵛ Kit.v0 Kt ∷ ren vs A
    wkV⊢   : ∀ {Δ} {D : Ctx Δ} {v A B} → D ⊢ᵛ v ∷ A → (D ▹ B) ⊢ᵛ Kit.wkV Kt v ∷ ren vs A

module Preserve {Kt : Kit} (TK : TKit Kt) where
  open TKit TK
  open Syntactic syn
  open Kit Kt

  -- an environment is typed when every variable's value has the traversed type
  _⊢ᴱ_∶_ : ∀ {Γ Δ} → Ctx Δ → Env Kt Γ Δ → Ctx Γ → Set
  D ⊢ᴱ ρ ∶ G = ∀ {x A} → G ∋ x ∷ A → D ⊢ᵛ ρ x ∷ trav Kt ρ A

  private
    castᵛ : ∀ {Δ} {D : Ctx Δ} {v A B} → A ≡ B → D ⊢ᵛ v ∷ A → D ⊢ᵛ v ∷ B
    castᵛ refl d = d

  ext⊢ : ∀ {Γ Δ} {G : Ctx Γ} {D : Ctx Δ} {ρ : Env Kt Γ Δ} {A}
       → D ⊢ᴱ ρ ∶ G → (D ▹ trav Kt ρ A) ⊢ᴱ ext Kt ρ ∶ (G ▹ A)
  ext⊢ {ρ = ρ} {A = A} E here               = castᵛ (sym (trav-wk Kt syn ρ A)) v0⊢
  ext⊢ {ρ = ρ}     E (there {A = A′} p) = castᵛ (sym (trav-wk Kt syn ρ A′)) (wkV⊢ (E p))

  -- conversion is stable under the kit, because the kit IS a substitution
  ≅-trav : ∀ {Γ Δ} (ρ : Env Kt Γ Δ) {A B : RTy Γ} → A ≅ B → trav Kt ρ A ≅ trav Kt ρ B
  ≅-trav ρ {A} {B} c =
    subst (λ X → X ≅ trav Kt ρ B) (sym (trav≡sub Kt syn ρ A))
      (subst (λ Y → sub (λ x → toTm (ρ x)) A ≅ Y) (sym (trav≡sub Kt syn ρ B)) (≅-sub _ c))

  -- natrec's step substitution commutes with the kit (an instance of the square)
  trav-nrs : ∀ {Γ Δ} (ρ : Env Kt Γ Δ) (M : RTy (Γ ∙))
           → trav Kt (ext Kt (ext Kt ρ)) (sub nrs M) ≡ sub nrs (trav Kt (ext Kt ρ) M)
  trav-nrs ρ M = square Kt syn nrs (ext Kt (ext Kt ρ)) (ext Kt ρ) nrs h M
    where
    h : ∀ x → trav Kt (ext Kt (ext Kt ρ)) (nrs x) ≡ sub nrs (toTm (ext Kt ρ x))
    h vz = trans (cong nsuc (trans (toTm-wk v0) (cong (ren vs) toTm-v0)))
                 (sym (cong (sub nrs) toTm-v0))
    h (vs y) =
      trans (toTm-wk (wkV (ρ y)))
      (trans (cong (ren vs) (toTm-wk (ρ y)))
      (trans (ren-ren vs vs (toTm (ρ y)))
      (trans (trav≡sub renK renS (λ z → vs (vs z)) (toTm (ρ y)))
      (sym (trans (cong (sub nrs) (toTm-wk (ρ y))) (sub-ren vs nrs (toTm (ρ y))))))))

  pres   : ∀ {Γ Δ} {G : Ctx Γ} {D : Ctx Δ} {ρ : Env Kt Γ Δ} {t A}
         → D ⊢ᴱ ρ ∶ G → G ⊢ t ∷ A → D ⊢ trav Kt ρ t ∷ trav Kt ρ A
  presTy : ∀ {Γ Δ} {G : Ctx Γ} {D : Ctx Δ} {ρ : Env Kt Γ Δ} {A}
         → D ⊢ᴱ ρ ∶ G → G ⊢ty A → D ⊢ty trav Kt ρ A

  presTy E ty-U       = ty-U
  presTy E ty-Nat     = ty-Nat
  presTy E (ty-El c)  = ty-El (pres E c)
  presTy E (ty-Π a b) = ty-Π (presTy E a) (presTy (ext⊢ E) b)

  pres E (⊢var p)   = toTm⊢ (E p)
  pres E (⊢lam a t) = ⊢lam (presTy E a) (pres (ext⊢ E) t)
  pres {ρ = ρ} E (⊢app {B = B} {u = u} t a) =
    cast (sym (trav-single Kt syn ρ u B)) (⊢app (pres E t) (pres E a))
  pres E ⊢nzero     = ⊢nzero
  pres E (⊢nsuc n)  = ⊢nsuc (pres E n)
  pres {ρ = ρ} E (⊢natrec {M = M} {n = n} m z s k) =
    cast (sym (trav-single Kt syn ρ n M))
      (⊢natrec (presTy (ext⊢ E) m)
               (cast (trav-single Kt syn ρ nzero M) (pres E z))
               (cast (trav-nrs ρ M) (pres (ext⊢ (ext⊢ E)) s))
               (pres E k))
  pres {ρ = ρ} E (⊢conv t c) = ⊢conv (pres E t) (≅-trav ρ c)

------------------------------------------------------------------------
-- The two instances: weakening, then substitution built on it
------------------------------------------------------------------------

renT : TKit renK
renT = record { syn = renS ; _⊢ᵛ_∷_ = _∋_∷_ ; toTm⊢ = ⊢var ; v0⊢ = here ; wkV⊢ = there }

-- weakening a derivation (the POC's `⊢wk`)
⊢wk : ∀ {Γ} {D : Ctx Γ} {t A B} → D ⊢ t ∷ A → (D ▹ B) ⊢ ren vs t ∷ ren vs A
⊢wk = Preserve.pres renT there

subT : TKit subK
subT = record { syn = subS ; _⊢ᵛ_∷_ = _⊢_∷_ ; toTm⊢ = λ d → d ; v0⊢ = ⊢var here ; wkV⊢ = ⊢wk }

-- substituting into a derivation (the POC's `Sub⊢`)
Sub⊢ : ∀ {Γ Δ} {G : Ctx Γ} {D : Ctx Δ} {σ : Var Γ → T Δ} {t A}
     → Preserve._⊢ᴱ_∶_ subT D σ G → G ⊢ t ∷ A → D ⊢ sub σ t ∷ sub σ A
Sub⊢ = Preserve.pres subT

-- the β instance: a single substitution is a typed environment
single⊢ : ∀ {Γ} {G : Ctx Γ} {u A} → G ⊢ u ∷ A → Preserve._⊢ᴱ_∶_ subT G (single u) (G ▹ A)
single⊢ {u = u} {A = A} d here =
  cast (sym (trans (sub-ren vs (single u) A) (sub-id A))) d
single⊢ {u = u} d (there {x = x} {A = A′} p) =
  cast (sym (trans (sub-ren vs (single u) A′) (sub-id A′))) (⊢var p)

β-sub : ∀ {Γ} {G : Ctx Γ} {t u A B} → (G ▹ A) ⊢ t ∷ B → G ⊢ u ∷ A
      → G ⊢ sub (single u) t ∷ sub (single u) B
β-sub dt du = Sub⊢ (single⊢ du) dt
