------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 38 — a STRICT directed CwF core, transport-free,
--            universe-parametric (the consistency tower's generic rung)
--
-- The redesign asked for: stop working AROUND `Sub`'s propositional proof
-- fields, and instead present the CwF so the transport-free principle holds
-- NATIVELY.  The move is to separate the DATA from the LAWS:
--
--   * a substitution is LAW-FREE functor data (`ob`/`mor` only) — so `_∘_` is
--     plain function composition, DEFINITIONALLY associative and unital;
--   * a type is a LAW-FREE covariant family (`fam`/`act` only) — so `_[_]` is
--     plain precomposition, DEFINITIONALLY functorial.
--
-- The payoff is that substitution-stability of the type formers is **`refl`** —
-- no `funext`, no `uip`, no `subst`, no `Ty` extensionality wrapper.  This is the
-- SAME strictness-by-construction the syntactic kernel already enjoys (dHoTT-20),
-- now on the SEMANTIC side:
--
--   * `[]-id`   : `A [ idSub ] ≡ A`                        — `refl`
--   * `[]-∘`    : `A [ σ ] [ τ ] ≡ A [ σ ∘ τ ]`           — `refl`
--   * `Σ-stable`: `(Σ' A B)[σ] ≡ Σ' (A[σ]) (B[σ ↑ A])`    — `refl`
--   * `×-stable`: `(A ×' B)[σ] ≡ (A[σ]) ×' (B[σ])`        — `refl`
--
-- UNIVERSE-PARAMETRIC.  Everything is polymorphic in the fibre level `ℓ'`
-- (`Ty Γ ℓ' : Set (ℓ ⊔ lsuc ℓ')`): a type at level `ℓ'` is classified one level
-- up.  This is exactly the shape of the CONSISTENCY TOWER's generic step —
-- `Once_n` modelled at level `ℓ'`, `Once_{n+1}` one level up — so this core is
-- meant to be the SINGLE level-parametric rung whose instances give the whole
-- ladder `Once ⊂ Once⁺ ⊂ Once⁺⁺ ⊂ …`, rather than a one-off model.
--
-- HONEST SCOPE — what strictness does and does NOT buy.  Making substitution
-- definitionally strict makes the COVARIANT-STABLE formers (`Σ`, `×`) `refl`-
-- stable.  It does NOT resolve the DIRECTED `Π⁺` future-cone: its fibre indexes
-- over the BASE category's morphisms, which genuinely change under a Cat→Cat
-- substitution (Beck–Chevalley failure — `NbEPDirPiSub`).  That laxness is real
-- mathematics, not a coherence artifact, so it survives strictification for
-- general base change (it is strict only along exact `σ`, e.g. isos).  The win
-- here is the clean strict substitution + `refl`-stable ordinary formers.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirStrict where

open import Agda.Primitive using ( Level; lzero; lsuc; _⊔_ )
open import Agda.Builtin.Equality using ( _≡_; refl )
open import Agda.Builtin.Sigma using ( Σ; _,_; fst; snd )

------------------------------------------------------------------------
-- Contexts as directed graphs/categories; LAW-FREE substitutions.
------------------------------------------------------------------------

record Ctx (ℓ : Level) : Set (lsuc ℓ) where
  field
    W   : Set ℓ
    Hom : W → W → Set ℓ
open Ctx

-- a substitution is FUNCTOR DATA with NO laws — so composition is strict.
record Sub {ℓ} (Δ Γ : Ctx ℓ) : Set ℓ where
  field
    ob  : W Δ → W Γ
    mor : ∀ {x y} → Hom Δ x y → Hom Γ (ob x) (ob y)
open Sub

idSub : ∀ {ℓ} {Γ : Ctx ℓ} → Sub Γ Γ
idSub = record { ob = λ x → x ; mor = λ f → f }

infixr 9 _∘_
_∘_ : ∀ {ℓ} {Θ Δ Γ : Ctx ℓ} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
σ ∘ τ = record { ob = λ x → ob σ (ob τ x) ; mor = λ f → mor σ (mor τ f) }

-- the strict CATEGORY LAWS hold DEFINITIONALLY (this is the whole point):
∘-idˡ : ∀ {ℓ} {Δ Γ : Ctx ℓ} (σ : Sub Δ Γ) → (idSub ∘ σ) ≡ σ
∘-idˡ σ = refl

∘-idʳ : ∀ {ℓ} {Δ Γ : Ctx ℓ} (σ : Sub Δ Γ) → (σ ∘ idSub) ≡ σ
∘-idʳ σ = refl

∘-assoc : ∀ {ℓ} {Ξ Θ Δ Γ : Ctx ℓ} (σ : Sub Δ Γ) (τ : Sub Θ Δ) (ρ : Sub Ξ Θ) →
          ((σ ∘ τ) ∘ ρ) ≡ (σ ∘ (τ ∘ ρ))
∘-assoc σ τ ρ = refl

------------------------------------------------------------------------
-- Types as LAW-FREE covariant families; substitution = precomposition.
------------------------------------------------------------------------

record Ty {ℓ} (Γ : Ctx ℓ) (ℓ' : Level) : Set (ℓ ⊔ lsuc ℓ') where
  field
    fam : W Γ → Set ℓ'
    act : ∀ {x y} → Hom Γ x y → fam x → fam y
open Ty

infix 8 _[_]
_[_] : ∀ {ℓ ℓ'} {Δ Γ : Ctx ℓ} → Ty Γ ℓ' → Sub Δ Γ → Ty Δ ℓ'
A [ σ ] = record { fam = λ x → fam A (ob σ x)
                 ; act = λ f a → act A (mor σ f) a }

-- ★ substitution is DEFINITIONALLY STRICT — the coherences are `refl`.
[]-id : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} (A : Ty Γ ℓ') → A [ idSub ] ≡ A
[]-id A = refl

[]-∘ : ∀ {ℓ ℓ'} {Θ Δ Γ : Ctx ℓ} (A : Ty Γ ℓ') (σ : Sub Δ Γ) (τ : Sub Θ Δ) →
       A [ σ ] [ τ ] ≡ A [ σ ∘ τ ]
[]-∘ A σ τ = refl

------------------------------------------------------------------------
-- Context extension and the lifted substitution `σ ↑ A`.
------------------------------------------------------------------------

infixl 5 _▷_
_▷_ : ∀ {ℓ ℓ'} (Γ : Ctx ℓ) (A : Ty Γ ℓ') → Ctx (ℓ ⊔ ℓ')
Γ ▷ A = record
  { W   = Σ (W Γ) (fam A)
  ; Hom = λ p q → Σ (Hom Γ (fst p) (fst q)) (λ h → act A h (snd p) ≡ snd q) }

-- the lift: its `mor` proof is the source proof VERBATIM (`snd m`), because
-- `act (A [ σ ]) f = act A (mor σ f)` DEFINITIONALLY.  Transport-free.
infixl 6 _↑_
_↑_ : ∀ {ℓ ℓ'} {Δ Γ : Ctx ℓ} (σ : Sub Δ Γ) (A : Ty Γ ℓ') →
      Sub (Δ ▷ (A [ σ ])) (Γ ▷ A)
σ ↑ A = record
  { ob  = λ p → (ob σ (fst p) , snd p)
  ; mor = λ m → (mor σ (fst m) , snd m) }

------------------------------------------------------------------------
-- Type formers, and their `refl` substitution-stability.
------------------------------------------------------------------------

-- dependent sum (a covariant former — genuinely stable).
Σ' : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} (A : Ty Γ ℓ') (B : Ty (Γ ▷ A) ℓ') → Ty Γ ℓ'
Σ' A B = record
  { fam = λ x → Σ (fam A x) (λ a → fam B (x , a))
  ; act = λ h p → (act A h (fst p) , act B (h , refl) (snd p)) }

-- ★ Σ-STABILITY IS `refl` — transport-free, no funext/uip/wrapper.
Σ-stable : ∀ {ℓ ℓ'} {Δ Γ : Ctx ℓ} (σ : Sub Δ Γ)
           (A : Ty Γ ℓ') (B : Ty (Γ ▷ A) ℓ') →
           (Σ' A B) [ σ ] ≡ Σ' (A [ σ ]) (B [ σ ↑ A ])
Σ-stable σ A B = refl

-- non-dependent product.
infixr 7 _×'_
_×'_ : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} (A B : Ty Γ ℓ') → Ty Γ ℓ'
A ×' B = record
  { fam = λ x → Σ (fam A x) (λ _ → fam B x)
  ; act = λ h p → (act A h (fst p) , act B h (snd p)) }

-- ★ ×-STABILITY IS `refl`.
×-stable : ∀ {ℓ ℓ'} {Δ Γ : Ctx ℓ} (σ : Sub Δ Γ) (A B : Ty Γ ℓ') →
           (A ×' B) [ σ ] ≡ (A [ σ ]) ×' (B [ σ ])
×-stable σ A B = refl

------------------------------------------------------------------------
-- Terms (natural sections), and a UNIVERSE reflecting the level below —
-- the relative-consistency ladder's generic rung.
------------------------------------------------------------------------

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

-- a term is a natural section of a type.
record Tm {ℓ ℓ'} (Γ : Ctx ℓ) (A : Ty Γ ℓ') : Set (ℓ ⊔ ℓ') where
  field
    tm  : (x : W Γ) → fam A x
    nat : ∀ {x y} (h : Hom Γ x y) → act A h (tm x) ≡ tm y
open Tm

-- terms substitute (and, like types, definitionally).
infix 8 _[_]ᵗ
_[_]ᵗ : ∀ {ℓ ℓ'} {Δ Γ : Ctx ℓ} {A : Ty Γ ℓ'} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ])
t [ σ ]ᵗ = record { tm = λ x → tm t (ob σ x) ; nat = λ h → nat t (mor σ h) }

------------------------------------------------------------------------
-- The universe.  `U ℓ'` over Γ REFLECTS the collection of level-`ℓ'` types as a
-- single type ONE LEVEL UP (`Ty Γ (ℓ ⊔ lsuc ℓ')`).  `code`/`El` witness the
-- reflection, and the computation rule `El (code A) ≡ A` is **`refl`** — the
-- decode is DEFINITIONAL (transport-free), because a code's naturality is `refl`
-- and `subst P refl` computes away.
------------------------------------------------------------------------

U : ∀ {ℓ} (ℓ' : Level) {Γ : Ctx ℓ} → Ty Γ (ℓ ⊔ lsuc ℓ')
U ℓ' {Γ} = record { fam = λ _ → Ty Γ ℓ' ; act = λ _ A → A }

code : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} → Ty Γ ℓ' → Tm Γ (U ℓ')
code A = record { tm = λ _ → A ; nat = λ _ → refl }

El : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} → Tm Γ (U ℓ') → Ty Γ ℓ'
El t = record
  { fam = λ x → fam (tm t x) x
  ; act = λ {x} {y} h v → subst (λ C → fam C y) (nat t h) (act (tm t x) h v) }

-- ★ the universe COMPUTATION RULE — decode after encode is the identity,
--   DEFINITIONALLY.  This is the soundness of the reflection: `Once_n`'s types
--   are faithfully present as objects at the next level.
El-code : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} (A : Ty Γ ℓ') → El (code A) ≡ A
El-code A = refl

-- ★ THE LADDER RUNG, ITERATED.  The universe of level `ℓ'` is ITSELF classified
--   one level up (`code (U ℓ')`), and decodes back DEFINITIONALLY.  Because the
--   whole core is level-parametric, this is uniform in the level — instantiating
--   `ℓ' := ℓ'₀, lsuc ℓ'₀, …` gives the relative-consistency tower
--   `Once ⊂ Once⁺ ⊂ Once⁺⁺ ⊂ …`, each rung modelled in the next, all from ONE
--   construction.  (Gödel is not bypassed — the reflection needs a level strictly
--   above, so the ladder never closes on itself; trust retreats to the limit.)
ladder : ∀ {ℓ ℓ'} {Γ : Ctx ℓ} → El (code (U ℓ' {Γ})) ≡ U ℓ' {Γ}
ladder {ℓ' = ℓ'} {Γ = Γ} = El-code (U ℓ' {Γ})
