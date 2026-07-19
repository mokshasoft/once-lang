------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 18 — the GROUPOID CORE over the de Bruijn kernel,
--                            and its denotational bridge `core → ≋`
--
-- Ports `NbEPDirKernel`'s `Core`/`core→≋` layer onto the STRICT-substitution
-- de Bruijn calculus of `NbEPDirDB`. `Core t u = Id t u × Id u t` — two terms
-- inter-reducible — is the groupoid CORE of the directed identity type: the
-- SYMMETRIC definitional equality, now over a calculus where substitution is
-- strict (propositional `≡`), not merely strict-up-to-`Hom`.
--
--   * Part 1 — the core, algebraically: `core-refl`/`core-sym`/`core-trans`
--     (a groupoid; symmetry recovered here that the directed `Id` refuses) and
--     `core-sub` — the core is stable under the STRICT substitution (`Id-sub`).
--     Axiom-free.
--   * Part 2 — a denotational model + `core → ≋`: a standard STLC interpreter
--     `eval : Γ ⊢ A → Env Γ → ⟦A⟧` into Agda (base type an arbitrary `Base`),
--     with evaluation soundness `⟶ ⊆ ≋` (the semantic substitution lemma
--     `sub-sound` for β, `funext` for the ξ/lam cases — threaded, never
--     assumed). Hence `core → ≋`: inter-reducible terms are OBSERVATIONALLY
--     equal — the definitional equality of the strict calculus is SOUND for
--     the model. This is the de Bruijn analogue of `Sound.agda`/`core→≋`.
--
-- Note on richness: this calculus's reduction is β-only (plus congruence), so
-- `Core` is thin — β is irreversible, so inter-reducibility is close to
-- α-equality. The reversible content (η, commuting conversions) that fattens
-- the core lives one calculus up; here the point is the LAYER (core = the
-- sound symmetric definitional equality over strict substitution), not its
-- girth. `--safe`; funext threaded, otherwise ZERO axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDBCore where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂ )
open import poc.OCP0009.NbEPDirDB
  using ( Ty; ι; _⇒_; Con; ∅; _,_; _∋_; vz; vs; _⊢_; var; lam; app
        ; Ren; extr; ren; Sub; exts; sub; sub1; _[_]
        ; _⟶_; β; ξ-lam; ξ-appˡ; ξ-appʳ; _⟶*_; done; step; Id; Id-sub )

private
  variable
    Γ Δ : Con
    A B : Ty

-- A local product for the core witnesses (`Con`'s `_,_` is taken).
infixr 4 _,,_
record _×_ (P Q : Set) : Set where
  constructor _,,_
  field π₁ : P
        π₂ : Q
open _×_

-- Transitivity of the reduction hom (not exported by `NbEPDirDB`).
⟶*-trans : {t u v : Γ ⊢ A} → t ⟶* u → u ⟶* v → t ⟶* v
⟶*-trans done       q = q
⟶*-trans (step r p) q = step r (⟶*-trans p q)

------------------------------------------------------------------------
-- PART 1 — the groupoid core, algebraically. Axiom-free.
------------------------------------------------------------------------

Core : Γ ⊢ A → Γ ⊢ A → Set
Core t u = Id t u × Id u t

core-refl : {t : Γ ⊢ A} → Core t t
core-refl = done ,, done

-- Symmetric BY CONSTRUCTION — the law the directed `Id` refuses; the core is
-- where symmetry is recovered.
core-sym : {t u : Γ ⊢ A} → Core t u → Core u t
core-sym (p ,, q) = q ,, p

core-trans : {t u v : Γ ⊢ A} → Core t u → Core u v → Core t v
core-trans (p ,, q) (p' ,, q') = ⟶*-trans p p' ,, ⟶*-trans q' q

-- The core is stable under the STRICT substitution — a well-behaved
-- conversion over genuine variables (uses `NbEPDirDB.Id-sub`).
core-sub : (σ : Sub Γ Δ) {t u : Γ ⊢ A} → Core t u → Core (sub σ t) (sub σ u)
core-sub σ (p ,, q) = Id-sub σ p ,, Id-sub σ q

------------------------------------------------------------------------
-- PART 2 — a denotational model, and `core → ≋`. Funext threaded.
------------------------------------------------------------------------

Funext : Set₁
Funext = ∀ {S : Set} {T : S → Set} {f g : (s : S) → T s} →
         (∀ s → f s ≡ g s) → f ≡ g

module _ (Base : Set) where

  ⟦_⟧ty : Ty → Set
  ⟦ ι ⟧ty     = Base
  ⟦ A ⇒ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

  Env : Con → Set
  Env Γ = ∀ {A} → Γ ∋ A → ⟦ A ⟧ty

  extEnv : Env Γ → ⟦ A ⟧ty → Env (Γ , A)
  extEnv γ a vz     = a
  extEnv γ a (vs x) = γ x

  eval : Γ ⊢ A → Env Γ → ⟦ A ⟧ty
  eval (var x)   γ = γ x
  eval (lam t)   γ = λ a → eval t (extEnv γ a)
  eval (app t u) γ = eval t γ (eval u γ)

  -- `eval` respects pointwise-equal environments (funext for the λ case).
  eval-cong : Funext → {γ γ' : Env Γ} → (∀ {A} (x : Γ ∋ A) → γ x ≡ γ' x) →
              (t : Γ ⊢ A) → eval t γ ≡ eval t γ'
  eval-cong fe h (var x)   = h x
  eval-cong fe h (lam t)   =
    fe (λ a → eval-cong fe (λ { vz → refl ; (vs x) → h x }) t)
  eval-cong fe h (app t u) =
    cong₂ (λ f x → f x) (eval-cong fe h t) (eval-cong fe h u)

  -- Renaming soundness: `eval (ren ρ t) δ = eval t (δ ∘ ρ)`.
  _∘ᵣₑ_ : Env Δ → Ren Γ Δ → Env Γ
  (δ ∘ᵣₑ ρ) x = δ (ρ x)

  ren-sound : Funext → (ρ : Ren Γ Δ) (t : Γ ⊢ A) (δ : Env Δ) →
              eval (ren ρ t) δ ≡ eval t (δ ∘ᵣₑ ρ)
  ren-sound fe ρ (var x)   δ = refl
  ren-sound fe ρ (app t u) δ =
    cong₂ (λ f x → f x) (ren-sound fe ρ t δ) (ren-sound fe ρ u δ)
  ren-sound fe ρ (lam t)   δ = fe (λ a →
    trans (ren-sound fe (extr ρ) t (extEnv δ a))
          (eval-cong fe (λ { vz → refl ; (vs x) → refl }) t))

  -- Substitution soundness: `eval (sub σ t) δ = eval t (semantic-env σ δ)`.
  semσ : Sub Γ Δ → Env Δ → Env Γ
  semσ σ δ x = eval (σ x) δ

  sub-sound : Funext → (σ : Sub Γ Δ) (t : Γ ⊢ A) (δ : Env Δ) →
              eval (sub σ t) δ ≡ eval t (semσ σ δ)
  sub-sound fe σ (var x)   δ = refl
  sub-sound fe σ (app t u) δ =
    cong₂ (λ f x → f x) (sub-sound fe σ t δ) (sub-sound fe σ u δ)
  sub-sound fe σ (lam t)   δ = fe (λ a →
    trans (sub-sound fe (exts σ) t (extEnv δ a))
          (eval-cong fe (bridge a) t))
    where
    bridge : (a : ⟦ _ ⟧ty) {C : Ty} (y : (_ , _) ∋ C) →
             semσ (exts σ) (extEnv δ a) y ≡ extEnv (semσ σ δ) a y
    bridge a vz     = refl
    bridge a (vs x) = trans (ren-sound fe vs (σ x) (extEnv δ a))
                            (eval-cong fe (λ y → refl) (σ x))

  -- Evaluation soundness: reduction preserves denotation, `⟶ ⊆ ≋`.
  eval-sound : Funext → {t u : Γ ⊢ A} → t ⟶ u → (δ : Env Γ) →
               eval t δ ≡ eval u δ
  eval-sound fe (β t s)         δ =
    trans (eval-cong fe (λ { vz → refl ; (vs x) → refl }) t)
          (sym (sub-sound fe (sub1 s) t δ))
  eval-sound fe (ξ-lam r)       δ = fe (λ a → eval-sound fe r (extEnv δ a))
  eval-sound fe (ξ-appˡ {u = u} r) δ = cong (λ f → f (eval u δ)) (eval-sound fe r δ)
  eval-sound fe (ξ-appʳ {t = t} r) δ = cong (eval t δ) (eval-sound fe r δ)

  ------------------------------------------------------------------------
  -- Observational equality, and the bridge: `core(Hom) ⊆ ≋`. Inter-reducible
  -- terms denote equally — the strict calculus's definitional equality is
  -- SOUND for the model.
  ------------------------------------------------------------------------

  infix 4 _≋_
  _≋_ : Γ ⊢ A → Γ ⊢ A → Set
  t ≋ u = (δ : Env _) → eval t δ ≡ eval u δ

  Id→≋ : Funext → {t u : Γ ⊢ A} → Id t u → t ≋ u
  Id→≋ fe done       δ = refl
  Id→≋ fe (step r p) δ = trans (eval-sound fe r δ) (Id→≋ fe p δ)

  core→≋ : Funext → {t u : Γ ⊢ A} → Core t u → t ≋ u
  core→≋ fe c = Id→≋ fe (π₁ c)
