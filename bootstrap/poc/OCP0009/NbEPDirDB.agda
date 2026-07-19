------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 16 — a DE BRUIJN kernel: substitution strict ON THE
--                            NOSE, and `Id = Hom` over genuine variables
--
-- The refinement of `NbEPDirKernel` flagged in HANDOFF §5(a). There, in the
-- point-free CCC, substitution was PRECOMPOSITION and its coherence laws were
-- REDUCTIONS (`t[id] ⟶ t` = `id-right`, `t[σ][τ] ⟶ t[σ∘τ]` = `assoc-r`) — so
-- substitution was strict only *up to `Hom`*. Here we pay for genuine
-- variables and get the laws AS EQUALITIES:
--
--   * an intrinsically-typed de Bruijn STLC (`_⊢_`), CARTESIAN (variables may
--     be used any number of times — weakening + contraction are free);
--   * RENAMINGS + parallel SUBSTITUTIONS as the standard two-layer calculus,
--     with the four fusion lemmas (`ren-ren`/`sub-ren`/`ren-sub`/`sub-sub`)
--     and `sub-id` — proven `--safe`, FUNEXT-FREE (a pointwise `sub-cong`
--     discharges every binder case);
--   * the CATEGORY-OF-CONTEXTS laws ON THE NOSE (propositional `≡`, no
--     reduction): `[id]` (`sub idₛ t ≡ t`), `[∘]` (`sub τ (sub σ t) ≡
--     sub (τ ∘ₛ σ) t`), and `idₛ`/`_∘ₛ_` unit + associativity;
--   * `_⟶_` β-reduction, `Id = Hom = ⟶*` as before, and THE kernel lemma
--     `⟶-sub` — substitution commutes with reduction — whose β case now has
--     REAL content: the substitution lemma `sub σ (t [ s ]) ≡
--     (sub (exts σ) t) [ sub σ s ]`, closed by `sub-sub` + `sub-id`.
--
-- Honest ceiling: "on the nose" here means PROPOSITIONAL `≡` (proven), not
-- DEFINITIONAL `refl`. Making `[id]`/`[∘]` hold definitionally needs an
-- explicit-substitution QIIT (quotient) — cubical, outside `--safe` MLTT.
-- But proven `≡` is already strictly stronger than `NbEPDirKernel`'s `⟶`
-- coherences: the strictness now lives in the SET of terms, not merely in
-- `Hom`. The `core(Hom) =` definitional-equality story carries over verbatim.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDB where

open import normalizer.Syntax.Types
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

------------------------------------------------------------------------
-- Types, contexts, variables, terms — intrinsically typed de Bruijn.
------------------------------------------------------------------------

infixr 7 _⇒_
data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

infixl 5 _,_
data Con : Set where
  ∅   : Con
  _,_ : Con → Ty → Con

infix 4 _∋_
data _∋_ : Con → Ty → Set where
  vz : ∀ {Γ A}   → (Γ , A) ∋ A
  vs : ∀ {Γ A B} → Γ ∋ A → (Γ , B) ∋ A

infix 4 _⊢_
data _⊢_ : Con → Ty → Set where
  var : ∀ {Γ A}   → Γ ∋ A → Γ ⊢ A
  lam : ∀ {Γ A B} → (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
  app : ∀ {Γ A B} → Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B

private
  variable
    Γ Δ Θ : Con
    A B : Ty

------------------------------------------------------------------------
-- Renamings (variable-for-variable) and their functorial action.
------------------------------------------------------------------------

Ren : Con → Con → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

extr : Ren Γ Δ → Ren (Γ , B) (Δ , B)
extr ρ vz     = vz
extr ρ (vs x) = vs (ρ x)

ren : Ren Γ Δ → Γ ⊢ A → Δ ⊢ A
ren ρ (var x)   = var (ρ x)
ren ρ (lam t)   = lam (ren (extr ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)

------------------------------------------------------------------------
-- Substitutions (variable-for-term) and their action; `exts` lifts under a
-- binder using renaming (weakening) — the standard two-layer trick.
------------------------------------------------------------------------

Sub : Con → Con → Set
Sub Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : Sub Γ Δ → Sub (Γ , B) (Δ , B)
exts σ vz     = var vz
exts σ (vs x) = ren vs (σ x)

sub : Sub Γ Δ → Γ ⊢ A → Δ ⊢ A
sub σ (var x)   = σ x
sub σ (lam t)   = lam (sub (exts σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)

-- The category of contexts: identity and the four composition operators
-- (defined with explicit indices so they are genuine `Ren`/`Sub`, not
-- implicit-argument lambdas).
idₛ : Sub Γ Γ
idₛ = var

infixr 8 _∘ᵣ_ _ₛ∘ᵣ_ _ᵣ∘ₛ_ _∘ₛ_
_∘ᵣ_ : Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)

_ₛ∘ᵣ_ : Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)

_ᵣ∘ₛ_ : Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = ren ρ (σ x)

_∘ₛ_ : Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = sub τ (σ x)

-- Single substitution for the last variable — what β plugs in.
sub1 : Γ ⊢ A → Sub (Γ , A) Γ
sub1 s vz     = s
sub1 s (vs x) = var x

infix 8 _[_]
_[_] : (Γ , A) ⊢ B → Γ ⊢ A → Γ ⊢ B
t [ s ] = sub (sub1 s) t

------------------------------------------------------------------------
-- Congruence of the actions under POINTWISE-equal renamings/substitutions.
-- This is what keeps the whole development funext-free: every binder case
-- gets its lifted substitutions compared pointwise, by case on the variable.
------------------------------------------------------------------------

extr-cong : {ρ ρ' : Ren Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ρ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → extr ρ x ≡ extr ρ' x
extr-cong h vz     = refl
extr-cong h (vs x) = cong vs (h x)

ren-cong : {ρ ρ' : Ren Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ρ' x) →
           (t : Γ ⊢ A) → ren ρ t ≡ ren ρ' t
ren-cong h (var x)   = cong var (h x)
ren-cong h (lam t)   = cong lam (ren-cong (extr-cong h) t)
ren-cong h (app t u) = cong₂ app (ren-cong h t) (ren-cong h u)

exts-cong : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ σ' x) →
            ∀ {A : Ty} (x : (Γ , B) ∋ A) → exts σ x ≡ exts σ' x
exts-cong h vz     = refl
exts-cong h (vs x) = cong (ren vs) (h x)

sub-cong : {σ σ' : Sub Γ Δ} → (∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ σ' x) →
           (t : Γ ⊢ A) → sub σ t ≡ sub σ' t
sub-cong h (var x)   = h x
sub-cong h (lam t)   = cong lam (sub-cong (exts-cong h) t)
sub-cong h (app t u) = cong₂ app (sub-cong h t) (sub-cong h u)

------------------------------------------------------------------------
-- The four fusion lemmas. Each binder case bridges "lift-then-compose" and
-- "compose-then-lift" by a pointwise ext-lemma fed through `*-cong`.
------------------------------------------------------------------------

-- ren ∘ ren.
extr-extr : (ρ' : Ren Δ Θ) (ρ : Ren Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extr ρ' ∘ᵣ extr ρ) x ≡ extr (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz     = refl
extr-extr ρ' ρ (vs x) = refl

ren-ren : {ρ' : Ren Δ Θ} {ρ : Ren Γ Δ} (t : Γ ⊢ A) →
          ren ρ' (ren ρ t) ≡ ren (ρ' ∘ᵣ ρ) t
ren-ren (var x)   = refl
ren-ren {ρ' = ρ'} {ρ} (lam t) =
  cong lam (trans (ren-ren t) (ren-cong (extr-extr ρ' ρ) t))
ren-ren (app t u) = cong₂ app (ren-ren t) (ren-ren u)

-- sub ∘ ren.
exts-extr : (σ : Sub Δ Θ) (ρ : Ren Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (exts σ ₛ∘ᵣ extr ρ) x ≡ exts (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz     = refl
exts-extr σ ρ (vs x) = refl

sub-ren : {σ : Sub Δ Θ} {ρ : Ren Γ Δ} (t : Γ ⊢ A) →
          sub σ (ren ρ t) ≡ sub (σ ₛ∘ᵣ ρ) t
sub-ren (var x)   = refl
sub-ren {σ = σ} {ρ} (lam t) =
  cong lam (trans (sub-ren t) (sub-cong (exts-extr σ ρ) t))
sub-ren (app t u) = cong₂ app (sub-ren t) (sub-ren u)

-- ren ∘ sub.
extr-exts : (ρ : Ren Δ Θ) (σ : Sub Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (extr ρ ᵣ∘ₛ exts σ) x ≡ exts (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz     = refl
extr-exts ρ σ (vs x) = trans (ren-ren (σ x)) (sym (ren-ren (σ x)))

ren-sub : {ρ : Ren Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
          ren ρ (sub σ t) ≡ sub (ρ ᵣ∘ₛ σ) t
ren-sub (var x)   = refl
ren-sub {ρ = ρ} {σ} (lam t) =
  cong lam (trans (ren-sub t) (sub-cong (extr-exts ρ σ) t))
ren-sub (app t u) = cong₂ app (ren-sub t) (ren-sub u)

-- sub ∘ sub.
exts-exts : (τ : Sub Δ Θ) (σ : Sub Γ Δ) {A : Ty} (x : (Γ , B) ∋ A) →
            (exts τ ∘ₛ exts σ) x ≡ exts (τ ∘ₛ σ) x
exts-exts τ σ vz     = refl
exts-exts τ σ (vs x) = trans (sub-ren (σ x)) (sym (ren-sub (σ x)))

sub-sub : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
          sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
sub-sub (var x)   = refl
sub-sub {τ = τ} {σ} (lam t) =
  cong lam (trans (sub-sub t) (sub-cong (exts-exts τ σ) t))
sub-sub (app t u) = cong₂ app (sub-sub t) (sub-sub u)

-- Identity: `exts` preserves the identity substitution, hence `sub idₛ = id`.
exts-id : ∀ {A : Ty} (x : (Γ , B) ∋ A) → exts idₛ x ≡ idₛ x
exts-id vz     = refl
exts-id (vs x) = refl

sub-id : (t : Γ ⊢ A) → sub idₛ t ≡ t
sub-id (var x)   = refl
sub-id (lam t)   = cong lam (trans (sub-cong exts-id t) (sub-id t))
sub-id (app t u) = cong₂ app (sub-id t) (sub-id u)

------------------------------------------------------------------------
-- THE CATEGORY-OF-CONTEXTS LAWS — ON THE NOSE (propositional `≡`).
-- Substitution is strict: these are equalities of TERMS / substitutions,
-- not reductions. (Contrast `NbEPDirKernel`, where they were `⟶` steps.)
------------------------------------------------------------------------

-- `[id]` and `[∘]` on terms.
[id] : (t : Γ ⊢ A) → sub idₛ t ≡ t
[id] = sub-id

[∘] : {τ : Sub Δ Θ} {σ : Sub Γ Δ} (t : Γ ⊢ A) →
      sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
[∘] = sub-sub

-- `_∘ₛ_` is a category (unit + associativity), pointwise.
∘ₛ-idˡ : (σ : Sub Γ Δ) {A : Ty} (x : Γ ∋ A) → (idₛ ∘ₛ σ) x ≡ σ x
∘ₛ-idˡ σ x = sub-id (σ x)

∘ₛ-idʳ : (σ : Sub Γ Δ) {A : Ty} (x : Γ ∋ A) → (σ ∘ₛ idₛ) x ≡ σ x
∘ₛ-idʳ σ x = refl

∘ₛ-assoc : ∀ {Γ Δ Θ Ξ} (ρ : Sub Θ Ξ) (τ : Sub Δ Θ) (σ : Sub Γ Δ)
           {A : Ty} (x : Γ ∋ A) → ((ρ ∘ₛ τ) ∘ₛ σ) x ≡ (ρ ∘ₛ (τ ∘ₛ σ)) x
∘ₛ-assoc ρ τ σ x = sym (sub-sub (σ x))

------------------------------------------------------------------------
-- Reduction, the directed identity type, and THE kernel lemma.
------------------------------------------------------------------------

infix 3 _⟶_
data _⟶_ : Γ ⊢ A → Γ ⊢ A → Set where
  β      : (t : (Γ , A) ⊢ B) (s : Γ ⊢ A) → app (lam t) s ⟶ t [ s ]
  ξ-lam  : {t t' : (Γ , A) ⊢ B} → t ⟶ t' → lam t ⟶ lam t'
  ξ-appˡ : {t t' : Γ ⊢ (A ⇒ B)} {u : Γ ⊢ A} → t ⟶ t' → app t u ⟶ app t' u
  ξ-appʳ : {t : Γ ⊢ (A ⇒ B)} {u u' : Γ ⊢ A} → u ⟶ u' → app t u ⟶ app t u'

infix 3 _⟶*_
data _⟶*_ : Γ ⊢ A → Γ ⊢ A → Set where
  done : {t : Γ ⊢ A} → t ⟶* t
  step : {t u v : Γ ⊢ A} → t ⟶ u → u ⟶* v → t ⟶* v

-- `Id` = the directed reduction hom, exactly as in `NbEPDirKernel`.
Id : Γ ⊢ A → Γ ⊢ A → Set
Id t u = t ⟶* u

-- THE β SUBSTITUTION LEMMA — the real content of subst-commutes-with-β:
-- substituting a redex's contractum agrees with contracting the substituted
-- redex. Closed by `sub-sub` (both sides) + a pointwise bridge using
-- `sub-ren` and `sub-id`.
sub-comm : (σ : Sub Γ Δ) (t : (Γ , A) ⊢ B) (s : Γ ⊢ A) →
           sub σ (t [ s ]) ≡ sub (sub1 (sub σ s)) (sub (exts σ) t)
sub-comm {Γ} {Δ} {A} σ t s =
  trans (sub-sub {τ = σ} {σ = sub1 s} t)
        (trans (sub-cong bridge t)
               (sym (sub-sub {τ = sub1 (sub σ s)} {σ = exts σ} t)))
  where
  bridge : ∀ {C} (x : (Γ , A) ∋ C) →
           (σ ∘ₛ sub1 s) x ≡ (sub1 (sub σ s) ∘ₛ exts σ) x
  bridge vz     = refl
  bridge (vs x) = sym (trans (sub-ren (σ x)) (sub-id (σ x)))

------------------------------------------------------------------------
-- Substitution commutes with reduction — single step and its closure. The
-- β case transports along `sub-comm`; the ξ cases recurse (under `lam`, the
-- substitution lifts to `exts σ`).
------------------------------------------------------------------------

⟶-sub : (σ : Sub Γ Δ) {t u : Γ ⊢ A} → t ⟶ u → sub σ t ⟶ sub σ u
⟶-sub σ (β t s)    =
  subst (λ z → app (lam (sub (exts σ) t)) (sub σ s) ⟶ z)
        (sym (sub-comm σ t s))
        (β (sub (exts σ) t) (sub σ s))
⟶-sub σ (ξ-lam r)  = ξ-lam (⟶-sub (exts σ) r)
⟶-sub σ (ξ-appˡ r) = ξ-appˡ (⟶-sub σ r)
⟶-sub σ (ξ-appʳ r) = ξ-appʳ (⟶-sub σ r)

-- The kernel lemma, at `Id = ⟶*`: `Id` is stable under (now STRICT)
-- substitution — the de Bruijn analogue of `NbEPDirKernel.Id-sub`.
Id-sub : (σ : Sub Γ Δ) {t u : Γ ⊢ A} → Id t u → Id (sub σ t) (sub σ u)
Id-sub σ done       = done
Id-sub σ (step r p) = step (⟶-sub σ r) (Id-sub σ p)

------------------------------------------------------------------------
-- The groupoid core carries over verbatim: `Core t u = Id t u × Id u t` is
-- the symmetric definitional equality, now over a STRICTLY substitutive
-- calculus. (Symmetry/reflexivity/transitivity/subst-stability exactly as in
-- `NbEPDirKernel`; omitted here — the point of this module is the strict
-- substitution calculus underneath.)
------------------------------------------------------------------------
