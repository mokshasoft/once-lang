------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 43 — a GENUINELY DEPENDENT raw calculus + its full
--   SYNTACTIC METATHEORY (renaming and substitution preserve typing).
--
-- The honest genuinely-dependent raw route (after finding the code-based route was
-- non-dependent — see PATHS/FINDINGS).  Dependency comes from a TYPE-LEVEL large
-- elimination `𝕀 t A B` (`if t then A else B`), so `Π̇ 𝔹 (𝕀 (var vz) A B)` is a
-- real dependent function type and `⊢app`'s result type `subTy (single u) B` is
-- NON-vacuous (contrast the code-based `⌜Π⌝`, whose codomain could not mention the
-- domain variable).  Contents, all `--safe`, zero axioms/postulates/holes:
--   * the syntax: terms `Tm` and TERM-DEPENDENT types `Ty` (`𝔹`/`⊥̇`/`𝕀`/`Π̇`);
--   * de Bruijn renaming + substitution, with the full fusion algebra;
--   * the dependent typing relation `_⊢_∷_` (+ a concrete dependent type example);
--   * ★ `ren-⊢`  — RENAMING preserves typing;
--   * ★ `sub-⊢`  — SUBSTITUTION preserves typing (the `app` case rests on the
--     genuine, non-vacuous `subTy-comm` for the dependent codomain).
--
-- These are the syntactic lemmas that the set-model soundness (M3c) rests on.  The
-- remaining rung — the set interpretation `⟦_⟧` with its semantic weakening/subst
-- lemmas + derivation-coherence — is the standard coherence-heavy DTT-soundness
-- core; its SEMANTIC analogue (genuinely-dependent CONSISTENCY) is already proven
-- intrinsically in NbEPDirDepIR (dHoTT-41) and NbEPDirDHoTT3 (the full kernel).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDTT where

open import Agda.Builtin.Equality using ( _≡_; refl )

cong  : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl
cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} (f : A → B → C)
        {x x' y y'} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl
cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x x' y y' z z'} →
        x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl
sym   : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

------------------------------------------------------------------------
-- Scopes, variables, terms, and (term-dependent) types.
------------------------------------------------------------------------

data Cx : Set where
  ε   : Cx
  _∙  : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ}   → Var (Γ ∙)
  vs : ∀ {Γ}   → Var Γ → Var (Γ ∙)

data Tm : Cx → Set where
  var   : ∀ {Γ} → Var Γ → Tm Γ
  tt ff : ∀ {Γ} → Tm Γ
  lam   : ∀ {Γ} → Tm (Γ ∙) → Tm Γ
  app   : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ

data Ty : Cx → Set where
  𝔹  : ∀ {Γ} → Ty Γ                              -- booleans
  ⊥̇  : ∀ {Γ} → Ty Γ                              -- the empty type
  𝕀  : ∀ {Γ} → Tm Γ → Ty Γ → Ty Γ → Ty Γ         -- type-level if (LARGE ELIM)
  Π̇  : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ            -- dependent function

------------------------------------------------------------------------
-- Renaming and substitution (SN-module technique), on terms and types.
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : ∀ {Γ Δ} → Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

ren : ∀ {Γ Δ} → Ren Γ Δ → Tm Γ → Tm Δ
ren ρ (var x)   = var (ρ x)
ren ρ tt        = tt
ren ρ ff        = ff
ren ρ (lam t)   = lam (ren (extR ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)

renTy : ∀ {Γ Δ} → Ren Γ Δ → Ty Γ → Ty Δ
renTy ρ 𝔹        = 𝔹
renTy ρ ⊥̇        = ⊥̇
renTy ρ (𝕀 t A B) = 𝕀 (ren ρ t) (renTy ρ A) (renTy ρ B)
renTy ρ (Π̇ A B)  = Π̇ (renTy ρ A) (renTy (extR ρ) B)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : ∀ {Γ Δ} → Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = ren vs (σ x)

sub : ∀ {Γ Δ} → Sub Γ Δ → Tm Γ → Tm Δ
sub σ (var x)   = σ x
sub σ tt        = tt
sub σ ff        = ff
sub σ (lam t)   = lam (sub (extS σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)

subTy : ∀ {Γ Δ} → Sub Γ Δ → Ty Γ → Ty Δ
subTy σ 𝔹        = 𝔹
subTy σ ⊥̇        = ⊥̇
subTy σ (𝕀 t A B) = 𝕀 (sub σ t) (subTy σ A) (subTy σ B)
subTy σ (Π̇ A B)  = Π̇ (subTy σ A) (subTy (extS σ) B)

ids : ∀ {Γ} → Sub Γ Γ
ids = var

single : ∀ {Γ} → Tm Γ → Sub (Γ ∙) Γ
single u vz     = u
single u (vs x) = var x

------------------------------------------------------------------------
-- Composition operators + the fusion lemmas (terms and types), funext-free.
------------------------------------------------------------------------

_∘ᵣ_ : ∀ {Γ Δ Θ} → Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
(ρ' ∘ᵣ ρ) x = ρ' (ρ x)
_ₛ∘ᵣ_ : ∀ {Γ Δ Θ} → Sub Δ Θ → Ren Γ Δ → Sub Γ Θ
(σ ₛ∘ᵣ ρ) x = σ (ρ x)
_ᵣ∘ₛ_ : ∀ {Γ Δ Θ} → Ren Δ Θ → Sub Γ Δ → Sub Γ Θ
(ρ ᵣ∘ₛ σ) x = ren ρ (σ x)
_∘ₛ_ : ∀ {Γ Δ Θ} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
(τ ∘ₛ σ) x = sub τ (σ x)

extR-cong : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) →
            ∀ (x : Var (Γ ∙)) → extR ρ x ≡ extR ρ' x
extR-cong h vz     = refl
extR-cong h (vs x) = cong vs (h x)
ren-cong : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) → (t : Tm Γ) → ren ρ t ≡ ren ρ' t
ren-cong h (var x)   = cong var (h x)
ren-cong h tt        = refl
ren-cong h ff        = refl
ren-cong h (lam t)   = cong lam (ren-cong (extR-cong h) t)
ren-cong h (app t u) = cong₂ app (ren-cong h t) (ren-cong h u)
renTy-cong : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) → (A : Ty Γ) → renTy ρ A ≡ renTy ρ' A
renTy-cong h 𝔹        = refl
renTy-cong h ⊥̇        = refl
renTy-cong h (𝕀 t A B) = cong₃ 𝕀 (ren-cong h t) (renTy-cong h A) (renTy-cong h B)
renTy-cong h (Π̇ A B)  = cong₂ Π̇ (renTy-cong h A) (renTy-cong (extR-cong h) B)

extS-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (ren vs) (h x)
sub-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) → (t : Tm Γ) → sub σ t ≡ sub σ' t
sub-cong h (var x)   = h x
sub-cong h tt        = refl
sub-cong h ff        = refl
sub-cong h (lam t)   = cong lam (sub-cong (extS-cong h) t)
sub-cong h (app t u) = cong₂ app (sub-cong h t) (sub-cong h u)
subTy-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) → (A : Ty Γ) → subTy σ A ≡ subTy σ' A
subTy-cong h 𝔹        = refl
subTy-cong h ⊥̇        = refl
subTy-cong h (𝕀 t A B) = cong₃ 𝕀 (sub-cong h t) (subTy-cong h A) (subTy-cong h B)
subTy-cong h (Π̇ A B)  = cong₂ Π̇ (subTy-cong h A) (subTy-cong (extS-cong h) B)

extr-extr : ∀ {Γ Δ Θ} (ρ' : Ren Δ Θ)(ρ : Ren Γ Δ)(x : Var (Γ ∙)) → (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz = refl
extr-extr ρ' ρ (vs x) = refl
ren-ren : ∀ {Γ Δ Θ}{ρ' : Ren Δ Θ}{ρ : Ren Γ Δ}(t : Tm Γ) → ren ρ' (ren ρ t) ≡ ren (ρ' ∘ᵣ ρ) t
ren-ren (var x) = refl
ren-ren tt = refl
ren-ren ff = refl
ren-ren {ρ' = ρ'}{ρ}(lam t) = cong lam (trans (ren-ren t) (ren-cong (extr-extr ρ' ρ) t))
ren-ren (app t u) = cong₂ app (ren-ren t) (ren-ren u)
renTy-renTy : ∀ {Γ Δ Θ}{ρ' : Ren Δ Θ}{ρ : Ren Γ Δ}(A : Ty Γ) → renTy ρ' (renTy ρ A) ≡ renTy (ρ' ∘ᵣ ρ) A
renTy-renTy 𝔹 = refl
renTy-renTy ⊥̇ = refl
renTy-renTy (𝕀 t A B) = cong₃ 𝕀 (ren-ren t) (renTy-renTy A) (renTy-renTy B)
renTy-renTy {ρ' = ρ'}{ρ}(Π̇ A B) = cong₂ Π̇ (renTy-renTy A) (trans (renTy-renTy B) (renTy-cong (extr-extr ρ' ρ) B))

exts-extr : ∀ {Γ Δ Θ}(σ : Sub Δ Θ)(ρ : Ren Γ Δ)(x : Var (Γ ∙)) → (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz = refl
exts-extr σ ρ (vs x) = refl
sub-ren : ∀ {Γ Δ Θ}{σ : Sub Δ Θ}{ρ : Ren Γ Δ}(t : Tm Γ) → sub σ (ren ρ t) ≡ sub (σ ₛ∘ᵣ ρ) t
sub-ren (var x) = refl
sub-ren tt = refl
sub-ren ff = refl
sub-ren {σ = σ}{ρ}(lam t) = cong lam (trans (sub-ren t) (sub-cong (exts-extr σ ρ) t))
sub-ren (app t u) = cong₂ app (sub-ren t) (sub-ren u)
subTy-renTy : ∀ {Γ Δ Θ}{σ : Sub Δ Θ}{ρ : Ren Γ Δ}(A : Ty Γ) → subTy σ (renTy ρ A) ≡ subTy (σ ₛ∘ᵣ ρ) A
subTy-renTy 𝔹 = refl
subTy-renTy ⊥̇ = refl
subTy-renTy (𝕀 t A B) = cong₃ 𝕀 (sub-ren t) (subTy-renTy A) (subTy-renTy B)
subTy-renTy {σ = σ}{ρ}(Π̇ A B) = cong₂ Π̇ (subTy-renTy A) (trans (subTy-renTy B) (subTy-cong (exts-extr σ ρ) B))

extr-exts : ∀ {Γ Δ Θ}(ρ : Ren Δ Θ)(σ : Sub Γ Δ)(x : Var (Γ ∙)) → (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz = refl
extr-exts ρ σ (vs x) = trans (ren-ren (σ x)) (sym (ren-ren (σ x)))
ren-sub : ∀ {Γ Δ Θ}{ρ : Ren Δ Θ}{σ : Sub Γ Δ}(t : Tm Γ) → ren ρ (sub σ t) ≡ sub (ρ ᵣ∘ₛ σ) t
ren-sub (var x) = refl
ren-sub tt = refl
ren-sub ff = refl
ren-sub {ρ = ρ}{σ}(lam t) = cong lam (trans (ren-sub t) (sub-cong (extr-exts ρ σ) t))
ren-sub (app t u) = cong₂ app (ren-sub t) (ren-sub u)
renTy-subTy : ∀ {Γ Δ Θ}{ρ : Ren Δ Θ}{σ : Sub Γ Δ}(A : Ty Γ) → renTy ρ (subTy σ A) ≡ subTy (ρ ᵣ∘ₛ σ) A
renTy-subTy 𝔹 = refl
renTy-subTy ⊥̇ = refl
renTy-subTy (𝕀 t A B) = cong₃ 𝕀 (ren-sub t) (renTy-subTy A) (renTy-subTy B)
renTy-subTy {ρ = ρ}{σ}(Π̇ A B) = cong₂ Π̇ (renTy-subTy A) (trans (renTy-subTy B) (subTy-cong (extr-exts ρ σ) B))

exts-exts : ∀ {Γ Δ Θ}(τ : Sub Δ Θ)(σ : Sub Γ Δ)(x : Var (Γ ∙)) → (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz = refl
exts-exts τ σ (vs x) = trans (sub-ren (σ x)) (sym (ren-sub (σ x)))
sub-sub : ∀ {Γ Δ Θ}{τ : Sub Δ Θ}{σ : Sub Γ Δ}(t : Tm Γ) → sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
sub-sub (var x) = refl
sub-sub tt = refl
sub-sub ff = refl
sub-sub {τ = τ}{σ}(lam t) = cong lam (trans (sub-sub t) (sub-cong (exts-exts τ σ) t))
sub-sub (app t u) = cong₂ app (sub-sub t) (sub-sub u)
subTy-subTy : ∀ {Γ Δ Θ}{τ : Sub Δ Θ}{σ : Sub Γ Δ}(A : Ty Γ) → subTy τ (subTy σ A) ≡ subTy (τ ∘ₛ σ) A
subTy-subTy 𝔹 = refl
subTy-subTy ⊥̇ = refl
subTy-subTy (𝕀 t A B) = cong₃ 𝕀 (sub-sub t) (subTy-subTy A) (subTy-subTy B)
subTy-subTy {τ = τ}{σ}(Π̇ A B) = cong₂ Π̇ (subTy-subTy A) (trans (subTy-subTy B) (subTy-cong (exts-exts τ σ) B))

exts-id : ∀ {Γ}(x : Var (Γ ∙)) → extS ids x ≡ ids x
exts-id vz = refl
exts-id (vs x) = refl
sub-id : ∀ {Γ}(t : Tm Γ) → sub ids t ≡ t
sub-id (var x) = refl
sub-id tt = refl
sub-id ff = refl
sub-id (lam t) = cong lam (trans (sub-cong exts-id t) (sub-id t))
sub-id (app t u) = cong₂ app (sub-id t) (sub-id u)
subTy-id : ∀ {Γ}(A : Ty Γ) → subTy ids A ≡ A
subTy-id 𝔹 = refl
subTy-id ⊥̇ = refl
subTy-id (𝕀 t A B) = cong₃ 𝕀 (sub-id t) (subTy-id A) (subTy-id B)
subTy-id (Π̇ A B) = cong₂ Π̇ (subTy-id A) (trans (subTy-cong exts-id B) (subTy-id B))


------------------------------------------------------------------------
-- Typed contexts and the GENUINELY DEPENDENT typing relation (the type-level
-- `𝕀` makes `Π̇ A (𝕀 (var vz) B C)` a real dependent function type, and `⊢app`'s
-- result `subTy (single u) B` is NON-vacuous).
------------------------------------------------------------------------

data Con : Cx → Set where
  ε   : Con ε
  _▷_ : ∀ {Γ} → Con Γ → Ty Γ → Con (Γ ∙)

data _∋_∷_ : ∀ {Γ} → Con Γ → Var Γ → Ty Γ → Set where
  vz : ∀ {Γ}{Δ : Con Γ}{A}   → (Δ ▷ A) ∋ vz ∷ renTy vs A
  vs : ∀ {Γ}{Δ : Con Γ}{A B}{x} → Δ ∋ x ∷ A → (Δ ▷ B) ∋ vs x ∷ renTy vs A

data _⊢_∷_ : ∀ {Γ} → Con Γ → Tm Γ → Ty Γ → Set where
  ⊢var : ∀ {Γ}{Δ : Con Γ}{x A} → Δ ∋ x ∷ A → Δ ⊢ var x ∷ A
  ⊢tt  : ∀ {Γ}{Δ : Con Γ}      → Δ ⊢ tt ∷ 𝔹
  ⊢ff  : ∀ {Γ}{Δ : Con Γ}      → Δ ⊢ ff ∷ 𝔹
  ⊢lam : ∀ {Γ}{Δ : Con Γ}{A B}{t} → (Δ ▷ A) ⊢ t ∷ B → Δ ⊢ lam t ∷ Π̇ A B
  ⊢app : ∀ {Γ}{Δ : Con Γ}{A B}{f u} →
         Δ ⊢ f ∷ Π̇ A B → Δ ⊢ u ∷ A → Δ ⊢ app f u ∷ subTy (single u) B

-- a concrete genuinely-dependent type: (b : 𝔹) → (if b then 𝔹 else (𝔹 → 𝔹))
dep-example : Ty ε
dep-example = Π̇ 𝔹 (𝕀 (var vz) 𝔹 (Π̇ 𝔹 𝔹))

------------------------------------------------------------------------
-- SYNTACTIC METATHEORY for the genuinely-dependent calculus:
--   renaming and substitution PRESERVE TYPING.  These are the syntactic lemmas
--   the set-model soundness rests on; `--safe`, zero axioms.
------------------------------------------------------------------------

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

-- weakening commutes with renaming under a binder.
renTy-wk : ∀ {Γ Δ} {ρ : Ren Γ Δ} (A : Ty Γ) →
           renTy (extR ρ) (renTy vs A) ≡ renTy vs (renTy ρ A)
renTy-wk {ρ = ρ} A =
  trans (renTy-renTy A) (trans (renTy-cong (λ _ → refl) A) (sym (renTy-renTy A)))

-- renaming commutes with a single substitution (type level).
renTy-comm : ∀ {Γ Δ} (ρ : Ren Γ Δ) (u : Tm Γ) (B : Ty (Γ ∙)) →
             renTy ρ (subTy (single u) B) ≡ subTy (single (ren ρ u)) (renTy (extR ρ) B)
renTy-comm ρ u B =
  trans (renTy-subTy B) (trans (subTy-cong bridge B) (sym (subTy-renTy B)))
  where
  bridge : ∀ (x : Var (_ ∙)) → (ρ ᵣ∘ₛ single u) x ≡ (single (ren ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

_⊢ᵣ_∷_ : ∀ {Γ Δ} → Con Δ → Ren Γ Δ → Con Γ → Set
Θ ⊢ᵣ ρ ∷ Γ = ∀ {x A} → Γ ∋ x ∷ A → Θ ∋ ρ x ∷ renTy ρ A

⊢ᵣ-ext : ∀ {Γ Δ} {Θ : Con Δ} {Γc : Con Γ} {ρ : Ren Γ Δ} {A : Ty Γ} →
         Θ ⊢ᵣ ρ ∷ Γc → (Θ ▷ renTy ρ A) ⊢ᵣ extR ρ ∷ (Γc ▷ A)
⊢ᵣ-ext {Θ = Θ} {ρ = ρ} rρ (vz {A = A₀}) =
  subst (λ z → (Θ ▷ renTy ρ A₀) ∋ vz ∷ z) (sym (renTy-wk {ρ = ρ} A₀)) vz
⊢ᵣ-ext {Θ = Θ} {ρ = ρ} {A = A} rρ (vs {A = A₀} x) =
  subst (λ z → (Θ ▷ renTy ρ A) ∋ _ ∷ z) (sym (renTy-wk {ρ = ρ} A₀)) (vs (rρ x))

-- ★ RENAMING PRESERVES TYPING (genuinely-dependent calculus).
ren-⊢ : ∀ {Γ Δ} {Γc : Con Γ} {Θ : Con Δ} {t A} {ρ : Ren Γ Δ} →
        Γc ⊢ t ∷ A → Θ ⊢ᵣ ρ ∷ Γc → Θ ⊢ ren ρ t ∷ renTy ρ A
ren-⊢ (⊢var x)  rρ = ⊢var (rρ x)
ren-⊢ ⊢tt       rρ = ⊢tt
ren-⊢ ⊢ff       rρ = ⊢ff
ren-⊢ (⊢lam td) rρ = ⊢lam (ren-⊢ td (⊢ᵣ-ext rρ))
ren-⊢ {ρ = ρ} (⊢app {B = B} {f = f} {u = u} tf tu) rρ =
  subst (λ z → _ ⊢ app (ren ρ f) (ren ρ u) ∷ z) (sym (renTy-comm ρ u B))
        (⊢app (ren-⊢ tf rρ) (ren-⊢ tu rρ))

-- substitution weakening commute (dual of renTy-wk).
subTy-wk : ∀ {Γ Δ} {σ : Sub Γ Δ} (A : Ty Γ) →
           subTy (extS σ) (renTy vs A) ≡ renTy vs (subTy σ A)
subTy-wk {σ = σ} A =
  trans (subTy-renTy A) (trans (subTy-cong (λ _ → refl) A) (sym (renTy-subTy A)))

subTy-comm : ∀ {Γ Δ} (σ : Sub Γ Δ) (u : Tm Γ) (B : Ty (Γ ∙)) →
             subTy σ (subTy (single u) B) ≡ subTy (single (sub σ u)) (subTy (extS σ) B)
subTy-comm σ u B =
  trans (subTy-subTy B) (trans (subTy-cong bridge B) (sym (subTy-subTy B)))
  where
  bridge : ∀ (x : Var (_ ∙)) → (σ ∘ₛ single u) x ≡ (single (sub σ u) ∘ₛ extS σ) x
  bridge vz     = refl
  bridge (vs x) = trans (sym (sub-id (σ x))) (sym (sub-ren (σ x)))

wk-⊢ᵣ : ∀ {Γ} {Θ : Con Γ} {B : Ty Γ} → (Θ ▷ B) ⊢ᵣ vs ∷ Θ
wk-⊢ᵣ x = vs x

_⊢ₛ_∷_ : ∀ {Γ Δ} → Con Δ → Sub Γ Δ → Con Γ → Set
Θ ⊢ₛ σ ∷ Γ = ∀ {x A} → Γ ∋ x ∷ A → Θ ⊢ σ x ∷ subTy σ A

⊢ₛ-ext : ∀ {Γ Δ} {Θ : Con Δ} {Γc : Con Γ} {σ : Sub Γ Δ} {A : Ty Γ} →
         Θ ⊢ₛ σ ∷ Γc → (Θ ▷ subTy σ A) ⊢ₛ extS σ ∷ (Γc ▷ A)
⊢ₛ-ext {Θ = Θ} {σ = σ} sσ (vz {A = A₀}) =
  subst (λ z → (Θ ▷ subTy σ A₀) ⊢ var vz ∷ z) (sym (subTy-wk {σ = σ} A₀)) (⊢var vz)
⊢ₛ-ext {Θ = Θ} {σ = σ} {A = A} sσ (vs {A = A₀} x) =
  subst (λ z → (Θ ▷ subTy σ A) ⊢ _ ∷ z) (sym (subTy-wk {σ = σ} A₀))
        (ren-⊢ (sσ x) wk-⊢ᵣ)

-- ★ SUBSTITUTION PRESERVES TYPING (genuinely-dependent calculus).
sub-⊢ : ∀ {Γ Δ} {Γc : Con Γ} {Θ : Con Δ} {t A} {σ : Sub Γ Δ} →
        Γc ⊢ t ∷ A → Θ ⊢ₛ σ ∷ Γc → Θ ⊢ sub σ t ∷ subTy σ A
sub-⊢ (⊢var x)  sσ = sσ x
sub-⊢ ⊢tt       sσ = ⊢tt
sub-⊢ ⊢ff       sσ = ⊢ff
sub-⊢ (⊢lam td) sσ = ⊢lam (sub-⊢ td (⊢ₛ-ext sσ))
sub-⊢ {σ = σ} (⊢app {B = B} {f = f} {u = u} tf tu) sσ =
  subst (λ z → _ ⊢ app (sub σ f) (sub σ u) ∷ z) (sym (subTy-comm σ u B))
        (⊢app (sub-⊢ tf sσ) (sub-⊢ tu sσ))
