------------------------------------------------------------------------
-- OCP-0009 · dHoTT step 43d — RAW-FAITHFUL DEPENDENT SOUNDNESS (M3c), the grind.
--   A CHURCH-STYLE genuinely-dependent calculus (domain-annotated `lam`, so
--   typing is UNIQUE) → its set model `⟦_⟧` → CONSISTENCY.  `--safe`.
--
-- Church-style is what raw M3c needs: with Curry `lam` the SAME term inhabits many
-- types (machine-checked in NbEPDirDTT), so the interpretation cannot be shown
-- independent of the typing derivation.  Annotating `lam` with its domain makes
-- typing unique → derivation-unique → the interpretation derivation-irrelevant.
--
-- Stages here (all `--safe`, zero axioms/postulates/holes):
--   1. syntax (mutual `Tm`/`Ty`, domain-annotated `lam`) + substitution + the
--      full fusion algebra;
--   2. typed contexts, well-formedness `_⊨_`, typing `_⊢_∷_` with FUNCTIONAL
--      variable lookup `lkTy` (no `∋` relation — its `renTy vs` index otherwise
--      stalls uniqueness unification);
--   4. ★ DERIVATION-UNIQUENESS: `⊢≡` (heterogeneous, so two `⊢app` match without
--      non-injective unification) ⇒ `⊢-unique` and `⊨-unique` (K/UIP-based).
-- The interpretation (`⟦_⟧` + semantic weakening/substitution lemmas → CONSISTENCY)
-- builds on this base and lands in a companion module.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPDirDTTCh where

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
-- Scopes, variables, and the mutually-defined terms and (term-dependent) types.
-- `lam` carries its domain type (Church-style).
------------------------------------------------------------------------

data Cx : Set where
  ε   : Cx
  _∙  : Cx → Cx

data Var : Cx → Set where
  vz : ∀ {Γ}   → Var (Γ ∙)
  vs : ∀ {Γ}   → Var Γ → Var (Γ ∙)

data Tm : Cx → Set
data Ty : Cx → Set

data Tm where
  var   : ∀ {Γ} → Var Γ → Tm Γ
  tt ff : ∀ {Γ} → Tm Γ
  lam   : ∀ {Γ} → Ty Γ → Tm (Γ ∙) → Tm Γ        -- domain-ANNOTATED
  app   : ∀ {Γ} → Tm Γ → Tm Γ → Tm Γ

data Ty where
  𝔹  : ∀ {Γ} → Ty Γ
  ⊥̇  : ∀ {Γ} → Ty Γ
  𝕀  : ∀ {Γ} → Tm Γ → Ty Γ → Ty Γ → Ty Γ
  Π̇  : ∀ {Γ} → Ty Γ → Ty (Γ ∙) → Ty Γ

------------------------------------------------------------------------
-- Renaming and substitution.
------------------------------------------------------------------------

Ren : Cx → Cx → Set
Ren Γ Δ = Var Γ → Var Δ

extR : ∀ {Γ Δ} → Ren Γ Δ → Ren (Γ ∙) (Δ ∙)
extR ρ vz     = vz
extR ρ (vs x) = vs (ρ x)

ren   : ∀ {Γ Δ} → Ren Γ Δ → Tm Γ → Tm Δ
renTy : ∀ {Γ Δ} → Ren Γ Δ → Ty Γ → Ty Δ
ren ρ (var x)   = var (ρ x)
ren ρ tt        = tt
ren ρ ff        = ff
ren ρ (lam A t) = lam (renTy ρ A) (ren (extR ρ) t)
ren ρ (app t u) = app (ren ρ t) (ren ρ u)
renTy ρ 𝔹        = 𝔹
renTy ρ ⊥̇        = ⊥̇
renTy ρ (𝕀 t A B) = 𝕀 (ren ρ t) (renTy ρ A) (renTy ρ B)
renTy ρ (Π̇ A B)  = Π̇ (renTy ρ A) (renTy (extR ρ) B)

Sub : Cx → Cx → Set
Sub Γ Δ = Var Γ → Tm Δ

extS : ∀ {Γ Δ} → Sub Γ Δ → Sub (Γ ∙) (Δ ∙)
extS σ vz     = var vz
extS σ (vs x) = ren vs (σ x)

sub   : ∀ {Γ Δ} → Sub Γ Δ → Tm Γ → Tm Δ
subTy : ∀ {Γ Δ} → Sub Γ Δ → Ty Γ → Ty Δ
sub σ (var x)   = σ x
sub σ tt        = tt
sub σ ff        = ff
sub σ (lam A t) = lam (subTy σ A) (sub (extS σ) t)
sub σ (app t u) = app (sub σ t) (sub σ u)
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
-- Composition operators + the fusion algebra (terms and types).
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
ren-cong   : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) → (t : Tm Γ) → ren ρ t ≡ ren ρ' t
renTy-cong : ∀ {Γ Δ} {ρ ρ' : Ren Γ Δ} → (∀ x → ρ x ≡ ρ' x) → (A : Ty Γ) → renTy ρ A ≡ renTy ρ' A
ren-cong h (var x)   = cong var (h x)
ren-cong h tt        = refl
ren-cong h ff        = refl
ren-cong h (lam A t) = cong₂ lam (renTy-cong h A) (ren-cong (extR-cong h) t)
ren-cong h (app t u) = cong₂ app (ren-cong h t) (ren-cong h u)
renTy-cong h 𝔹        = refl
renTy-cong h ⊥̇        = refl
renTy-cong h (𝕀 t A B) = cong₃ 𝕀 (ren-cong h t) (renTy-cong h A) (renTy-cong h B)
renTy-cong h (Π̇ A B)  = cong₂ Π̇ (renTy-cong h A) (renTy-cong (extR-cong h) B)

extS-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) →
            ∀ (x : Var (Γ ∙)) → extS σ x ≡ extS σ' x
extS-cong h vz     = refl
extS-cong h (vs x) = cong (ren vs) (h x)
sub-cong   : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) → (t : Tm Γ) → sub σ t ≡ sub σ' t
subTy-cong : ∀ {Γ Δ} {σ σ' : Sub Γ Δ} → (∀ x → σ x ≡ σ' x) → (A : Ty Γ) → subTy σ A ≡ subTy σ' A
sub-cong h (var x)   = h x
sub-cong h tt        = refl
sub-cong h ff        = refl
sub-cong h (lam A t) = cong₂ lam (subTy-cong h A) (sub-cong (extS-cong h) t)
sub-cong h (app t u) = cong₂ app (sub-cong h t) (sub-cong h u)
subTy-cong h 𝔹        = refl
subTy-cong h ⊥̇        = refl
subTy-cong h (𝕀 t A B) = cong₃ 𝕀 (sub-cong h t) (subTy-cong h A) (subTy-cong h B)
subTy-cong h (Π̇ A B)  = cong₂ Π̇ (subTy-cong h A) (subTy-cong (extS-cong h) B)

extr-extr : ∀ {Γ Δ Θ} (ρ' : Ren Δ Θ)(ρ : Ren Γ Δ)(x : Var (Γ ∙)) → (extR ρ' ∘ᵣ extR ρ) x ≡ extR (ρ' ∘ᵣ ρ) x
extr-extr ρ' ρ vz = refl
extr-extr ρ' ρ (vs x) = refl
ren-ren   : ∀ {Γ Δ Θ}{ρ' : Ren Δ Θ}{ρ : Ren Γ Δ}(t : Tm Γ) → ren ρ' (ren ρ t) ≡ ren (ρ' ∘ᵣ ρ) t
renTy-renTy : ∀ {Γ Δ Θ}{ρ' : Ren Δ Θ}{ρ : Ren Γ Δ}(A : Ty Γ) → renTy ρ' (renTy ρ A) ≡ renTy (ρ' ∘ᵣ ρ) A
ren-ren (var x) = refl
ren-ren tt = refl
ren-ren ff = refl
ren-ren {ρ' = ρ'}{ρ}(lam A t) = cong₂ lam (renTy-renTy A) (trans (ren-ren t) (ren-cong (extr-extr ρ' ρ) t))
ren-ren (app t u) = cong₂ app (ren-ren t) (ren-ren u)
renTy-renTy 𝔹 = refl
renTy-renTy ⊥̇ = refl
renTy-renTy (𝕀 t A B) = cong₃ 𝕀 (ren-ren t) (renTy-renTy A) (renTy-renTy B)
renTy-renTy {ρ' = ρ'}{ρ}(Π̇ A B) = cong₂ Π̇ (renTy-renTy A) (trans (renTy-renTy B) (renTy-cong (extr-extr ρ' ρ) B))

exts-extr : ∀ {Γ Δ Θ}(σ : Sub Δ Θ)(ρ : Ren Γ Δ)(x : Var (Γ ∙)) → (extS σ ₛ∘ᵣ extR ρ) x ≡ extS (σ ₛ∘ᵣ ρ) x
exts-extr σ ρ vz = refl
exts-extr σ ρ (vs x) = refl
sub-ren   : ∀ {Γ Δ Θ}{σ : Sub Δ Θ}{ρ : Ren Γ Δ}(t : Tm Γ) → sub σ (ren ρ t) ≡ sub (σ ₛ∘ᵣ ρ) t
subTy-renTy : ∀ {Γ Δ Θ}{σ : Sub Δ Θ}{ρ : Ren Γ Δ}(A : Ty Γ) → subTy σ (renTy ρ A) ≡ subTy (σ ₛ∘ᵣ ρ) A
sub-ren (var x) = refl
sub-ren tt = refl
sub-ren ff = refl
sub-ren {σ = σ}{ρ}(lam A t) = cong₂ lam (subTy-renTy A) (trans (sub-ren t) (sub-cong (exts-extr σ ρ) t))
sub-ren (app t u) = cong₂ app (sub-ren t) (sub-ren u)
subTy-renTy 𝔹 = refl
subTy-renTy ⊥̇ = refl
subTy-renTy (𝕀 t A B) = cong₃ 𝕀 (sub-ren t) (subTy-renTy A) (subTy-renTy B)
subTy-renTy {σ = σ}{ρ}(Π̇ A B) = cong₂ Π̇ (subTy-renTy A) (trans (subTy-renTy B) (subTy-cong (exts-extr σ ρ) B))

extr-exts : ∀ {Γ Δ Θ}(ρ : Ren Δ Θ)(σ : Sub Γ Δ)(x : Var (Γ ∙)) → (extR ρ ᵣ∘ₛ extS σ) x ≡ extS (ρ ᵣ∘ₛ σ) x
extr-exts ρ σ vz = refl
extr-exts ρ σ (vs x) = trans (ren-ren (σ x)) (sym (ren-ren (σ x)))
ren-sub   : ∀ {Γ Δ Θ}{ρ : Ren Δ Θ}{σ : Sub Γ Δ}(t : Tm Γ) → ren ρ (sub σ t) ≡ sub (ρ ᵣ∘ₛ σ) t
renTy-subTy : ∀ {Γ Δ Θ}{ρ : Ren Δ Θ}{σ : Sub Γ Δ}(A : Ty Γ) → renTy ρ (subTy σ A) ≡ subTy (ρ ᵣ∘ₛ σ) A
ren-sub (var x) = refl
ren-sub tt = refl
ren-sub ff = refl
ren-sub {ρ = ρ}{σ}(lam A t) = cong₂ lam (renTy-subTy A) (trans (ren-sub t) (sub-cong (extr-exts ρ σ) t))
ren-sub (app t u) = cong₂ app (ren-sub t) (ren-sub u)
renTy-subTy 𝔹 = refl
renTy-subTy ⊥̇ = refl
renTy-subTy (𝕀 t A B) = cong₃ 𝕀 (ren-sub t) (renTy-subTy A) (renTy-subTy B)
renTy-subTy {ρ = ρ}{σ}(Π̇ A B) = cong₂ Π̇ (renTy-subTy A) (trans (renTy-subTy B) (subTy-cong (extr-exts ρ σ) B))

exts-exts : ∀ {Γ Δ Θ}(τ : Sub Δ Θ)(σ : Sub Γ Δ)(x : Var (Γ ∙)) → (extS τ ∘ₛ extS σ) x ≡ extS (τ ∘ₛ σ) x
exts-exts τ σ vz = refl
exts-exts τ σ (vs x) = trans (sub-ren (σ x)) (sym (ren-sub (σ x)))
sub-sub   : ∀ {Γ Δ Θ}{τ : Sub Δ Θ}{σ : Sub Γ Δ}(t : Tm Γ) → sub τ (sub σ t) ≡ sub (τ ∘ₛ σ) t
subTy-subTy : ∀ {Γ Δ Θ}{τ : Sub Δ Θ}{σ : Sub Γ Δ}(A : Ty Γ) → subTy τ (subTy σ A) ≡ subTy (τ ∘ₛ σ) A
sub-sub (var x) = refl
sub-sub tt = refl
sub-sub ff = refl
sub-sub {τ = τ}{σ}(lam A t) = cong₂ lam (subTy-subTy A) (trans (sub-sub t) (sub-cong (exts-exts τ σ) t))
sub-sub (app t u) = cong₂ app (sub-sub t) (sub-sub u)
subTy-subTy 𝔹 = refl
subTy-subTy ⊥̇ = refl
subTy-subTy (𝕀 t A B) = cong₃ 𝕀 (sub-sub t) (subTy-subTy A) (subTy-subTy B)
subTy-subTy {τ = τ}{σ}(Π̇ A B) = cong₂ Π̇ (subTy-subTy A) (trans (subTy-subTy B) (subTy-cong (exts-exts τ σ) B))

exts-id : ∀ {Γ}(x : Var (Γ ∙)) → extS ids x ≡ ids x
exts-id vz = refl
exts-id (vs x) = refl
sub-id   : ∀ {Γ}(t : Tm Γ) → sub ids t ≡ t
subTy-id : ∀ {Γ}(A : Ty Γ) → subTy ids A ≡ A
sub-id (var x) = refl
sub-id tt = refl
sub-id ff = refl
sub-id (lam A t) = cong₂ lam (subTy-id A) (trans (sub-cong exts-id t) (sub-id t))
sub-id (app t u) = cong₂ app (sub-id t) (sub-id u)
subTy-id 𝔹 = refl
subTy-id ⊥̇ = refl
subTy-id (𝕀 t A B) = cong₃ 𝕀 (sub-id t) (subTy-id A) (subTy-id B)
subTy-id (Π̇ A B) = cong₂ Π̇ (subTy-id A) (trans (subTy-cong exts-id B) (subTy-id B))


------------------------------------------------------------------------
-- Stage 2 — typed contexts + well-formedness + typing, with FUNCTIONAL variable
-- lookup (`lkTy`), so the variable rule carries no `∋` derivation to be unique
-- about (the `renTy vs` index that stalls `∋`-uniqueness never appears).
------------------------------------------------------------------------

data Con : Cx → Set
data _⊨_ : ∀ {Γ} → Con Γ → Ty Γ → Set
lkTy : ∀ {Γ} → Con Γ → Var Γ → Ty Γ
data _⊢_∷_ : ∀ {Γ} → Con Γ → Tm Γ → Ty Γ → Set

infixl 5 _▷_
data Con where
  ε   : Con ε
  _▷_ : ∀ {Γ}(Δ : Con Γ){A} → Δ ⊨ A → Con (Γ ∙)

lkTy (_▷_ Δ {A} wA) vz     = renTy vs A
lkTy (Δ ▷ wB)       (vs x) = renTy vs (lkTy Δ x)

data _⊨_ where
  ⊨𝔹 : ∀ {Γ}{Δ : Con Γ}         → Δ ⊨ 𝔹
  ⊨⊥ : ∀ {Γ}{Δ : Con Γ}         → Δ ⊨ ⊥̇
  ⊨𝕀 : ∀ {Γ}{Δ : Con Γ}{t A B}  → Δ ⊢ t ∷ 𝔹 → Δ ⊨ A → Δ ⊨ B → Δ ⊨ 𝕀 t A B
  ⊨Π : ∀ {Γ}{Δ : Con Γ}{A B}    → (wA : Δ ⊨ A) → (Δ ▷ wA) ⊨ B → Δ ⊨ Π̇ A B

data _⊢_∷_ where
  ⊢var : ∀ {Γ}{Δ : Con Γ}(x : Var Γ) → Δ ⊢ var x ∷ lkTy Δ x
  ⊢tt  : ∀ {Γ}{Δ : Con Γ}      → Δ ⊢ tt ∷ 𝔹
  ⊢ff  : ∀ {Γ}{Δ : Con Γ}      → Δ ⊢ ff ∷ 𝔹
  ⊢lam : ∀ {Γ}{Δ : Con Γ}{A B}{t} → (wA : Δ ⊨ A) → (Δ ▷ wA) ⊢ t ∷ B →
         Δ ⊢ lam A t ∷ Π̇ A B
  ⊢app : ∀ {Γ}{Δ : Con Γ}{A B}{f u} →
         (wA : Δ ⊨ A) → (Δ ▷ wA) ⊨ B →
         Δ ⊢ f ∷ Π̇ A B → Δ ⊢ u ∷ A → Δ ⊢ app f u ∷ subTy (single u) B


------------------------------------------------------------------------
-- Stage 4 — DERIVATION-UNIQUENESS.  `⊢≡` is HETEROGENEOUS (the two result types
-- are independent, so matching two `⊢app` needs no non-injective unification);
-- `with … | refl` collapses the transports (K/UIP, `--safe`-compatible).
------------------------------------------------------------------------

open import Agda.Builtin.Sigma using ( Σ; _,_; fst; snd )

subst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → x ≡ y → P x → P y
subst P refl px = px

uip : ∀ {a} {A : Set a} {x : A} (p : x ≡ x) → p ≡ refl
uip refl = refl

Π̇-injˡ : ∀ {Γ}{A A' : Ty Γ}{B B' : Ty (Γ ∙)} → Π̇ A B ≡ Π̇ A' B' → A ≡ A'
Π̇-injˡ refl = refl
Π̇-injʳ : ∀ {Γ}{A A' : Ty Γ}{B B' : Ty (Γ ∙)} → Π̇ A B ≡ Π̇ A' B' → B ≡ B'
Π̇-injʳ refl = refl

⊢≡      : ∀ {Γ}{Δ : Con Γ}{t A A'} (td : Δ ⊢ t ∷ A)(td' : Δ ⊢ t ∷ A') →
          Σ (A ≡ A') (λ p → subst (λ z → Δ ⊢ t ∷ z) p td ≡ td')
⊨-unique : ∀ {Γ}{Δ : Con Γ}{A} (w w' : Δ ⊨ A) → w ≡ w'
⊢-unique : ∀ {Γ}{Δ : Con Γ}{t A} (td td' : Δ ⊢ t ∷ A) → td ≡ td'

⊢-unique td td' with ⊢≡ td td'
... | p , q rewrite uip p = q

⊨-unique ⊨𝔹 ⊨𝔹 = refl
⊨-unique ⊨⊥ ⊨⊥ = refl
⊨-unique (⊨𝕀 tb wA wB) (⊨𝕀 tb' wA' wB') =
  cong₃ ⊨𝕀 (⊢-unique tb tb') (⊨-unique wA wA') (⊨-unique wB wB')
⊨-unique (⊨Π wA wB) (⊨Π wA' wB') with ⊨-unique wA wA'
... | refl = cong (⊨Π wA) (⊨-unique wB wB')

⊢≡ (⊢var x) (⊢var x) = refl , refl
⊢≡ ⊢tt ⊢tt = refl , refl
⊢≡ ⊢ff ⊢ff = refl , refl
⊢≡ (⊢lam wA td) (⊢lam wA' td') with ⊨-unique wA wA'
... | refl with ⊢≡ td td'
...   | refl , refl = refl , refl
⊢≡ (⊢app wA wB tf tu) (⊢app wA' wB' tf' tu') with ⊢≡ tf tf'
... | refl , refl with ⊨-unique wA wA'
...   | refl with ⊨-unique wB wB' | ⊢≡ tu tu'
...     | refl | refl , refl = refl , refl

------------------------------------------------------------------------
-- Stage 5 — RENAMING METATHEORY along order-preserving embeddings (OPEs): the
-- syntactic naturality the semantic weakening lemma rests on.
------------------------------------------------------------------------

-- renaming commutes with a single substitution (needed in `ren⊢`'s app case).
renTy-comm : ∀ {Γ Δ} (ρ : Ren Γ Δ) (u : Tm Γ) (B : Ty (Γ ∙)) →
             renTy ρ (subTy (single u) B) ≡ subTy (single (ren ρ u)) (renTy (extR ρ) B)
renTy-comm ρ u B =
  trans (renTy-subTy B) (trans (subTy-cong bridge B) (sym (subTy-renTy B)))
  where
  bridge : ∀ (x : Var (_ ∙)) → (ρ ᵣ∘ₛ single u) x ≡ (single (ren ρ u) ₛ∘ᵣ extR ρ) x
  bridge vz     = refl
  bridge (vs x) = refl

renTy-wk : ∀ {Γ Δ} {ρ : Ren Γ Δ} (A : Ty Γ) →
           renTy (extR ρ) (renTy vs A) ≡ renTy vs (renTy ρ A)
renTy-wk {ρ = ρ} A =
  trans (renTy-renTy A) (trans (renTy-cong (λ _ → refl) A) (sym (renTy-renTy A)))

data OPE : Cx → Cx → Set where
  done : OPE ε ε
  keep : ∀ {Γ Δ} → OPE Γ Δ → OPE (Γ ∙) (Δ ∙)
  skip : ∀ {Γ Δ} → OPE Γ Δ → OPE Γ (Δ ∙)

⌜_⌝ : ∀ {Γ Δ} → OPE Γ Δ → Ren Γ Δ
⌜ done ⌝   ()
⌜ keep o ⌝ = extR ⌜ o ⌝
⌜ skip o ⌝ = λ x → vs (⌜ o ⌝ x)

data _⊑[_]_ : ∀ {Γ Δ} → Con Γ → OPE Γ Δ → Con Δ → Set
ren⊨ : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A} → Δc ⊨ A → Θc ⊨ renTy ⌜ o ⌝ A
ren⊢ : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){t A} → Δc ⊢ t ∷ A → Θc ⊢ ren ⌜ o ⌝ t ∷ renTy ⌜ o ⌝ A
lkcompat : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc)(x : Var Γ) →
           lkTy Θc (⌜ o ⌝ x) ≡ renTy ⌜ o ⌝ (lkTy Δc x)

data _⊑[_]_ where
  done : ε ⊑[ done ] ε
  keep : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){A}(wA : Δc ⊨ A) →
         (Δc ▷ wA) ⊑[ keep o ] (Θc ▷ ren⊨ r wA)
  skip : ∀ {Γ Δ}{Δc : Con Γ}{Θc : Con Δ}{o}(r : Δc ⊑[ o ] Θc){B}(wB : Θc ⊨ B) →
         Δc ⊑[ skip o ] (Θc ▷ wB)

ren⊨ r ⊨𝔹            = ⊨𝔹
ren⊨ r ⊨⊥            = ⊨⊥
ren⊨ r (⊨𝕀 tb wA wB) = ⊨𝕀 (ren⊢ r tb) (ren⊨ r wA) (ren⊨ r wB)
ren⊨ r (⊨Π wA wB)    = ⊨Π (ren⊨ r wA) (ren⊨ (keep r wA) wB)

ren⊢ {o = o} r (⊢var x) =
  subst (λ z → _ ⊢ var (⌜ o ⌝ x) ∷ z) (lkcompat r x) (⊢var (⌜ o ⌝ x))
ren⊢ r ⊢tt            = ⊢tt
ren⊢ r ⊢ff            = ⊢ff
ren⊢ r (⊢lam wA td)   = ⊢lam (ren⊨ r wA) (ren⊢ (keep r wA) td)
ren⊢ {o = o} r (⊢app {B = B} {u = u} wA wB tf tu) =
  subst (λ z → _ ⊢ app _ _ ∷ z) (sym (renTy-comm ⌜ o ⌝ u B))
        (⊢app (ren⊨ r wA) (ren⊨ (keep r wA) wB) (ren⊢ r tf) (ren⊢ r tu))

lkcompat (keep {o = o} r {A = A} wA) vz = sym (renTy-wk {ρ = ⌜ o ⌝} A)
lkcompat (keep {Δc = Δc} {o = o} r wA) (vs x) =
  trans (cong (renTy vs) (lkcompat r x)) (sym (renTy-wk {ρ = ⌜ o ⌝} (lkTy Δc x)))
lkcompat (skip {Δc = Δc} {o = o} r wB) x =
  trans (cong (renTy vs) (lkcompat r x)) (renTy-renTy {ρ' = vs} {ρ = ⌜ o ⌝} (lkTy Δc x))

-- the identity OPE, and the weakening OPE (drop the top variable).
idOPE : ∀ {Γ} → OPE Γ Γ
idOPE {ε}   = done
idOPE {Γ ∙} = keep idOPE

idOPE-id : ∀ {Γ}(x : Var Γ) → ⌜ idOPE ⌝ x ≡ x
idOPE-id vz     = refl
idOPE-id (vs x) = cong vs (idOPE-id x)

ren-idOPE   : ∀ {Γ}(t : Tm Γ) → ren ⌜ idOPE ⌝ t ≡ t
renTy-idOPE : ∀ {Γ}(A : Ty Γ) → renTy ⌜ idOPE ⌝ A ≡ A
ren-idOPE (var x)   = cong var (idOPE-id x)
ren-idOPE tt        = refl
ren-idOPE ff        = refl
ren-idOPE (lam A t) = cong₂ lam (renTy-idOPE A) (ren-idOPE t)
ren-idOPE (app t u) = cong₂ app (ren-idOPE t) (ren-idOPE u)
renTy-idOPE 𝔹        = refl
renTy-idOPE ⊥̇        = refl
renTy-idOPE (𝕀 t A B) = cong₃ 𝕀 (ren-idOPE t) (renTy-idOPE A) (renTy-idOPE B)
renTy-idOPE (Π̇ A B)  = cong₂ Π̇ (renTy-idOPE A) (renTy-idOPE B)

▷≡ : ∀ {Γ}{Δc : Con Γ}{A A'}(p : A ≡ A'){wA : Δc ⊨ A}{wA' : Δc ⊨ A'} →
     subst (Δc ⊨_) p wA ≡ wA' → (Δc ▷ wA) ≡ (Δc ▷ wA')
▷≡ {Δc = Δc} refl q = cong (Δc ▷_) q

id⊑ : ∀ {Γ}(Δc : Con Γ) → Δc ⊑[ idOPE ] Δc
id⊑ ε         = done
id⊑ (Δc ▷ wA) =
  subst (λ Θ → (Δc ▷ wA) ⊑[ keep idOPE ] Θ)
        (▷≡ (renTy-idOPE _) (⊨-unique _ wA)) (keep (id⊑ Δc) wA)

wk⊑ : ∀ {Γ}(Δc : Con Γ){C}(wC : Δc ⊨ C) → Δc ⊑[ skip idOPE ] (Δc ▷ wC)
wk⊑ Δc wC = skip (id⊑ Δc) wC
