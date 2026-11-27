-- SPDX-License-Identifier: AGPL-3.0-or-later
-- Copyright (C) 2025-2026 Jonas Claesson

------------------------------------------------------------------------
-- OCP-0009 · dHoTT — SCOPED SYNTAX WITH BINDING, GENERIC IN A SIGNATURE
--                    (SPIKE-GENERIC-SYNTAX, promoted from `POC/tmp/`).
--
-- A syntax is a BINDING SIGNATURE: sorts, the constructors of each sort, and
-- each constructor's fields — `fld s k` (a subterm of sort `s` under `k` new
-- binders) or `fnat` (a natural) — with variables at one sort. Categorically:
-- the initial algebra of the signature's functor on sorted, scoped families
-- (Fiore–Plotkin–Turi; Allais et al.'s "universe of syntaxes", the shape of
-- the Knot's object-level `Lib/Syn`).
--
-- Over it, ONCE for every signature:
--   * one traversal by a KIT (what a variable becomes, how a value survives a
--     binder); renaming and substitution are its two instances;
--   * congruence (pointwise-equal environments, funext-free) and FUSION (one
--     theorem; the four fusion lemmas of a hand-written syntax are its
--     corollaries, each proving only its one-binder case);
--   * the algebra of SYNTACTIC kits: fusion with renaming and substitution on
--     both sides, simulation (the traversal IS a substitution), one
--     commuting square, and weakening and single substitution through it.
--
-- ★ ENCODING (2026-11-27, measured by `POC/tmp/TermProbe*.agda`): a node
--   holds the PRODUCT `⟦ fields c ⟧ Γ`, computed from the field list, a
--   record with η whose constructors carry NO indices; and a field's scope is computed by matching
--   on its binder depth (0, 1, 2, then the general case), so a depth-k field
--   has the type `Tm s Γ`, `Tm s (Γ ∙)`, … syntactically. An argument list
--   indexed by the computed field list, or field types `Tm s (Γ ⋯ k)`, leave
--   dot patterns that Agda's termination checker cannot compare with a
--   REBUILT subterm, and recursion through `f (Π A B)` from a pattern
--   `Hom (Π A B) t u` stops terminating; this encoding keeps it.
--
-- `Spec/Syntax` instantiates this at the kernel's signature, ONCE (an instance
-- copy per use would defeat syntactic equality, PLAN-REF), and re-exports the
-- kernel-facing names. Import this module qualified.
--
-- `--safe`, ZERO axioms, no sized types, no funext.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Spec.Bind where
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Scope

------------------------------------------------------------------------
-- Binding signatures
------------------------------------------------------------------------

data Field (S : Set) : Set where
  fld  : S → ℕ → Field S
  fnat : Field S

record BSig : Set₁ where
  field
    Sort   : Set
    vsort  : Sort                       -- the sort variables live at
    Con    : Sort → Set
    fields : ∀ {s} → Con s → List (Field Sort)
open BSig public

-- `k` more binders
_⋯_ : Cx → ℕ → Cx
Γ ⋯ zero  = Γ
Γ ⋯ suc k = (Γ ⋯ k) ∙

------------------------------------------------------------------------
-- The syntax of a signature
------------------------------------------------------------------------

-- the fields' products: RECORDS with η and no indices. η matters: a
-- function defined on the formers (pattern synonyms) reduces on `node c xs`
-- for a variable `xs`, so a case it refutes by computation needs no clause,
-- as with the old constructors (data products left `xs` unsplit and the case
-- open: `POC/tmp/TermProbe8.agda`).
record ⟨⟩ᶠ : Set where
  constructor ⟨⟩

infixr 5 _⊗_ _,ᶠ_
record _⊗_ (A B : Set) : Set where
  constructor _,ᶠ_
  field
    fstᶠ : A
    sndᶠ : B

-- named, so a signature can be applied ONCE (`module KS = Syn KSig`): its
-- `node`/`var` then fix the signature, which pattern synonyms cannot name
module Syn (Σ : BSig) where
  data Tm : Sort Σ → Cx → Set
  ⟦_⟧ : List (Field (Sort Σ)) → Cx → Set

  data Tm where
    var  : ∀ {Γ} → Var Γ → Tm (vsort Σ) Γ
    node : ∀ {s Γ} (c : Con Σ s) → ⟦ fields Σ c ⟧ Γ → Tm s Γ

  ⟦ [] ⟧ Γ                              = ⟨⟩ᶠ
  ⟦ fld s zero ∷ fs ⟧ Γ                 = Tm s Γ ⊗ ⟦ fs ⟧ Γ
  ⟦ fld s (suc zero) ∷ fs ⟧ Γ           = Tm s (Γ ∙) ⊗ ⟦ fs ⟧ Γ
  ⟦ fld s (suc (suc zero)) ∷ fs ⟧ Γ     = Tm s ((Γ ∙) ∙) ⊗ ⟦ fs ⟧ Γ
  ⟦ fld s (suc (suc (suc k))) ∷ fs ⟧ Γ  = Tm s (Γ ⋯ suc (suc (suc k))) ⊗ ⟦ fs ⟧ Γ
  ⟦ fnat ∷ fs ⟧ Γ                       = ℕ ⊗ ⟦ fs ⟧ Γ

open Syn public

------------------------------------------------------------------------
-- Kits, the one traversal, and everything proved once
------------------------------------------------------------------------

module Trav (Σ : BSig) where
  T : Cx → Set
  T = Tm Σ (vsort Σ)

  private
    c₂ : ∀ {A B : Set} {a a′ : A} {b b′ : B} → a ≡ a′ → b ≡ b′ → _≡_ {A ⊗ B} (a ,ᶠ b) (a′ ,ᶠ b′)
    c₂ refl refl = refl

  record Kit : Set₁ where
    field
      V    : Cx → Set
      wkV  : ∀ {Γ} → V Γ → V (Γ ∙)
      v0   : ∀ {Γ} → V (Γ ∙)
      toTm : ∀ {Γ} → V Γ → T Γ

  module _ (K : Kit) where
    open Kit K
    Env : Cx → Cx → Set
    Env Γ Δ = Var Γ → V Δ

    ext : ∀ {Γ Δ} → Env Γ Δ → Env (Γ ∙) (Δ ∙)
    ext ρ vz     = v0
    ext ρ (vs x) = wkV (ρ x)

    extN : ∀ k {Γ Δ} → Env Γ Δ → Env (Γ ⋯ k) (Δ ⋯ k)
    extN zero    ρ = ρ
    extN (suc k) ρ = ext (extN k ρ)

    trav  : ∀ {s Γ Δ} → Env Γ Δ → Tm Σ s Γ → Tm Σ s Δ
    travF : ∀ fs {Γ Δ} → Env Γ Δ → ⟦_⟧ Σ fs Γ → ⟦_⟧ Σ fs Δ
    trav ρ (var x)     = toTm (ρ x)
    trav ρ (node c xs) = node c (travF (fields Σ c) ρ xs)
    travF []                                ρ ⟨⟩        = ⟨⟩
    travF (fld s zero ∷ fs)                 ρ (x ,ᶠ xs) = trav ρ x ,ᶠ travF fs ρ xs
    travF (fld s (suc zero) ∷ fs)           ρ (x ,ᶠ xs) = trav (ext ρ) x ,ᶠ travF fs ρ xs
    travF (fld s (suc (suc zero)) ∷ fs)     ρ (x ,ᶠ xs) = trav (ext (ext ρ)) x ,ᶠ travF fs ρ xs
    travF (fld s (suc (suc (suc k))) ∷ fs)  ρ (x ,ᶠ xs) = trav (extN (suc (suc (suc k))) ρ) x ,ᶠ travF fs ρ xs
    travF (fnat ∷ fs)                       ρ (n ,ᶠ xs) = n ,ᶠ travF fs ρ xs

  ----------------------------------------------------------------------
  -- Congruence: pointwise-equal environments traverse alike
  ----------------------------------------------------------------------

  module Cong (K : Kit) where
    open Kit K
    ext-cong : ∀ {Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → ∀ x → ext K ρ x ≡ ext K ρ′ x
    ext-cong h vz     = refl
    ext-cong h (vs x) = cong wkV (h x)

    extN-cong : ∀ k {Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → ∀ x → extN K k ρ x ≡ extN K k ρ′ x
    extN-cong zero    h = h
    extN-cong (suc k) h = ext-cong (extN-cong k h)

    trav-cong  : ∀ {s Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → (t : Tm Σ s Γ) → trav K ρ t ≡ trav K ρ′ t
    travF-cong : ∀ fs {Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → (xs : ⟦_⟧ Σ fs Γ) → travF K fs ρ xs ≡ travF K fs ρ′ xs
    trav-cong h (var x)     = cong toTm (h x)
    trav-cong h (node c xs) = cong (node c) (travF-cong (fields Σ c) h xs)
    travF-cong []                                h ⟨⟩        = refl
    travF-cong (fld s zero ∷ fs)                 h (x ,ᶠ xs) = c₂ (trav-cong h x) (travF-cong fs h xs)
    travF-cong (fld s (suc zero) ∷ fs)           h (x ,ᶠ xs) = c₂ (trav-cong (extN-cong 1 h) x) (travF-cong fs h xs)
    travF-cong (fld s (suc (suc zero)) ∷ fs)     h (x ,ᶠ xs) = c₂ (trav-cong (extN-cong 2 h) x) (travF-cong fs h xs)
    travF-cong (fld s (suc (suc (suc k))) ∷ fs)  h (x ,ᶠ xs) = c₂ (trav-cong (extN-cong (suc (suc (suc k))) h) x) (travF-cong fs h xs)
    travF-cong (fnat ∷ fs)                       h (n ,ᶠ xs) = cong (n ,ᶠ_) (travF-cong fs h xs)

  ----------------------------------------------------------------------
  -- Fusion: ONE theorem
  ----------------------------------------------------------------------

  module Fusion (K₁ K₂ K₃ : Kit) where
    open Kit
    Rel : ∀ {Γ Δ Θ} → Env K₁ Γ Δ → Env K₂ Δ Θ → Env K₃ Γ Θ → Set
    Rel ρ₁ ρ₂ ρ₃ = ∀ x → trav K₂ ρ₂ (toTm K₁ (ρ₁ x)) ≡ toTm K₃ (ρ₃ x)

    module _ (ext-rel : ∀ {Γ Δ Θ} {ρ₁ : Env K₁ Γ Δ} {ρ₂ : Env K₂ Δ Θ} {ρ₃ : Env K₃ Γ Θ}
                       → Rel ρ₁ ρ₂ ρ₃ → Rel (ext K₁ ρ₁) (ext K₂ ρ₂) (ext K₃ ρ₃)) where
      private
        extN-rel : ∀ k {Γ Δ Θ} {ρ₁ : Env K₁ Γ Δ} {ρ₂ : Env K₂ Δ Θ} {ρ₃ : Env K₃ Γ Θ}
                 → Rel ρ₁ ρ₂ ρ₃ → Rel (extN K₁ k ρ₁) (extN K₂ k ρ₂) (extN K₃ k ρ₃)
        extN-rel zero    r = r
        extN-rel (suc k) r = ext-rel (extN-rel k r)

      fusion  : ∀ {s Γ Δ Θ} {ρ₁ : Env K₁ Γ Δ} {ρ₂ : Env K₂ Δ Θ} {ρ₃ : Env K₃ Γ Θ}
              → Rel ρ₁ ρ₂ ρ₃ → (t : Tm Σ s Γ) → trav K₂ ρ₂ (trav K₁ ρ₁ t) ≡ trav K₃ ρ₃ t
      fusionF : ∀ fs {Γ Δ Θ} {ρ₁ : Env K₁ Γ Δ} {ρ₂ : Env K₂ Δ Θ} {ρ₃ : Env K₃ Γ Θ}
              → Rel ρ₁ ρ₂ ρ₃ → (xs : ⟦_⟧ Σ fs Γ) → travF K₂ fs ρ₂ (travF K₁ fs ρ₁ xs) ≡ travF K₃ fs ρ₃ xs
      fusion r (var x)     = r x
      fusion r (node c xs) = cong (node c) (fusionF (fields Σ c) r xs)
      fusionF []                                r ⟨⟩        = refl
      fusionF (fld s zero ∷ fs)                 r (x ,ᶠ xs) = c₂ (fusion r x) (fusionF fs r xs)
      fusionF (fld s (suc zero) ∷ fs)           r (x ,ᶠ xs) = c₂ (fusion (extN-rel 1 r) x) (fusionF fs r xs)
      fusionF (fld s (suc (suc zero)) ∷ fs)     r (x ,ᶠ xs) = c₂ (fusion (extN-rel 2 r) x) (fusionF fs r xs)
      fusionF (fld s (suc (suc (suc k))) ∷ fs)  r (x ,ᶠ xs) = c₂ (fusion (extN-rel (suc (suc (suc k))) r) x) (fusionF fs r xs)
      fusionF (fnat ∷ fs)                       r (n ,ᶠ xs) = cong (n ,ᶠ_) (fusionF fs r xs)

  ----------------------------------------------------------------------
  -- Renaming and substitution
  ----------------------------------------------------------------------

  renK : Kit
  renK = record { V = Var ; wkV = vs ; v0 = vz ; toTm = var }

  ren : ∀ {s Γ Δ} → (Var Γ → Var Δ) → Tm Σ s Γ → Tm Σ s Δ
  ren = trav renK

  subK : Kit
  subK = record { V = T ; wkV = ren vs ; v0 = var vz ; toTm = λ t → t }

  sub : ∀ {s Γ Δ} → (Var Γ → T Δ) → Tm Σ s Γ → Tm Σ s Δ
  sub = trav subK

  private
    var-inj : ∀ {Γ} {x y : Var Γ} → _≡_ {T Γ} (var x) (var y) → x ≡ y
    var-inj refl = refl

  ren-ren : ∀ {s Γ Δ Θ} (ρ₁ : Var Γ → Var Δ) (ρ₂ : Var Δ → Var Θ) (t : Tm Σ s Γ)
          → ren ρ₂ (ren ρ₁ t) ≡ ren (λ x → ρ₂ (ρ₁ x)) t
  ren-ren ρ₁ ρ₂ = Fusion.fusion renK renK renK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Var Γ → Var Θ}
       → Fusion.Rel renK renK renK ρ₁ ρ₂ ρ₃ → Fusion.Rel renK renK renK (ext renK ρ₁) (ext renK ρ₂) (ext renK ρ₃)
    er r vz     = refl
    er r (vs x) = cong (λ y → var (vs y)) (var-inj (r x))

  sub-ren : ∀ {s Γ Δ Θ} (ρ : Var Γ → Var Δ) (σ : Var Δ → T Θ) (t : Tm Σ s Γ)
          → sub σ (ren ρ t) ≡ sub (λ x → σ (ρ x)) t
  sub-ren ρ σ = Fusion.fusion renK subK subK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Var Δ → T Θ} {ρ₃ : Var Γ → T Θ}
       → Fusion.Rel renK subK subK ρ₁ ρ₂ ρ₃ → Fusion.Rel renK subK subK (ext renK ρ₁) (ext subK ρ₂) (ext subK ρ₃)
    er r vz     = refl
    er r (vs x) = cong (ren vs) (r x)

  ren-sub : ∀ {s Γ Δ Θ} (σ : Var Γ → T Δ) (ρ : Var Δ → Var Θ) (t : Tm Σ s Γ)
          → ren ρ (sub σ t) ≡ sub (λ x → ren ρ (σ x)) t
  ren-sub σ ρ = Fusion.fusion subK renK subK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → T Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Var Γ → T Θ}
       → Fusion.Rel subK renK subK ρ₁ ρ₂ ρ₃ → Fusion.Rel subK renK subK (ext subK ρ₁) (ext renK ρ₂) (ext subK ρ₃)
    er r vz = refl
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (ren-ren vs (ext renK ρ₂) (ρ₁ x))
            (trans (sym (ren-ren ρ₂ vs (ρ₁ x))) (cong (ren vs) (r x)))

  sub-sub : ∀ {s Γ Δ Θ} (σ₁ : Var Γ → T Δ) (σ₂ : Var Δ → T Θ) (t : Tm Σ s Γ)
          → sub σ₂ (sub σ₁ t) ≡ sub (λ x → sub σ₂ (σ₁ x)) t
  sub-sub σ₁ σ₂ = Fusion.fusion subK subK subK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → T Δ} {ρ₂ : Var Δ → T Θ} {ρ₃ : Var Γ → T Θ}
       → Fusion.Rel subK subK subK ρ₁ ρ₂ ρ₃ → Fusion.Rel subK subK subK (ext subK ρ₁) (ext subK ρ₂) (ext subK ρ₃)
    er r vz = refl
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (sub-ren vs (ext subK ρ₂) (ρ₁ x))
            (trans (sym (ren-sub ρ₂ vs (ρ₁ x))) (cong (ren vs) (r x)))

  ----------------------------------------------------------------------
  -- Substitution by variables is the identity
  ----------------------------------------------------------------------

  private
    ext-id : ∀ {Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → ∀ x → ext subK σ x ≡ var x
    ext-id h vz     = refl
    ext-id h (vs x) = cong (ren vs) (h x)

    extN-id : ∀ k {Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → ∀ x → extN subK k σ x ≡ var x
    extN-id zero    h = h
    extN-id (suc k) h = ext-id (extN-id k h)

  sub-id′  : ∀ {s Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → (t : Tm Σ s Γ) → sub σ t ≡ t
  subF-id′ : ∀ fs {Γ} {σ : Var Γ → T Γ} → (∀ x → σ x ≡ var x) → (xs : ⟦_⟧ Σ fs Γ) → travF subK fs σ xs ≡ xs
  sub-id′ h (var x)     = h x
  sub-id′ h (node c xs) = cong (node c) (subF-id′ (fields Σ c) h xs)
  subF-id′ []                                h ⟨⟩        = refl
  subF-id′ (fld s zero ∷ fs)                 h (x ,ᶠ xs) = c₂ (sub-id′ h x) (subF-id′ fs h xs)
  subF-id′ (fld s (suc zero) ∷ fs)           h (x ,ᶠ xs) = c₂ (sub-id′ (extN-id 1 h) x) (subF-id′ fs h xs)
  subF-id′ (fld s (suc (suc zero)) ∷ fs)     h (x ,ᶠ xs) = c₂ (sub-id′ (extN-id 2 h) x) (subF-id′ fs h xs)
  subF-id′ (fld s (suc (suc (suc k))) ∷ fs)  h (x ,ᶠ xs) = c₂ (sub-id′ (extN-id (suc (suc (suc k))) h) x) (subF-id′ fs h xs)
  subF-id′ (fnat ∷ fs)                       h (n ,ᶠ xs) = cong (n ,ᶠ_) (subF-id′ fs h xs)

  sub-id : ∀ {s Γ} (t : Tm Σ s Γ) → sub var t ≡ t
  sub-id = sub-id′ (λ x → refl)

  ----------------------------------------------------------------------
  -- SYNTACTIC kits: fresh variable `var vz`, weakening `ren vs`
  ----------------------------------------------------------------------

  record Syntactic (K : Kit) : Set where
    field
      toTm-v0 : ∀ {Γ} → Kit.toTm K (Kit.v0 K {Γ}) ≡ var vz
      toTm-wk : ∀ {Γ} (v : Kit.V K Γ) → Kit.toTm K (Kit.wkV K v) ≡ ren vs (Kit.toTm K v)

  renS : Syntactic renK
  renS = record { toTm-v0 = refl ; toTm-wk = λ v → refl }

  subS : Syntactic subK
  subS = record { toTm-v0 = refl ; toTm-wk = λ v → refl }

  -- single substitution: the fresh variable becomes `u`
  single : ∀ {Γ} → T Γ → Var (Γ ∙) → T Γ
  single u vz     = u
  single u (vs x) = var x

  module SynK (K : Kit) (S : Syntactic K) where
    open Kit K
    open Syntactic S

    K-ren : ∀ {s Γ Δ Θ} (ρ : Var Γ → Var Δ) (ρ′ : Env K Δ Θ) (t : Tm Σ s Γ)
          → trav K ρ′ (ren ρ t) ≡ trav K (λ x → ρ′ (ρ x)) t
    K-ren ρ ρ′ = Fusion.fusion renK K K er (λ x → refl)
      where
      er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → Var Δ} {ρ₂ : Env K Δ Θ} {ρ₃ : Env K Γ Θ}
         → Fusion.Rel renK K K ρ₁ ρ₂ ρ₃ → Fusion.Rel renK K K (ext renK ρ₁) (ext K ρ₂) (ext K ρ₃)
      er r vz     = refl
      er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
        trans (toTm-wk (ρ₂ (ρ₁ x))) (trans (cong (ren vs) (r x)) (sym (toTm-wk (ρ₃ x))))

    ren-K : ∀ {s Γ Δ Θ} (ρ′ : Env K Γ Δ) (ρ : Var Δ → Var Θ) (ρ₃ : Env K Γ Θ)
          → (∀ x → ren ρ (toTm (ρ′ x)) ≡ toTm (ρ₃ x))
          → (t : Tm Σ s Γ) → ren ρ (trav K ρ′ t) ≡ trav K ρ₃ t
    ren-K ρ′ ρ ρ₃ h = Fusion.fusion K renK K er h
      where
      er : ∀ {Γ Δ Θ} {ρ₁ : Env K Γ Δ} {ρ₂ : Var Δ → Var Θ} {ρ₃ : Env K Γ Θ}
         → Fusion.Rel K renK K ρ₁ ρ₂ ρ₃ → Fusion.Rel K renK K (ext K ρ₁) (ext renK ρ₂) (ext K ρ₃)
      er r vz = trans (cong (ren (ext renK _)) toTm-v0) (sym toTm-v0)
      er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
        trans (cong (ren (ext renK ρ₂)) (toTm-wk (ρ₁ x)))
        (trans (ren-ren vs (ext renK ρ₂) (toTm (ρ₁ x)))
        (trans (sym (ren-ren ρ₂ vs (toTm (ρ₁ x))))
        (trans (cong (ren vs) (r x)) (sym (toTm-wk (ρ₃ x))))))

    K-sub : ∀ {s Γ Δ Θ} (σ : Var Γ → T Δ) (ρ : Env K Δ Θ) (t : Tm Σ s Γ)
          → trav K ρ (sub σ t) ≡ sub (λ x → trav K ρ (σ x)) t
    K-sub σ ρ = Fusion.fusion subK K subK er (λ x → refl)
      where
      er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → T Δ} {ρ₂ : Env K Δ Θ} {ρ₃ : Var Γ → T Θ}
         → Fusion.Rel subK K subK ρ₁ ρ₂ ρ₃ → Fusion.Rel subK K subK (ext subK ρ₁) (ext K ρ₂) (ext subK ρ₃)
      er r vz = toTm-v0
      er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
        trans (K-ren vs (ext K ρ₂) (ρ₁ x))
        (trans (sym (ren-K ρ₂ vs (λ y → wkV (ρ₂ y)) (λ y → sym (toTm-wk (ρ₂ y))) (ρ₁ x)))
               (cong (ren vs) (r x)))

    sub-K : ∀ {s Γ Δ Θ} (ρ : Env K Γ Δ) (σ : Var Δ → T Θ) (t : Tm Σ s Γ)
          → sub σ (trav K ρ t) ≡ sub (λ x → sub σ (toTm (ρ x))) t
    sub-K ρ σ = Fusion.fusion K subK subK er (λ x → refl)
      where
      er : ∀ {Γ Δ Θ} {ρ₁ : Env K Γ Δ} {ρ₂ : Var Δ → T Θ} {ρ₃ : Var Γ → T Θ}
         → Fusion.Rel K subK subK ρ₁ ρ₂ ρ₃ → Fusion.Rel K subK subK (ext K ρ₁) (ext subK ρ₂) (ext subK ρ₃)
      er r vz = cong (sub (ext subK _)) toTm-v0
      er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
        trans (cong (sub (ext subK ρ₂)) (toTm-wk (ρ₁ x)))
        (trans (sub-ren vs (ext subK ρ₂) (toTm (ρ₁ x)))
        (trans (sym (ren-sub ρ₂ vs (toTm (ρ₁ x)))) (cong (ren vs) (r x))))

    -- SIMULATION: a syntactic kit's traversal IS a substitution
    trav≡sub : ∀ {s Γ Δ} (ρ : Env K Γ Δ) (t : Tm Σ s Γ) → trav K ρ t ≡ sub (λ x → toTm (ρ x)) t
    trav≡sub ρ t = trans (sym (sub-id (trav K ρ t)))
                         (trans (sub-K ρ var t) (Cong.trav-cong subK (λ x → sub-id (toTm (ρ x))) t))

    -- THE SQUARE: K commutes with a substitution, pointwise
    square : ∀ {s Γ Γ′ Δ Δ′} (σ : Var Γ′ → T Γ) (ρ′ : Env K Γ Δ) (ρ : Env K Γ′ Δ′) (σ′ : Var Δ′ → T Δ)
           → (∀ x → trav K ρ′ (σ x) ≡ sub σ′ (toTm (ρ x)))
           → (M : Tm Σ s Γ′) → trav K ρ′ (sub σ M) ≡ sub σ′ (trav K ρ M)
    square σ ρ′ ρ σ′ h M =
      trans (K-sub σ ρ′ M) (trans (Cong.trav-cong subK h M) (sym (sub-K ρ σ′ M)))

    trav-wk : ∀ {s Γ Δ} (ρ : Env K Γ Δ) (A : Tm Σ s Γ) → trav K (ext K ρ) (ren vs A) ≡ ren vs (trav K ρ A)
    trav-wk ρ A = trans (K-ren vs (ext K ρ) A)
                        (sym (ren-K ρ vs (λ y → wkV (ρ y)) (λ y → sym (toTm-wk (ρ y))) A))

    trav-single : ∀ {s Γ Δ} (ρ : Env K Γ Δ) (u : T Γ) (B : Tm Σ s (Γ ∙))
                → trav K ρ (sub (single u) B) ≡ sub (single (trav K ρ u)) (trav K (ext K ρ) B)
    trav-single ρ u B = square (single u) ρ (ext K ρ) (single (trav K ρ u)) h B
      where
      h : ∀ x → trav K ρ (single u x) ≡ sub (single (trav K ρ u)) (toTm (ext K ρ x))
      h vz     = sym (cong (sub (single (trav K ρ u))) toTm-v0)
      h (vs y) = sym (trans (cong (sub (single (trav K ρ u))) (toTm-wk (ρ y)))
                     (trans (sub-ren vs (single (trav K ρ u)) (toTm (ρ y))) (sub-id (toTm (ρ y)))))
