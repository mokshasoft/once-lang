-- SPIKE (untracked): generic scoped syntax at the META level (SPIKE-GENERIC-SYNTAX S1).
--
-- A syntax is a binding signature, in the shape of `Lib/Syn` (the Knot's
-- object-level one): sorts, constructors per sort, each a list of fields
-- (`rec s k`: a subterm of sort `s` under `k` new binders; `nat`: a
-- natural), and variables at one sort. Over it: ONE traversal by a kit,
-- ONE congruence, ONE fusion theorem; renaming and substitution are
-- instances, and the four fusion lemmas of `Spec/Syntax` are corollaries.

{-# OPTIONS --safe #-}
module tmp.GenSyn where
open import DirectedHoTT.Prelude using ( _≡_; refl; sym; trans; cong )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.List using ( List; []; _∷_ )
open import DirectedHoTT.Spec.Scope using ( Cx; ε; _∙; Var; vz; vs )

------------------------------------------------------------------------
-- Binding signatures
------------------------------------------------------------------------

data Field (S : Set) : Set where
  rec : S → ℕ → Field S
  nat : Field S

record Sig : Set₁ where
  field
    Sort   : Set
    vsort  : Sort                       -- the sort variables live at
    Con    : Sort → Set
    fields : ∀ {s} → Con s → List (Field Sort)
open Sig public

_⋯_ : Cx → ℕ → Cx
Γ ⋯ zero  = Γ
Γ ⋯ suc k = (Γ ⋯ k) ∙

------------------------------------------------------------------------
-- The syntax of a signature
------------------------------------------------------------------------

module _ (Σ : Sig) where
  data Tm : Sort Σ → Cx → Set
  data Args (Γ : Cx) : List (Field (Sort Σ)) → Set

  data Tm where
    var : ∀ {Γ} → Var Γ → Tm (vsort Σ) Γ
    con : ∀ {s Γ} (c : Con Σ s) → Args Γ (fields Σ c) → Tm s Γ

  infixr 5 _∷ʳ_ _∷ⁿ_
  data Args Γ where
    []   : Args Γ []
    _∷ʳ_ : ∀ {s k fs} → Tm s (Γ ⋯ k) → Args Γ fs → Args Γ (rec s k ∷ fs)
    _∷ⁿ_ : ∀ {fs} → ℕ → Args Γ fs → Args Γ (nat ∷ fs)

------------------------------------------------------------------------
-- Kits and the one traversal
------------------------------------------------------------------------

module Trav (Σ : Sig) where
  T = Tm Σ (vsort Σ)

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
    travA : ∀ {fs Γ Δ} → Env Γ Δ → Args Σ Γ fs → Args Σ Δ fs
    trav ρ (var x)    = toTm (ρ x)
    trav ρ (con c as) = con c (travA ρ as)
    travA ρ []                       = []
    travA ρ (_∷ʳ_ {k = k} t as)      = trav (extN k ρ) t ∷ʳ travA ρ as
    travA ρ (n ∷ⁿ as)                = n ∷ⁿ travA ρ as

  ----------------------------------------------------------------------
  -- Congruence: pointwise-equal environments traverse alike (no funext)
  ----------------------------------------------------------------------

  module Cong (K : Kit) where
    open Kit K
    private
      ext-cong : ∀ {Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → ∀ x → ext K ρ x ≡ ext K ρ′ x
      ext-cong h vz     = refl
      ext-cong h (vs x) = cong wkV (h x)

      extN-cong : ∀ k {Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → ∀ x → extN K k ρ x ≡ extN K k ρ′ x
      extN-cong zero    h = h
      extN-cong (suc k) h = ext-cong (extN-cong k h)

    trav-cong  : ∀ {s Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → (t : Tm Σ s Γ) → trav K ρ t ≡ trav K ρ′ t
    travA-cong : ∀ {fs Γ Δ} {ρ ρ′ : Env K Γ Δ} → (∀ x → ρ x ≡ ρ′ x) → (as : Args Σ Γ fs) → travA K ρ as ≡ travA K ρ′ as
    trav-cong h (var x)    = cong toTm (h x)
    trav-cong h (con c as) = cong (con c) (travA-cong h as)
    travA-cong h []                  = refl
    travA-cong h (_∷ʳ_ {k = k} t as) = cong₂ʳ (trav-cong (extN-cong k h) t) (travA-cong h as)
      where cong₂ʳ : ∀ {s k fs Γ} {a a′ : Tm Σ s (Γ ⋯ k)} {b b′ : Args Σ Γ fs} → a ≡ a′ → b ≡ b′ → (a ∷ʳ b) ≡ (a′ ∷ʳ b′)
            cong₂ʳ refl refl = refl
    travA-cong h (n ∷ⁿ as)           = cong (n ∷ⁿ_) (travA-cong h as)

  ----------------------------------------------------------------------
  -- Fusion: ONE theorem. Given three kits and environments related at
  -- every variable, stable under one binder, the two traversals fuse.
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
      fusionA : ∀ {fs Γ Δ Θ} {ρ₁ : Env K₁ Γ Δ} {ρ₂ : Env K₂ Δ Θ} {ρ₃ : Env K₃ Γ Θ}
              → Rel ρ₁ ρ₂ ρ₃ → (as : Args Σ Γ fs) → travA K₂ ρ₂ (travA K₁ ρ₁ as) ≡ travA K₃ ρ₃ as
      fusion r (var x)    = r x
      fusion r (con c as) = cong (con c) (fusionA r as)
      fusionA r []                  = refl
      fusionA r (_∷ʳ_ {k = k} t as) = c₂ (fusion (extN-rel k r) t) (fusionA r as)
        where c₂ : ∀ {s k fs Γ} {a a′ : Tm Σ s (Γ ⋯ k)} {b b′ : Args Σ Γ fs} → a ≡ a′ → b ≡ b′ → (a ∷ʳ b) ≡ (a′ ∷ʳ b′)
              c₂ refl refl = refl
      fusionA r (n ∷ⁿ as)           = cong (n ∷ⁿ_) (fusionA r as)

  ----------------------------------------------------------------------
  -- The two instances
  ----------------------------------------------------------------------

  renK : Kit
  renK = record { V = Var ; wkV = vs ; v0 = vz ; toTm = var }

  ren : ∀ {s Γ Δ} → (Var Γ → Var Δ) → Tm Σ s Γ → Tm Σ s Δ
  ren = trav renK

  subK : Kit
  subK = record { V = T ; wkV = ren vs ; v0 = var vz ; toTm = λ t → t }

  sub : ∀ {s Γ Δ} → (Var Γ → T Δ) → Tm Σ s Γ → Tm Σ s Δ
  sub = trav subK

  ----------------------------------------------------------------------
  -- The four fusion lemmas of `Spec/Syntax`, as corollaries.
  -- Each instance proves only `ext-rel`: the vz and vs cases of one binder.
  ----------------------------------------------------------------------

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
    er r vz     = refl
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (ren-ren vs (ext renK ρ₂) (ρ₁ x))
            (trans (sym (ren-ren ρ₂ vs (ρ₁ x))) (cong (ren vs) (r x)))

  sub-sub : ∀ {s Γ Δ Θ} (σ₁ : Var Γ → T Δ) (σ₂ : Var Δ → T Θ) (t : Tm Σ s Γ)
          → sub σ₂ (sub σ₁ t) ≡ sub (λ x → sub σ₂ (σ₁ x)) t
  sub-sub σ₁ σ₂ = Fusion.fusion subK subK subK er (λ x → refl)
    where
    er : ∀ {Γ Δ Θ} {ρ₁ : Var Γ → T Δ} {ρ₂ : Var Δ → T Θ} {ρ₃ : Var Γ → T Θ}
       → Fusion.Rel subK subK subK ρ₁ ρ₂ ρ₃ → Fusion.Rel subK subK subK (ext subK ρ₁) (ext subK ρ₂) (ext subK ρ₃)
    er r vz     = refl
    er {ρ₁ = ρ₁} {ρ₂} {ρ₃} r (vs x) =
      trans (sub-ren vs (ext subK ρ₂) (ρ₁ x))
            (trans (sym (ren-sub ρ₂ vs (ρ₁ x))) (cong (ren vs) (r x)))
