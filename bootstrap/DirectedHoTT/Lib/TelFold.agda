------------------------------------------------------------------------
-- OCP-0009 · LIB — ★★★ A FOLD OVER A CONSTRUCTOR LIST, at a CONSTANT
-- motive, parametric in the ALGEBRA.  The levitated successor of the old
-- `Lib/IFold`: `size` is the algebra (0, +, suc), `depth` is (0, max,
-- suc), and a description is a list of `Tel`s (`Lib/Tel`).
--
--     foldMs Ts   one method per constructor, each COMPUTED from its
--                 telescope by one induction (the description a VARIABLE)
--     ⊢foldE      the one method `methₗ (foldMs Ts)` types at `MethTy`
--     fold-ι      and at constructor `k` it computes to
--                     nd (foldK T (dihN idₛ T D e p))
--
-- ★ THE MOTIVE IS STABLE: `subTy σ K ≡ K`.  That is what "constant" means
--   in a de Bruijn syntax, and it is `refl` at `Nat` and at `Π Nat Nat`
--   (the occurrence check's level-in, bool-out motive).  It is exactly
--   the fact that lets the hypotheses' normal form `IhN` collapse to the
--   σ-free `IhK` — one `Σ' K` per recursive field.
--
-- ⚠ NO TRAILING `op _ z` (kept from `IFold`, same reason): a constructor
--   with ONE recursive field folds to that field's value, not to
--   `op x z` — `plusTm` recurses on its first argument, so a trailing
--   `+ 0` would make a unary-recursive syntax's measure quadratic.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module DirectedHoTT.Lib.TelFold where
open import normalizer.Syntax.Types using ( _≡_; refl; sym; trans; cong; cong₂; subst; _,_ )
open import Agda.Builtin.Nat using ( zero; suc ) renaming ( Nat to ℕ )
open import Agda.Builtin.Bool using ( Bool; true; false )
open import DirectedHoTT.Spec.Syntax
open import DirectedHoTT.Spec.Typing hiding ( _×_; _,,_ )
open import DirectedHoTT.Metatheory.RedCong using ( ⟶*-trans )
open import DirectedHoTT.Metatheory.TySub using ( ⊢-cast )
open import DirectedHoTT.Metatheory.Fundamental.Syntactic using ( ⟨_⟩ᵣ; subTy-var; _,ₛ_ )
open import DirectedHoTT.Metatheory.Premises using ( MethG; methSg )
open import DirectedHoTT.Lib.Sugar
  using ( Cons; []; _∷_; Nth; nth-z; nth-s; tag; Dₗ; conₗ; selF; selF-β; methₗ
        ; AllD; []ᵈ; _∷ᵈ_; ⊢Dₗ; PerK; []ₘ; _∷ₘ_; ⊢methₗ; MethK )
open import DirectedHoTT.Lib.Tel

private
  variable
    Γ Δ : Cx
    c k : ℕ

------------------------------------------------------------------------
-- 1. THE ALGEBRA.  ⚠ Everything is CONTEXT-POLYMORPHIC: a method body
--    lives under three binders the caller never names.
------------------------------------------------------------------------

record Alg : Set₁ where
  field
    K     : {Γ : Cx} → RTy Γ
    z     : {Γ : Cx} → RTm Γ
    op    : {Γ : Cx} → RTm Γ → RTm Γ → RTm Γ
    nd    : {Γ : Cx} → RTm Γ → RTm Γ
    K-sub  : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTy σ (K {Γ}) ≡ K
    z-sub  : {Γ Δ : Cx} (σ : Sub Γ Δ) → subTm σ (z {Γ}) ≡ z
    op-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (a b : RTm Γ) → subTm σ (op a b) ≡ op (subTm σ a) (subTm σ b)
    nd-sub : {Γ Δ : Cx} (σ : Sub Γ Δ) (a : RTm Γ) → subTm σ (nd a) ≡ nd (subTm σ a)
    ⊢K  : {Γ : Ctx} → Γ ⊢ty K
    ⊢z  : {Γ : Ctx} → Γ ⊢ z ∷ K
    ⊢op : {Γ : Ctx} {a b : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ K → Γ ⊢ b ∷ K → Γ ⊢ op a b ∷ K
    ⊢nd : {Γ : Ctx} {a : RTm ⌊ Γ ⌋} → Γ ⊢ a ∷ K → Γ ⊢ nd a ∷ K

module _ (A : Alg) where
  open Alg A

  K-ren : {Γ Δ : Cx} (ρ : Ren Γ Δ) → renTy ρ (K {Γ}) ≡ K
  K-ren ρ = trans (sym (subTy-var ρ K)) (K-sub ⟨ ρ ⟩ᵣ)

  ----------------------------------------------------------------------
  -- 2. THE HYPOTHESES at a stable motive: one `Σ' K` per `tρ`.
  ----------------------------------------------------------------------

  IhK : Tel Δ → RTy Γ
  IhK (tι j)   = Unit
  IhK (tσ S T) = IhK T
  IhK (tρ j T) = Σ' K (IhK T)

  IhK-sub : {Γ Θ : Cx} (σ : Sub Γ Θ) (T : Tel Δ) → subTy σ (IhK {Γ = Γ} T) ≡ IhK T
  IhK-sub σ (tι j)   = refl
  IhK-sub σ (tσ S T) = IhK-sub σ T
  IhK-sub σ (tρ j T) = cong₂ Σ' (K-sub σ) (IhK-sub (extS σ) T)

  IhK-ren : {Γ Θ : Cx} (ρ : Ren Γ Θ) (T : Tel Δ) → renTy ρ (IhK {Γ = Γ} T) ≡ IhK T
  IhK-ren ρ T = trans (sym (subTy-var ρ (IhK T))) (IhK-sub ⟨ ρ ⟩ᵣ T)

  -- ★ the normal form `IhN` IS `IhK` at a stable motive
  IhN-K : (σ : Sub Δ Γ) (T : Tel Δ) (D p : RTm Γ) → IhN σ T D K p ≡ IhK T
  IhN-K σ (tι j)   D p = refl
  IhN-K σ (tσ S T) D p = IhN-K (σ ,ₛ fst p) T D (snd p)
  IhN-K σ (tρ j T) D p =
    cong₂ Σ' (trans (cong (subTy (single (fst p))) (K-sub (extS (single (subTm σ j)))))
                    (K-sub (single (fst p))))
             (trans (cong (λ M → IhN (vs ᵣ∘ₛ σ) T (renTm vs D) M (snd (renTm vs p)))
                          (K-ren (extR (extR vs))))
                    (IhN-K (vs ᵣ∘ₛ σ) T (renTm vs D) (snd (renTm vs p))))

  ----------------------------------------------------------------------
  -- 3. ★ THE FOLD OF ONE NODE, read along the telescope.
  ----------------------------------------------------------------------

  -- does the rest of the telescope have a recursive field?
  ρ? : Tel Δ → Bool
  ρ? (tι j)   = false
  ρ? (tσ S T) = ρ? T
  ρ? (tρ j T) = true

  foldK : Tel Δ → RTm Γ → RTm Γ
  opK   : Bool → Tel Δ → RTm Γ → RTm Γ → RTm Γ
  foldK (tι j)   h = z
  foldK (tσ S T) h = foldK T h
  foldK (tρ j T) h = opK (ρ? T) T (fst h) (snd h)
  opK false T x h = x
  opK true  T x h = op x (foldK T h)

  foldK-sub : {Θ : Cx} (σ : Sub Γ Θ) (T : Tel Δ) (h : RTm Γ) →
              subTm σ (foldK T h) ≡ foldK T (subTm σ h)
  opK-sub   : {Θ : Cx} (σ : Sub Γ Θ) (b : Bool) (T : Tel Δ) (x h : RTm Γ) →
              subTm σ (opK b T x h) ≡ opK b T (subTm σ x) (subTm σ h)
  foldK-sub σ (tι j)   h = z-sub σ
  foldK-sub σ (tσ S T) h = foldK-sub σ T h
  foldK-sub σ (tρ j T) h = opK-sub σ (ρ? T) T (fst h) (snd h)
  opK-sub σ false T x h = refl
  opK-sub σ true  T x h = trans (op-sub σ x (foldK T h)) (cong (op (subTm σ x)) (foldK-sub σ T h))

  ⊢foldK : {Γ : Ctx} (T : Tel Δ) {h : RTm ⌊ Γ ⌋} → Γ ⊢ h ∷ IhK T → Γ ⊢ foldK T h ∷ K
  ⊢opK   : {Γ : Ctx} (b : Bool) (T : Tel Δ) {x h : RTm ⌊ Γ ⌋} →
           Γ ⊢ x ∷ K → Γ ⊢ h ∷ IhK T → Γ ⊢ opK b T x h ∷ K
  ⊢foldK (tι j)   dh = ⊢z
  ⊢foldK (tσ S T) dh = ⊢foldK T dh
  ⊢foldK (tρ j T) dh =
    ⊢opK (ρ? T) T (⊢fst dh) (⊢-cast (IhK-sub (single _) T) (⊢snd dh))
  ⊢opK false T dx dh = dx
  ⊢opK true  T dx dh = ⊢op dx (⊢foldK T dh)

  ----------------------------------------------------------------------
  -- 4. ★ THE METHOD of one constructor, and its type.
  ----------------------------------------------------------------------

  mfold : Tel Δ → RTm Γ
  mfold T = lam (lam (lam (nd (foldK T (var vz)))))

  ⊢mfold : {Γ : Ctx} {I D : RTm ⌊ Γ ⌋} {T : Tel ⌊ Γ ⌋} {s : RTm (((⌊ Γ ⌋ ∙) ∙) ∙)} →
           Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → TelOK Γ I T →
           Γ ⊢ mfold T ∷ MethG I D K ⌜ T ⌝ᵗ s
  ⊢mfold {D = D} {T = T} {s = s} dI dD ok =
    ⊢methT dI dD ⊢K ok
      (⊢-cast (sym (K-sub (methSg s)))
        (⊢nd (⊢foldK T (⊢-cast eq (⊢var here)))))
    where
      D₂ = renTm vs (renTm vs D)
      eq : renTy vs (IhN wk2ₛ T D₂ (wk2M K) (var vz)) ≡ IhK T
      eq = trans (cong (renTy vs)
                   (trans (cong (λ M → IhN wk2ₛ T D₂ M (var vz)) (K-ren _))
                          (IhN-K wk2ₛ T D₂ (var vz))))
                 (IhK-ren vs T)

  ----------------------------------------------------------------------
  -- 5. ★★ THE CONSTRUCTOR LIST.
  ----------------------------------------------------------------------

  -- `j +' k` counts `j` on from `k` with the head case DEFINITIONAL
  --   (`zero +' k = k`) and the step moving `k` (`suc j +' k = j +' suc k`)
  --   — exactly the two shapes `PerK`'s head and tail meet.
  infixl 30 _+'_
  _+'_ : ℕ → ℕ → ℕ
  zero  +' k = k
  suc j +' k = j +' suc k

  +'-suc : (j k : ℕ) → j +' suc k ≡ suc (j +' k)
  +'-suc zero    k = refl
  +'-suc (suc j) k = +'-suc j (suc k)

  +'-zero : (j : ℕ) → j +' zero ≡ j
  +'-zero zero    = refl
  +'-zero (suc j) = trans (+'-suc j zero) (cong suc (+'-zero j))

  foldMs : Tels Δ c → Cons Δ c
  foldMs []ᵗ       = []
  foldMs (T ∷ᵗ Ts) = mfold T ∷ foldMs Ts

  perFold : {Γ : Ctx} {I D f : RTm ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} →
            Γ ⊢ I ∷ U → Γ ⊢ D ∷ Desc I → AllOK Γ I Ts →
            ({j : ℕ} {C : RTm ⌊ Γ ⌋} → Nth ⌜ Ts ⌝ₛ j C → app f (tag (j +' k)) ⟶* C) →
            PerK Γ I D K f k (foldMs Ts)
  perFold dI dD []ᵒ          look = []ₘ
  perFold dI dD (ok ∷ᵒ oks) look = (look nth-z , ⊢mfold dI dD ok) ∷ₘ perFold dI dD oks (λ n → look (nth-s n))

  ⊢foldE : {Γ : Ctx} {I : RTm ⌊ Γ ⌋} {Ts : Tels ⌊ Γ ⌋ c} →
           Γ ⊢ I ∷ U → AllOK Γ I Ts → Γ ⊢ methₗ (foldMs Ts) ∷ MethTy I (Dₗ ⌜ Ts ⌝ₛ) K
  ⊢foldE {Ts = Ts} dI oks =
    ⊢methₗ dI (allD dI oks) ⊢K
      (perFold dI (⊢Dₗ dI (allD dI oks)) oks
        (λ {j} n → subst (λ m → app (selF ⌜ Ts ⌝ₛ) (tag m) ⟶* _) (sym (+'-zero j)) (selF-β n)))

  ----------------------------------------------------------------------
  -- 6. ★★ …AND IT COMPUTES: ι, the three β's of the method, and the
  --    body's substitution pushed through the fold (`foldK-sub`).
  ----------------------------------------------------------------------

  nth-mfold : {Ts : Tels Δ c} {T : Tel Δ} → NthT Ts k T → Nth (foldMs Ts) k (mfold T)
  nth-mfold nthᵗ-z     = nth-z
  nth-mfold (nthᵗ-s n) = nth-s (nth-mfold n)

  fold-ι : {Ts : Tels Δ c} {T : Tel Δ} {i p : RTm Δ} → NthT Ts k T →
           ielim (Dₗ ⌜ Ts ⌝ₛ) i (methₗ (foldMs Ts)) (conₗ k p)
             ⟶* nd (foldK T (dihN idₛ T (Dₗ ⌜ Ts ⌝ₛ) (methₗ (foldMs Ts)) p))
  fold-ι {Ts = Ts} {T} {i} {p} n =
    ⟶*-trans (ιT (nth-⌜⌝ n) (nth-mfold n))
      (step (ξ-appˡ (ξ-appˡ (β _ i)))
      (step (ξ-appˡ (β _ p))
      (step (β _ h)
        (subst (λ t → t ⟶* nd (foldK T h)) (sym body) done))))
    where
      h = dihN idₛ T (Dₗ ⌜ Ts ⌝ₛ) (methₗ (foldMs Ts)) p
      σ₁ = extS (extS (single i))
      σ₂ = extS (single p)
      body : subTm (single h) (subTm σ₂ (subTm σ₁ (nd (foldK T (var vz))))) ≡ nd (foldK T h)
      body = trans (cong (λ t → subTm (single h) (subTm σ₂ t))
                         (trans (nd-sub σ₁ _) (cong nd (foldK-sub σ₁ T (var vz)))))
             (trans (cong (subTm (single h))
                          (trans (nd-sub σ₂ _) (cong nd (foldK-sub σ₂ T (var vz)))))
             (trans (nd-sub (single h) _) (cong nd (foldK-sub (single h) T (var vz)))))
