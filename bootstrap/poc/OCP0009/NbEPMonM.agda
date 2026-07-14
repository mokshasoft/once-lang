------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L3.1b — LINEAR NbE: THE MODEL
--
-- Normalization by evaluation for the closed linear core, on the
-- right-pure fragment (plan §10 derivation, transcribed):
--
--   * `Val` — the Day-convolution model over the L3.0 world category:
--       Val ι Γ       = CTm ⟪Γ⟫ ι            (a neutral)
--       Val I Γ       = Γ ≡ ε                (units carry nothing)
--       Val (A ⊗ B) Γ = a REPARTITION Perm Γ (Γ₁ ++ Γ₂) + two values
--       Val (A ⊸ B) Γ = ∀ Δ → Val A Δ → Val B (Γ ++ Δ)
--     The ⊸-clause is the Day exponential: worlds COMBINE — there is
--     no weakening to forbid, it is unwritable in this index
--     discipline. Linearity is enforced by the shape of the model.
--   * `vmap` — the presheaf action along world permutations.
--   * `evalV` — every combinator, by structural recursion; the α/ƛ/ρ/σ
--     cases are REPARTITION ARITHMETIC in the world category (L3.0's
--     ⊙P/pad/bswapW), never syntax.
--   * `reify`/`reflectTy`/`reflectNe` — mutual, structured on the
--     right-purity witnesses `Good`/`GoodR` so termination is
--     structural. Reflection decomposes types (⊗ flattens, I
--     vanishes, ⊸ probes with a reflected generic argument).
--   * `NF` — the normalizer: NF f = reify (evalV f (reflectTy _)) ∘
--     splitTm. β, η, AND the structural theory all collapse in the
--     model, so βη-equal programs get IDENTICAL normal forms — checked
--     by `refl` in the demos, including a genuinely higher-order one
--     (double `flip` = identity).
--
-- `Good`/`GoodR` exclude exactly the located frontier: ⊗/I to the
-- right of ⊸ (function results). Those return in L3.2 (residualizing
-- let-monad) and L3.3 (the unit problem).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonM where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; sym )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; Λc; evc )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; ++-idʳ; ++-assoc
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; _⊙P_; padˡ; padʳ; bswapW )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv; ctxOf; splitTm )

private
  psubst : ∀ {Γ Δ Δ'} → Δ ≡ Δ' → Perm Γ Δ → Perm Γ Δ'
  psubst refl p = p

  perm-ε : ∀ {Γ} → Perm Γ ε → Γ ≡ ε
  perm-ε pnil = refl

------------------------------------------------------------------------
-- The model.
------------------------------------------------------------------------

-- Atom-neutrals carry a PENDING world permutation: world actions
-- compose in the world category (where `pid ⊙P ρ` COMPUTES to `ρ`),
-- not in syntax — no junk, so equal values reify to identical terms.
NeAt : (Ctx → Set) → Ctx → Set
NeAt N Γ = Σ Ctx (λ Γ₀ → Σ (Perm Γ Γ₀) (λ _ → N Γ₀))

Val : CTy → Ctx → Set
Val ι₁      Γ = NeAt (λ Γ₀ → CTm ⟪ Γ₀ ⟫ ι₁) Γ
Val ι₂      Γ = NeAt (λ Γ₀ → CTm ⟪ Γ₀ ⟫ ι₂) Γ
Val I       Γ = Γ ≡ ε
Val (A ⊗ B) Γ =
  Σ Ctx (λ Γ₁ → Σ Ctx (λ Γ₂ →
    Σ (Perm Γ (Γ₁ ++ Γ₂)) (λ _ → Σ (Val A Γ₁) (λ _ → Val B Γ₂))))
Val (A ⊸ B) Γ = ∀ Δ → Val A Δ → Val B (Γ ++ Δ)

vmap : ∀ A {Γ' Γ} → Perm Γ' Γ → Val A Γ → Val A Γ'
vmap ι₁      ρ (Γ₀ , (ρ₀ , n)) = Γ₀ , ((ρ ⊙P ρ₀) , n)
vmap ι₂      ρ (Γ₀ , (ρ₀ , n)) = Γ₀ , ((ρ ⊙P ρ₀) , n)
vmap I       ρ refl = perm-ε ρ
vmap (A ⊗ B) ρ (Γ₁ , (Γ₂ , (ρ₀ , (va , vb)))) =
  Γ₁ , (Γ₂ , ((ρ ⊙P ρ₀) , (va , vb)))
vmap (A ⊸ B) ρ f    = λ Δ v → vmap B (padʳ Δ ρ) (f Δ v)

------------------------------------------------------------------------
-- Evaluation: repartition arithmetic in the world category.
------------------------------------------------------------------------

evalV : ∀ {A B} → CTm A B → ∀ {Γ} → Val A Γ → Val B Γ
evalV idc      v = v
evalV (f ∘c g) v = evalV f (evalV g v)
evalV (f ⊗c g) (Γ₁ , (Γ₂ , (ρ , (va , vb)))) =
  Γ₁ , (Γ₂ , (ρ , (evalV f va , evalV g vb)))
evalV αrc (Γ₁ , (Γ₂ , (ρ , ((Γ₁₁ , (Γ₁₂ , (ρ₁ , (va , vb)))) , vd)))) =
  Γ₁₁ , ((Γ₁₂ ++ Γ₂) ,
    ( psubst (++-assoc Γ₁₁ Γ₁₂ Γ₂) (ρ ⊙P padʳ Γ₂ ρ₁)
    , (va , (Γ₁₂ , (Γ₂ , (pid (Γ₁₂ ++ Γ₂) , (vb , vd)))))))
evalV αlc (Γ₁ , (Γ₂ , (ρ , (va , (Γ₂₁ , (Γ₂₂ , (ρ₂ , (vb , vd)))))))) =
  (Γ₁ ++ Γ₂₁) , (Γ₂₂ ,
    ( psubst (sym (++-assoc Γ₁ Γ₂₁ Γ₂₂)) (ρ ⊙P padˡ Γ₁ ρ₂)
    , ((Γ₁ , (Γ₂₁ , (pid (Γ₁ ++ Γ₂₁) , (va , vb)))) , vd)))
evalV ƛrc (_ , (Γ₂ , (ρ , (refl , va)))) = vmap _ ρ va
evalV {A} ƛlc {Γ} v = ε , (Γ , (pid Γ , (refl , v)))
evalV ρrc (Γ₁ , (_ , (ρ , (va , refl)))) =
  vmap _ (psubst (++-idʳ Γ₁) ρ) va
evalV ρlc {Γ} v =
  Γ , (ε , (psubst (sym (++-idʳ Γ)) (pid Γ) , (v , refl)))
evalV σc (Γ₁ , (Γ₂ , (ρ , (va , vb)))) =
  Γ₂ , (Γ₁ , ((ρ ⊙P bswapW Γ₁ Γ₂) , (vb , va)))
evalV (Λc f) {Γ} v =
  λ Δ w → evalV f (Γ , (Δ , (pid (Γ ++ Δ) , (v , w))))
evalV evc (Γ₁ , (Γ₂ , (ρ , (vf , va)))) = vmap _ ρ (vf Γ₂ va)

------------------------------------------------------------------------
-- Right-purity witnesses: the located frontier, excluded structurally.
------------------------------------------------------------------------

mutual
  data Good : CTy → Set where
    g₁ : Good ι₁
    g₂ : Good ι₂
    gI : Good I
    g⊗ : ∀ {A B} → Good A → Good B → Good (A ⊗ B)
    g⊸ : ∀ {A B} → Good A → GoodR B → Good (A ⊸ B)

  data GoodR : CTy → Set where
    gr₁ : GoodR ι₁
    gr₂ : GoodR ι₂
    gr⊸ : ∀ {A B} → Good A → GoodR B → GoodR (A ⊸ B)

------------------------------------------------------------------------
-- Reify and reflect, mutual on the witnesses.
------------------------------------------------------------------------

mutual
  reify : ∀ {A Γ} → Good A → Val A Γ → CTm ⟪ Γ ⟫ A
  reify g₁ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reify g₂ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reify gI refl = idc
  reify {Γ = Γ} (g⊗ ga gb) (Γ₁ , (Γ₂ , (ρ , (va , vb)))) =
    ((reify ga va ⊗c reify gb vb) ∘c mult Γ₁ Γ₂) ∘c permC ρ
  reify {Γ = Γ} (g⊸ {A} ga grb) f =
    Λc (reifyR grb (f (ctxOf A) (reflectTy ga)) ∘c
        (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A)))

  reifyR : ∀ {B Γ} → GoodR B → Val B Γ → CTm ⟪ Γ ⟫ B
  reifyR gr₁ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reifyR gr₂ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reifyR {Γ = Γ} (gr⊸ {A} ga grb) f =
    Λc (reifyR grb (f (ctxOf A) (reflectTy ga)) ∘c
        (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A)))

  reflectTy : ∀ {A} → Good A → Val A (ctxOf A)
  reflectTy g₁ = (ι₁ ∷ ε) , (pid (ι₁ ∷ ε) , ρrc)
  reflectTy g₂ = (ι₂ ∷ ε) , (pid (ι₂ ∷ ε) , ρrc)
  reflectTy gI = refl
  reflectTy (g⊗ {A} {B} ga gb) =
    ctxOf A , (ctxOf B ,
      (pid (ctxOf A ++ ctxOf B) , (reflectTy ga , reflectTy gb)))
  reflectTy (g⊸ ga grb) =
    λ Δ v → reflectNe grb (evc ∘c (idc ⊗c reify ga v))

  reflectNe : ∀ {B Γ} → GoodR B → CTm ⟪ Γ ⟫ B → Val B Γ
  reflectNe {Γ = Γ} gr₁ n = Γ , (pid Γ , n)
  reflectNe {Γ = Γ} gr₂ n = Γ , (pid Γ , n)
  reflectNe {Γ = Γ} (gr⊸ ga grb) n =
    λ Δ v → reflectNe grb ((evc ∘c (n ⊗c reify ga v)) ∘c mult Γ Δ)

------------------------------------------------------------------------
-- THE NORMALIZER.
------------------------------------------------------------------------

NF : ∀ {A B} → Good A → Good B → CTm A B → CTm A B
NF {A} ga gb f = reify gb (evalV f (reflectTy ga)) ∘c splitTm A

------------------------------------------------------------------------
-- Demos: β, η, structural — and a higher-order equality — all get
-- IDENTICAL normal forms, by refl.
------------------------------------------------------------------------

private
  gA⊗ : Good (ι₁ ⊗ ι₂)
  gA⊗ = g⊗ g₁ g₂

  gB⊗ : Good (ι₂ ⊗ ι₁)
  gB⊗ = g⊗ g₂ g₁

  g⇒ : Good (ι₁ ⊸ ι₂)
  g⇒ = g⊸ g₁ gr₂

  -- β⊸: ev ∘ (Λ σ ⊗ 1) normalizes like σ.
  _ : NF gA⊗ gB⊗ (evc ∘c (Λc σc ⊗c idc)) ≡ NF gA⊗ gB⊗ σc
  _ = refl

  -- η⊸: Λ(ev ∘ (id ⊗ 1)) normalizes like id, at a function type.
  _ : NF g⇒ g⇒ (Λc (evc ∘c (idc ⊗c idc))) ≡ NF g⇒ g⇒ idc
  _ = refl

  -- Structural: σ ∘ σ normalizes like id.
  _ : NF gA⊗ gA⊗ (σc {ι₂} {ι₁} ∘c σc) ≡ NF gA⊗ gA⊗ idc
  _ = refl

  -- HIGHER-ORDER: flipping a function twice normalizes like not
  -- flipping it at all — a βη + structural equality, decided by refl.
  flipC : ∀ {A B D} → CTm A (B ⊸ D) → CTm B (A ⊸ D)
  flipC g = Λc (evc ∘c ((g ⊗c idc) ∘c σc))

  _ : NF g⇒ g⇒ (flipC (flipC idc)) ≡ NF g⇒ g⇒ idc
  _ = refl
