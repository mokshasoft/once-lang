------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L3.2 — RESIDUALIZING SPLITS:
--            linear NbE with PAIR-RETURNING NEUTRALS
--
-- L3.1 located the frontier at ⊗ to the right of ⊸: a neutral of pair
-- type cannot be split semantically. This stage crosses that line with
-- the RESIDUALIZING SPLIT MONAD — the doorstep of proof-net territory:
--
--   * `Sp P Γ` — a value of shape `P` under a stack of PENDING SPLITS:
--     each `spl` node records a repartition, a neutral pair-scrutinee,
--     and a continuation in the world extended by the two components.
--     In combinator syntax a "let (x,y) = n in …" is just composition
--     — no variable binding, THE payoff of categorical NbE.
--   * Nodes carry pending permutations (the L3.1b trick, systematized):
--     `vmapSp`/`withSpˡ`/`withSpʳ` compose world actions into the top
--     node, where `pid ⊙P ρ` COMPUTES — no syntactic junk.
--   * `absorb` — every type absorbs splits: atoms splice syntactically
--     (`reifySp`), `I` and `⊗` are `Sp`-carriers, functions push splits
--     into their results (`go`, the application-under-splits).
--   * `Val` v2: `Val I` and `Val (A ⊗ B)` are `Sp`-carriers; the Day
--     exponential is unchanged. `GoodR` gains `gr⊗` — functions may
--     RETURN PAIRS; `reflectNe` at `gr⊗` is the let-split of a neutral
--     (one `spl` node over reflected fresh components).
--   * Demos by `refl`: all four L3.1 equalities re-decided over the
--     extended model, plus the new one — double-swap of a NEUTRAL
--     pair under a λ is the identity (β + η + let-split + structural,
--     one `refl`).
--
-- Still excluded (L3.3): `I` to the right of ⊸ — the unit problem.
-- Canonicity across INDEPENDENT splits (their emission order) is the
-- L3.2b/proof-net question; demos here have forced orders.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonB where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; sym )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; Λc; evc )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_; ++-idʳ; ++-assoc
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; _⊙P_; insˡ; padˡ; padʳ; bswapW )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv; ctxOf; splitTm )

private
  psubst : ∀ {Γ Δ Δ'} → Δ ≡ Δ' → Perm Γ Δ → Perm Γ Δ'
  psubst refl p = p

  perm-ε : ∀ {Γ} → Perm Γ ε → Γ ≡ ε
  perm-ε pnil = refl

  -- Γ₁ ++ (Θ₁ ++ Θ₂) ⇒ Θ₁ ++ (Γ₁ ++ Θ₂): the middle block exchange.
  exch : ∀ Γ₁ Θ₁ Θ₂ → Perm (Γ₁ ++ (Θ₁ ++ Θ₂)) (Θ₁ ++ (Γ₁ ++ Θ₂))
  exch Γ₁ Θ₁ Θ₂ =
    psubst (++-assoc Θ₁ Γ₁ Θ₂)
      (psubst (sym (++-assoc Γ₁ Θ₁ Θ₂)) (pid (Γ₁ ++ (Θ₁ ++ Θ₂)))
       ⊙P padʳ Θ₂ (bswapW Γ₁ Θ₁))

  -- X ∷ Y ∷ (Γ₁ ++ Θ₂) ⇒ Γ₁ ++ (X ∷ Y ∷ Θ₂): carry two heads past Γ₁.
  carry² : ∀ {X Y} Γ₁ Θ₂ →
           Perm (X ∷ (Y ∷ (Γ₁ ++ Θ₂))) (Γ₁ ++ (X ∷ (Y ∷ Θ₂)))
  carry² Γ₁ Θ₂ =
    pcons (pcons (pid (Γ₁ ++ Θ₂)) (insˡ Γ₁ here)) (insˡ Γ₁ here)

------------------------------------------------------------------------
-- The residualizing split monad.
------------------------------------------------------------------------

data Sp (P : Ctx → Set) : Ctx → Set where
  ret : ∀ {Γ} → P Γ → Sp P Γ
  spl : ∀ {Γ X Y Γ₁ Γ₂} →
        Perm Γ (Γ₁ ++ Γ₂) → CTm ⟪ Γ₁ ⟫ (X ⊗ Y) →
        Sp P (X ∷ (Y ∷ Γ₂)) → Sp P Γ

mapSp : ∀ {P Q Γ} → (∀ {Δ} → P Δ → Q Δ) → Sp P Γ → Sp Q Γ
mapSp f (ret p)       = ret (f p)
mapSp f (spl ρ n k)   = spl ρ n (mapSp f k)

bindSp : ∀ {P Q Γ} → Sp P Γ → (∀ {Δ} → P Δ → Sp Q Δ) → Sp Q Γ
bindSp (ret p)     f = f p
bindSp (spl ρ n k) f = spl ρ n (bindSp k f)

vmapSp : ∀ {P Γ' Γ} → (∀ {Δ' Δ} → Perm Δ' Δ → P Δ → P Δ') →
         Perm Γ' Γ → Sp P Γ → Sp P Γ'
vmapSp pv ρ (ret p)      = ret (pv ρ p)
vmapSp pv ρ (spl ρ₀ n k) = spl (ρ ⊙P ρ₀) n k

-- Splice all pending splits into syntax around a reified core.
reifySp : ∀ {P T Γ} → (∀ {Δ} → P Δ → CTm ⟪ Δ ⟫ T) → Sp P Γ → CTm ⟪ Γ ⟫ T
reifySp f (ret p) = f p
reifySp f (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) =
  reifySp f k ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ)))

-- Pull the LEFT component's splits out across a repartition.
withSpˡ : ∀ {P Q : Ctx → Set} {Γ Γ₁ Γ₂} →
          Perm Γ (Γ₁ ++ Γ₂) → Sp P Γ₁ →
          (∀ {Δ₁ Δ} → Perm Δ (Δ₁ ++ Γ₂) → P Δ₁ → Sp Q Δ) → Sp Q Γ
withSpˡ ρ (ret p) f = f ρ p
withSpˡ {Γ₂ = Γ₂} ρ (spl {X = X} {Y} {Θ₁} {Θ₂} ρ₁ n k) f =
  spl (psubst (++-assoc Θ₁ Θ₂ Γ₂) (ρ ⊙P padʳ Γ₂ ρ₁)) n
      (withSpˡ (pid (X ∷ (Y ∷ (Θ₂ ++ Γ₂)))) k f)

-- Pull the RIGHT component's splits out across a repartition.
withSpʳ : ∀ {P Q : Ctx → Set} {Γ Γ₁ Γ₂} →
          Perm Γ (Γ₁ ++ Γ₂) → Sp P Γ₂ →
          (∀ {Δ₂ Δ} → Perm Δ (Γ₁ ++ Δ₂) → P Δ₂ → Sp Q Δ) → Sp Q Γ
withSpʳ ρ (ret p) f = f ρ p
withSpʳ {Γ₁ = Γ₁} ρ (spl {X = X} {Y} {Θ₁} {Θ₂} ρ₂ n k) f =
  spl (ρ ⊙P (padˡ Γ₁ ρ₂ ⊙P exch Γ₁ Θ₁ Θ₂)) n
      (withSpʳ (carry² Γ₁ Θ₂) k f)

------------------------------------------------------------------------
-- The model, v2: I and ⊗ are Sp-carriers.
------------------------------------------------------------------------

NeAt : (Ctx → Set) → Ctx → Set
NeAt N Γ = Σ Ctx (λ Γ₀ → Σ (Perm Γ Γ₀) (λ _ → N Γ₀))

Val : CTy → Ctx → Set
Val ι₁      Γ = NeAt (λ Γ₀ → CTm ⟪ Γ₀ ⟫ ι₁) Γ
Val ι₂      Γ = NeAt (λ Γ₀ → CTm ⟪ Γ₀ ⟫ ι₂) Γ
Val I       Γ = Sp (λ Δ → Δ ≡ ε) Γ
Val (A ⊗ B) Γ = Sp (λ Δ →
  Σ Ctx (λ Δ₁ → Σ Ctx (λ Δ₂ →
    Σ (Perm Δ (Δ₁ ++ Δ₂)) (λ _ → Σ (Val A Δ₁) (λ _ → Val B Δ₂))))) Γ

Val (A ⊸ B) Γ = ∀ Δ → Val A Δ → Val B (Γ ++ Δ)

private
  pvI : ∀ {Δ' Δ} → Perm Δ' Δ → Δ ≡ ε → Δ' ≡ ε
  pvI ρ' refl = perm-ε ρ'

vmap : ∀ A {Γ' Γ} → Perm Γ' Γ → Val A Γ → Val A Γ'
vmap ι₁      ρ (Γ₀ , (ρ₀ , n)) = Γ₀ , ((ρ ⊙P ρ₀) , n)
vmap ι₂      ρ (Γ₀ , (ρ₀ , n)) = Γ₀ , ((ρ ⊙P ρ₀) , n)
vmap I       ρ v = vmapSp pvI ρ v
vmap (A ⊗ B) ρ v =
  vmapSp (λ ρ' (Δ₁ , (Δ₂ , (ρ₀ , x))) → Δ₁ , (Δ₂ , ((ρ' ⊙P ρ₀) , x)))
         ρ v
vmap (A ⊸ B) ρ f = λ Δ v → vmap B (padʳ Δ ρ) (f Δ v)

------------------------------------------------------------------------
-- Absorption: every type swallows pending splits.
------------------------------------------------------------------------

absorb : ∀ A {Γ} → Sp (Val A) Γ → Val A Γ
absorb ι₁ (ret v) = v
absorb ι₁ {Γ} sp@(spl _ _ _) =
  Γ , (pid Γ , reifySp (λ (Γ₀ , (ρ₀ , n)) → n ∘c permC ρ₀) sp)
absorb ι₂ (ret v) = v
absorb ι₂ {Γ} sp@(spl _ _ _) =
  Γ , (pid Γ , reifySp (λ (Γ₀ , (ρ₀ , n)) → n ∘c permC ρ₀) sp)
absorb I       sp = bindSp sp (λ v → v)
absorb (A ⊗ B) sp = bindSp sp (λ v → v)
absorb (A ⊸ B) sp = λ Δ v → absorb B (go Δ v sp)
  where
  go : ∀ Δ → Val A Δ → ∀ {Γ} → Sp (Val (A ⊸ B)) Γ → Sp (Val B) (Γ ++ Δ)
  go Δ v (ret f) = ret (f Δ v)
  go Δ v (spl {Γ₁ = Θ₁} {Θ₂} ρ n k) =
    spl (psubst (++-assoc Θ₁ Θ₂ Δ) (padʳ Δ ρ)) n (go Δ v k)

------------------------------------------------------------------------
-- Evaluation: repartition arithmetic, now under splits.
------------------------------------------------------------------------

evalV : ∀ {A B} → CTm A B → ∀ {Γ} → Val A Γ → Val B Γ
evalV idc      v = v
evalV (f ∘c g) v = evalV f (evalV g v)
evalV (f ⊗c g) v =
  mapSp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
          Δ₁ , (Δ₂ , (ρ , (evalV f va , evalV g vb)))) v
evalV αrc v =
  bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (vab , vd)))) →
    withSpˡ ρ vab (λ ρ' (Θ₁ , (Θ₂ , (ρᵢ , (va , vb)))) →
      ret (Θ₁ , ((Θ₂ ++ Δ₂) ,
        ( psubst (++-assoc Θ₁ Θ₂ Δ₂) (ρ' ⊙P padʳ Δ₂ ρᵢ)
        , (va , ret (Θ₂ , (Δ₂ , (pid (Θ₂ ++ Δ₂) , (vb , vd))))))))))
evalV αlc v =
  bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (va , vbd)))) →
    withSpʳ ρ vbd (λ ρ' (Θ₁ , (Θ₂ , (ρᵢ , (vb , vd)))) →
      ret ((Δ₁ ++ Θ₁) , (Θ₂ ,
        ( psubst (sym (++-assoc Δ₁ Θ₁ Θ₂)) (ρ' ⊙P padˡ Δ₁ ρᵢ)
        , (ret (Δ₁ , (Θ₁ , (pid (Δ₁ ++ Θ₁) , (va , vb)))) , vd))))))
evalV {B = A} ƛrc v =
  absorb A (bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (vI , va)))) →
    withSpˡ ρ vI (kƛ A va)))
  where
  kƛ : ∀ A {Δ₂} → Val A Δ₂ →
       ∀ {Δ₁' Δ} → Perm Δ (Δ₁' ++ Δ₂) → Δ₁' ≡ ε → Sp (Val A) Δ
  kƛ A va ρ' refl = ret (vmap A ρ' va)
evalV ƛlc {Γ} v = ret (ε , (Γ , (pid Γ , (ret refl , v))))
evalV {B = A} ρrc v =
  absorb A (bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (va , vI)))) →
    withSpʳ ρ vI (kρ A va)))
  where
  kρ : ∀ A {Δ₁} → Val A Δ₁ →
       ∀ {Δ₂' Δ} → Perm Δ (Δ₁ ++ Δ₂') → Δ₂' ≡ ε → Sp (Val A) Δ
  kρ A {Δ₁} va ρ' refl = ret (vmap A (psubst (++-idʳ Δ₁) ρ') va)
evalV ρlc {Γ} v =
  ret (Γ , (ε , (psubst (sym (++-idʳ Γ)) (pid Γ) , (v , ret refl))))
evalV σc v =
  mapSp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
          Δ₂ , (Δ₁ , ((ρ ⊙P bswapW Δ₁ Δ₂) , (vb , va)))) v
evalV (Λc f) {Γ} v =
  λ Δ w → evalV f (ret (Γ , (Δ , (pid (Γ ++ Δ) , (v , w)))))
evalV {B = B} evc v =
  absorb B (bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (vf , va)))) →
    ret (vmap B ρ (vf Δ₂ va))))

------------------------------------------------------------------------
-- Right-purity, v2: functions may return pairs (gr⊗). Units on the
-- right remain the L3.3 frontier.
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
    gr⊗ : ∀ {A B} → GoodR A → GoodR B → GoodR (A ⊗ B)
    gr⊸ : ∀ {A B} → Good A → GoodR B → GoodR (A ⊸ B)

mutual
  reify : ∀ {A Γ} → Good A → Val A Γ → CTm ⟪ Γ ⟫ A
  reify g₁ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reify g₂ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reify gI v = reifySp (λ { refl → idc }) v
  reify (g⊗ ga gb) v =
    reifySp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
      ((reify ga va ⊗c reify gb vb) ∘c mult Δ₁ Δ₂) ∘c permC ρ) v
  reify {Γ = Γ} (g⊸ {A} ga grb) f =
    Λc (reifyR grb (f (ctxOf A) (reflectTy ga)) ∘c
        (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A)))

  reifyR : ∀ {B Γ} → GoodR B → Val B Γ → CTm ⟪ Γ ⟫ B
  reifyR gr₁ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reifyR gr₂ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reifyR (gr⊗ ga gb) v =
    reifySp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
      ((reifyR ga va ⊗c reifyR gb vb) ∘c mult Δ₁ Δ₂) ∘c permC ρ) v
  reifyR {Γ = Γ} (gr⊸ {A} ga grb) f =
    Λc (reifyR grb (f (ctxOf A) (reflectTy ga)) ∘c
        (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A)))

  reflectTy : ∀ {A} → Good A → Val A (ctxOf A)
  reflectTy g₁ = (ι₁ ∷ ε) , (pid (ι₁ ∷ ε) , ρrc)
  reflectTy g₂ = (ι₂ ∷ ε) , (pid (ι₂ ∷ ε) , ρrc)
  reflectTy gI = ret refl
  reflectTy (g⊗ {A} {B} ga gb) =
    ret (ctxOf A , (ctxOf B ,
      (pid (ctxOf A ++ ctxOf B) , (reflectTy ga , reflectTy gb))))
  reflectTy (g⊸ ga grb) =
    λ Δ v → reflectNe grb (evc ∘c (idc ⊗c reify ga v))

  -- The let-split of a neutral: one spl node over fresh components.
  reflectNe : ∀ {B Γ} → GoodR B → CTm ⟪ Γ ⟫ B → Val B Γ
  reflectNe {Γ = Γ} gr₁ n = Γ , (pid Γ , n)
  reflectNe {Γ = Γ} gr₂ n = Γ , (pid Γ , n)
  reflectNe {B = X ⊗ Y} {Γ = Γ} (gr⊗ ga gb) n =
    spl (psubst (sym (++-idʳ Γ)) (pid Γ)) n
        (ret ((X ∷ ε) , ((Y ∷ ε) ,
          ( pid (X ∷ (Y ∷ ε))
          , (reflectNe ga ρrc , reflectNe gb ρrc)))))
  reflectNe {Γ = Γ} (gr⊸ ga grb) n =
    λ Δ v → reflectNe grb ((evc ∘c (n ⊗c reify ga v)) ∘c mult Γ Δ)

------------------------------------------------------------------------
-- THE NORMALIZER, v2.
------------------------------------------------------------------------

NF : ∀ {A B} → Good A → Good B → CTm A B → CTm A B
NF {A} ga gb f = reify gb (evalV f (reflectTy ga)) ∘c splitTm A

------------------------------------------------------------------------
-- Demos — the L3.1 four, re-decided over the extended model, plus the
-- new frontier crossing.
------------------------------------------------------------------------

private
  gA⊗ : Good (ι₁ ⊗ ι₂)
  gA⊗ = g⊗ g₁ g₂

  gB⊗ : Good (ι₂ ⊗ ι₁)
  gB⊗ = g⊗ g₂ g₁

  g⇒ : Good (ι₁ ⊸ ι₂)
  g⇒ = g⊸ g₁ gr₂

  _ : NF gA⊗ gB⊗ (evc ∘c (Λc σc ⊗c idc)) ≡ NF gA⊗ gB⊗ σc
  _ = refl

  _ : NF g⇒ g⇒ (Λc (evc ∘c (idc ⊗c idc))) ≡ NF g⇒ g⇒ idc
  _ = refl

  _ : NF gA⊗ gA⊗ (σc {ι₂} {ι₁} ∘c σc) ≡ NF gA⊗ gA⊗ idc
  _ = refl

  flipC : ∀ {A B D} → CTm A (B ⊸ D) → CTm B (A ⊸ D)
  flipC g = Λc (evc ∘c ((g ⊗c idc) ∘c σc))

  _ : NF g⇒ g⇒ (flipC (flipC idc)) ≡ NF g⇒ g⇒ idc
  _ = refl

  -- THE FRONTIER CROSSED: a function returning a PAIR. Double-swapping
  -- the neutral pair under a λ normalizes like not touching it:
  -- β + η + let-split + structural, one refl.
  g⇒⊗ : Good (ι₁ ⊸ (ι₁ ⊗ ι₂))
  g⇒⊗ = g⊸ g₁ (gr⊗ gr₁ gr₂)

  _ : NF g⇒⊗ g⇒⊗ (Λc ((σc ∘c σc) ∘c evc)) ≡ NF g⇒⊗ g⇒⊗ idc
  _ = refl
