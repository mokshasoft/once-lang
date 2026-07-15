------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L3.3 — UNITS CROSSED:
--            a TOTAL normalizer for the free SMCC
--
-- The last fragment restriction falls. An `I`-returning neutral is a
-- second node in the split monad — `usI`: a neutral consumed for
-- nothing, spliced as `ƛr ∘ (n ⊗ 1)`. With it, `reflect` is total by
-- type recursion, the right-purity witnesses `Good`/`GoodR` DISSOLVE,
-- and
--
--   NF : CTm A B → CTm A B
--
-- is a total normalizer for the WHOLE closed linear core: β⊸, η⊸,
-- let-splits of neutral pairs, uses of neutral units, and the entire
-- structural theory all computed away by evaluation.
--
-- What the unit problem REMAINS, precisely: canonicity of emission
-- order. Independent `usI`/`spl` nodes commute (a unit-use binds
-- nothing; disjoint splits do not interact), so βη-equal programs can
-- reify to normal forms differing by node order — e.g. a unit-use
-- INSIDE a pair component vs. hoisted OUTSIDE the pair. Deciding
-- equality of `Sp`-trees modulo these commutations is the proof-net
-- layer (L3.2b/L3.3b); the demos below have forced orders. Adequacy
-- (NF respects and reflects `_≈c_`) is the other open theorem —
-- to be proven once, over this total model.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonJ where

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

  exch : ∀ Γ₁ Θ₁ Θ₂ → Perm (Γ₁ ++ (Θ₁ ++ Θ₂)) (Θ₁ ++ (Γ₁ ++ Θ₂))
  exch Γ₁ Θ₁ Θ₂ =
    psubst (++-assoc Θ₁ Γ₁ Θ₂)
      (psubst (sym (++-assoc Γ₁ Θ₁ Θ₂)) (pid (Γ₁ ++ (Θ₁ ++ Θ₂)))
       ⊙P padʳ Θ₂ (bswapW Γ₁ Θ₁))

  carry² : ∀ {X Y} Γ₁ Θ₂ →
           Perm (X ∷ (Y ∷ (Γ₁ ++ Θ₂))) (Γ₁ ++ (X ∷ (Y ∷ Θ₂)))
  carry² Γ₁ Θ₂ =
    pcons (pcons (pid (Γ₁ ++ Θ₂)) (insˡ Γ₁ here)) (insˡ Γ₁ here)

------------------------------------------------------------------------
-- The split monad, complete: pair-splits AND unit-uses.
------------------------------------------------------------------------

data Sp (P : Ctx → Set) : Ctx → Set where
  ret : ∀ {Γ} → P Γ → Sp P Γ
  spl : ∀ {Γ X Y Γ₁ Γ₂} →
        Perm Γ (Γ₁ ++ Γ₂) → CTm ⟪ Γ₁ ⟫ (X ⊗ Y) →
        Sp P (X ∷ (Y ∷ Γ₂)) → Sp P Γ
  usI : ∀ {Γ Γ₁ Γ₂} →
        Perm Γ (Γ₁ ++ Γ₂) → CTm ⟪ Γ₁ ⟫ I →
        Sp P Γ₂ → Sp P Γ

mapSp : ∀ {P Q Γ} → (∀ {Δ} → P Δ → Q Δ) → Sp P Γ → Sp Q Γ
mapSp f (ret p)     = ret (f p)
mapSp f (spl ρ n k) = spl ρ n (mapSp f k)
mapSp f (usI ρ n k) = usI ρ n (mapSp f k)

bindSp : ∀ {P Q Γ} → Sp P Γ → (∀ {Δ} → P Δ → Sp Q Δ) → Sp Q Γ
bindSp (ret p)     f = f p
bindSp (spl ρ n k) f = spl ρ n (bindSp k f)
bindSp (usI ρ n k) f = usI ρ n (bindSp k f)

vmapSp : ∀ {P Γ' Γ} → (∀ {Δ' Δ} → Perm Δ' Δ → P Δ → P Δ') →
         Perm Γ' Γ → Sp P Γ → Sp P Γ'
vmapSp pv ρ (ret p)      = ret (pv ρ p)
vmapSp pv ρ (spl ρ₀ n k) = spl (ρ ⊙P ρ₀) n k
vmapSp pv ρ (usI ρ₀ n k) = usI (ρ ⊙P ρ₀) n k

reifySp : ∀ {P T Γ} → (∀ {Δ} → P Δ → CTm ⟪ Δ ⟫ T) → Sp P Γ → CTm ⟪ Γ ⟫ T
reifySp f (ret p) = f p
reifySp f (spl {Γ₁ = Γ₁} {Γ₂} ρ n k) =
  reifySp f k ∘c (αrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ)))
reifySp f (usI {Γ₁ = Γ₁} {Γ₂} ρ n k) =
  reifySp f k ∘c (ƛrc ∘c ((n ⊗c idc) ∘c (mult Γ₁ Γ₂ ∘c permC ρ)))

withSpˡ : ∀ {P Q : Ctx → Set} {Γ Γ₁ Γ₂} →
          Perm Γ (Γ₁ ++ Γ₂) → Sp P Γ₁ →
          (∀ {Δ₁ Δ} → Perm Δ (Δ₁ ++ Γ₂) → P Δ₁ → Sp Q Δ) → Sp Q Γ
withSpˡ ρ (ret p) f = f ρ p
withSpˡ {Γ₂ = Γ₂} ρ (spl {X = X} {Y} {Θ₁} {Θ₂} ρ₁ n k) f =
  spl (psubst (++-assoc Θ₁ Θ₂ Γ₂) (ρ ⊙P padʳ Γ₂ ρ₁)) n
      (withSpˡ (pid (X ∷ (Y ∷ (Θ₂ ++ Γ₂)))) k f)
withSpˡ {Γ₂ = Γ₂} ρ (usI {Γ₁ = Θ₁} {Θ₂} ρ₁ n k) f =
  usI (psubst (++-assoc Θ₁ Θ₂ Γ₂) (ρ ⊙P padʳ Γ₂ ρ₁)) n
      (withSpˡ (pid (Θ₂ ++ Γ₂)) k f)

withSpʳ : ∀ {P Q : Ctx → Set} {Γ Γ₁ Γ₂} →
          Perm Γ (Γ₁ ++ Γ₂) → Sp P Γ₂ →
          (∀ {Δ₂ Δ} → Perm Δ (Γ₁ ++ Δ₂) → P Δ₂ → Sp Q Δ) → Sp Q Γ
withSpʳ ρ (ret p) f = f ρ p
withSpʳ {Γ₁ = Γ₁} ρ (spl {X = X} {Y} {Θ₁} {Θ₂} ρ₂ n k) f =
  spl (ρ ⊙P (padˡ Γ₁ ρ₂ ⊙P exch Γ₁ Θ₁ Θ₂)) n
      (withSpʳ (carry² Γ₁ Θ₂) k f)
withSpʳ {Γ₁ = Γ₁} ρ (usI {Γ₁ = Θ₁} {Θ₂} ρ₂ n k) f =
  usI (ρ ⊙P (padˡ Γ₁ ρ₂ ⊙P exch Γ₁ Θ₁ Θ₂)) n
      (withSpʳ (pid (Γ₁ ++ Θ₂)) k f)

------------------------------------------------------------------------
-- The model, v3 — no fragment restriction anywhere.
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

absorb : ∀ A {Γ} → Sp (Val A) Γ → Val A Γ
absorb ι₁ (ret v) = v
absorb ι₁ {Γ} sp@(spl _ _ _) =
  Γ , (pid Γ , reifySp (λ (Γ₀ , (ρ₀ , n)) → n ∘c permC ρ₀) sp)
absorb ι₁ {Γ} sp@(usI _ _ _) =
  Γ , (pid Γ , reifySp (λ (Γ₀ , (ρ₀ , n)) → n ∘c permC ρ₀) sp)
absorb ι₂ (ret v) = v
absorb ι₂ {Γ} sp@(spl _ _ _) =
  Γ , (pid Γ , reifySp (λ (Γ₀ , (ρ₀ , n)) → n ∘c permC ρ₀) sp)
absorb ι₂ {Γ} sp@(usI _ _ _) =
  Γ , (pid Γ , reifySp (λ (Γ₀ , (ρ₀ , n)) → n ∘c permC ρ₀) sp)
absorb I       sp = bindSp sp (λ v → v)
absorb (A ⊗ B) sp = bindSp sp (λ v → v)
absorb (A ⊸ B) sp = λ Δ v → absorb B (go Δ v sp)
  where
  go : ∀ Δ → Val A Δ → ∀ {Γ} → Sp (Val (A ⊸ B)) Γ → Sp (Val B) (Γ ++ Δ)
  go Δ v (ret f) = ret (f Δ v)
  go Δ v (spl {Γ₁ = Θ₁} {Θ₂} ρ n k) =
    spl (psubst (++-assoc Θ₁ Θ₂ Δ) (padʳ Δ ρ)) n (go Δ v k)
  go Δ v (usI {Γ₁ = Θ₁} {Θ₂} ρ n k) =
    usI (psubst (++-assoc Θ₁ Θ₂ Δ) (padʳ Δ ρ)) n (go Δ v k)

------------------------------------------------------------------------
-- Evaluation — textually the L3.2 code; the new node rides inside the
-- combinators.
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
-- Reify and reflect — TOTAL, by type recursion. No witnesses.
------------------------------------------------------------------------

mutual
  reify : ∀ A {Γ} → Val A Γ → CTm ⟪ Γ ⟫ A
  reify ι₁ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reify ι₂ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  reify I  v = reifySp (λ { refl → idc }) v
  reify (A ⊗ B) v =
    reifySp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
      ((reify A va ⊗c reify B vb) ∘c mult Δ₁ Δ₂) ∘c permC ρ) v
  reify (A ⊸ B) {Γ} f =
    Λc (reify B (f (ctxOf A) (reflectTy A)) ∘c
        (multInv Γ (ctxOf A) ∘c (idc ⊗c splitTm A)))

  reflectTy : ∀ A → Val A (ctxOf A)
  reflectTy ι₁ = (ι₁ ∷ ε) , (pid (ι₁ ∷ ε) , ρrc)
  reflectTy ι₂ = (ι₂ ∷ ε) , (pid (ι₂ ∷ ε) , ρrc)
  reflectTy I  = ret refl
  reflectTy (A ⊗ B) =
    ret (ctxOf A , (ctxOf B ,
      (pid (ctxOf A ++ ctxOf B) , (reflectTy A , reflectTy B))))
  reflectTy (A ⊸ B) =
    λ Δ v → reflectNe B (evc ∘c (idc ⊗c reify A v))

  reflectNe : ∀ B {Γ} → CTm ⟪ Γ ⟫ B → Val B Γ
  reflectNe ι₁ {Γ} n = Γ , (pid Γ , n)
  reflectNe ι₂ {Γ} n = Γ , (pid Γ , n)
  reflectNe I  {Γ} n =
    usI (psubst (sym (++-idʳ Γ)) (pid Γ)) n (ret refl)
  reflectNe (X ⊗ Y) {Γ} n =
    spl (psubst (sym (++-idʳ Γ)) (pid Γ)) n
        (ret ((X ∷ ε) , ((Y ∷ ε) ,
          ( pid (X ∷ (Y ∷ ε))
          , (reflectNe X ρrc , reflectNe Y ρrc)))))
  reflectNe (A ⊸ B) {Γ} n =
    λ Δ v → reflectNe B ((evc ∘c (n ⊗c reify A v)) ∘c mult Γ Δ)

------------------------------------------------------------------------
-- THE TOTAL NORMALIZER.
------------------------------------------------------------------------

NF : ∀ {A B} → CTm A B → CTm A B
NF {A} f = reify _ (evalV f (reflectTy A)) ∘c splitTm A

------------------------------------------------------------------------
-- Demos — the whole suite, no witnesses, plus the unit crossings.
------------------------------------------------------------------------

private
  _ : NF (evc ∘c (Λc (σc {ι₁} {ι₂}) ⊗c idc)) ≡ NF σc
  _ = refl

  _ : NF (Λc (evc ∘c (idc {ι₁ ⊸ ι₂} ⊗c idc))) ≡ NF idc
  _ = refl

  _ : NF (σc {ι₂} {ι₁} ∘c σc) ≡ NF (idc {ι₁ ⊗ ι₂})
  _ = refl

  flipC : ∀ {A B D} → CTm A (B ⊸ D) → CTm B (A ⊸ D)
  flipC g = Λc (evc ∘c ((g ⊗c idc) ∘c σc))

  _ : NF (flipC (flipC (idc {ι₁ ⊸ ι₂}))) ≡ NF idc
  _ = refl

  _ : NF (Λc ((σc ∘c σc) ∘c evc)) ≡ NF (idc {ι₁ ⊸ (ι₁ ⊗ ι₂)})
  _ = refl

  -- UNITS CROSSED: η at a unit-RETURNING function type — the type the
  -- fragment ladder could not touch until now.
  _ : NF (Λc (evc ∘c (idc {ι₁ ⊸ I} ⊗c idc))) ≡ NF idc
  _ = refl

  -- Units as arguments, through the full higher-order path.
  _ : NF (flipC (flipC (idc {I ⊸ ι₂}))) ≡ NF idc
  _ = refl
