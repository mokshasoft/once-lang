------------------------------------------------------------------------
-- OCP-0009 · rung 2b part 2, STAGE L3.4a — PLACEMENT CANONICITY:
--            the hoisting normalizer
--
-- L3.3's `NF` is total, but βη-equal programs could reify to normal
-- forms differing in WHERE independent `spl`/`usI` nodes are emitted —
-- inside a pair component on one route, hoisted outside on another.
-- This stage removes the PLACEMENT variance structurally:
--
--   * Atoms are Sp-carriers too (`Val ι = Sp (Core ι)`), so `absorb`
--     is a uniform `join` at every positive type — nodes are never
--     baked into neutral syntax mid-evaluation (L3.3's atom-`absorb`
--     did, freezing a placement choice).
--   * `hoist`/`Core` — before emission, `reify` PULLS every node out
--     of pair components to the enclosing boundary (`withSpˡ`/
--     `withSpʳ` chains), recursively; `Core` values are surface-node-
--     free. Functions stay opaque (their nodes surface inside their
--     λ, when probed).
--   * The u3-class equality that L3.3 could NOT decide — rebuilding a
--     unit-carrying pair through ƛ-eliminators vs. not touching it —
--     now checks by `refl`.
--
-- What remains for FULL canonicity (the proof-net core, recorded):
--   (a) ORDER of independent nodes at the same boundary — needs the
--       adjacent-swap sort keyed by consumed world positions (linear ⇒
--       disjoint ⇒ totally ordered); confluence = trace-monoid normal
--       form.
--   (b) λ-BOUNDARY commutation — a node independent of the argument
--       may sit inside or outside a `Λc`; deciding needs per-node
--       argument-dependence analysis on its repartition.
-- Both are localized to `Sp`-tree post-processing over THIS model.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module poc.OCP0009.NbEPMonF where

open import normalizer.Syntax.Types
  using ( Σ; _,_; _≡_; refl; sym )
open import poc.OCP0009.NbEPMonL
  using ( CTy; ι₁; ι₂; I; _⊗_; _⊸_
        ; CTm; idc; _∘c_; _⊗c_; αrc; αlc; ƛrc; ƛlc; ρrc; ρlc; σc
        ; Λc; evc )
open import poc.OCP0009.NbEPMonT
  using ( Ctx; ε; _∷_; _++_
        ; Ins; here; there; Perm; pnil; pcons; pid
        ; _⊙P_; insˡ; padˡ; padʳ; bswapW
        ; pidR; pidRInv; passoc; passocInv; exch; carry² )
open import poc.OCP0009.NbEPMonW
  using ( ⟪_⟫; permC; mult; multInv; ctxOf; splitTm )

private
  perm-ε : ∀ {Γ} → Perm Γ ε → Γ ≡ ε
  perm-ε pnil = refl

------------------------------------------------------------------------
-- The split monad (as L3.3).
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
  spl ((ρ ⊙P padʳ Γ₂ ρ₁) ⊙P passoc Θ₁ Θ₂ Γ₂) n
      (withSpˡ (pid (X ∷ (Y ∷ (Θ₂ ++ Γ₂)))) k f)
withSpˡ {Γ₂ = Γ₂} ρ (usI {Γ₁ = Θ₁} {Θ₂} ρ₁ n k) f =
  usI ((ρ ⊙P padʳ Γ₂ ρ₁) ⊙P passoc Θ₁ Θ₂ Γ₂) n
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
-- The model, v4: EVERY positive type is an Sp-carrier — placement is
-- never frozen mid-evaluation.
------------------------------------------------------------------------

AtCore : CTy → Ctx → Set
AtCore A Δ = Σ Ctx (λ Γ₀ → Σ (Perm Δ Γ₀) (λ _ → CTm ⟪ Γ₀ ⟫ A))

Val : CTy → Ctx → Set
Val ι₁      Γ = Sp (AtCore ι₁) Γ
Val ι₂      Γ = Sp (AtCore ι₂) Γ
Val I       Γ = Sp (λ Δ → Δ ≡ ε) Γ
Val (A ⊗ B) Γ = Sp (λ Δ →
  Σ Ctx (λ Δ₁ → Σ Ctx (λ Δ₂ →
    Σ (Perm Δ (Δ₁ ++ Δ₂)) (λ _ → Σ (Val A Δ₁) (λ _ → Val B Δ₂))))) Γ
Val (A ⊸ B) Γ = ∀ Δ → Val A Δ → Val B (Γ ++ Δ)

private
  pvAt : ∀ {A Δ' Δ} → Perm Δ' Δ → AtCore A Δ → AtCore A Δ'
  pvAt ρ (Γ₀ , (ρ₀ , n)) = Γ₀ , ((ρ ⊙P ρ₀) , n)

  pvI : ∀ {Δ' Δ} → Perm Δ' Δ → Δ ≡ ε → Δ' ≡ ε
  pvI ρ' refl = perm-ε ρ'

vmap : ∀ A {Γ' Γ} → Perm Γ' Γ → Val A Γ → Val A Γ'
vmap ι₁      ρ v = vmapSp pvAt ρ v
vmap ι₂      ρ v = vmapSp pvAt ρ v
vmap I       ρ v = vmapSp pvI ρ v
vmap (A ⊗ B) ρ v =
  vmapSp (λ ρ' (Δ₁ , (Δ₂ , (ρ₀ , x))) → Δ₁ , (Δ₂ , ((ρ' ⊙P ρ₀) , x)))
         ρ v
vmap (A ⊸ B) ρ f = λ Δ v → vmap B (padʳ Δ ρ) (f Δ v)

-- Application under pending splits (absorb's ⊸-pusher, top level so
-- the adequacy layer can splice it).
appSp : ∀ {A B} (Δ : Ctx) → Val A Δ →
        ∀ {Γ} → Sp (Val (A ⊸ B)) Γ → Sp (Val B) (Γ ++ Δ)
appSp Δ v (ret f) = ret (f Δ v)
appSp Δ v (spl {Γ₁ = Θ₁} {Θ₂} ρ n k) =
  spl (padʳ Δ ρ ⊙P passoc Θ₁ Θ₂ Δ) n (appSp Δ v k)
appSp Δ v (usI {Γ₁ = Θ₁} {Θ₂} ρ n k) =
  usI (padʳ Δ ρ ⊙P passoc Θ₁ Θ₂ Δ) n (appSp Δ v k)

-- Absorption is a uniform join at every positive type.
absorb : ∀ A {Γ} → Sp (Val A) Γ → Val A Γ
absorb ι₁      sp = bindSp sp (λ v → v)
absorb ι₂      sp = bindSp sp (λ v → v)
absorb I       sp = bindSp sp (λ v → v)
absorb (A ⊗ B) sp = bindSp sp (λ v → v)
absorb (A ⊸ B) sp = λ Δ v → absorb B (appSp Δ v sp)

------------------------------------------------------------------------
-- Evaluation — textually L3.3.
--
-- The α/ƛ/ρ continuations are lifted to top level (rather than local
-- `where`s / inline λ) so the adequacy proof (Adq15) can name the exact
-- same function when matching `evalV αrc`/`αlc`/`ƛrc`/`ρrc`.
------------------------------------------------------------------------

-- The tensor split-leaf functor (Val (A ⊗ B) Γ = Sp (⊗Leaf A B) Γ).
⊗Leaf : CTy → CTy → Ctx → Set
⊗Leaf A B Δ =
  Σ Ctx (λ Δ₁ → Σ Ctx (λ Δ₂ →
    Σ (Perm Δ (Δ₁ ++ Δ₂)) (λ _ → Σ (Val A Δ₁) (λ _ → Val B Δ₂))))

evkαi : ∀ {A B D Δ₂} → Val D Δ₂ →
        ∀ {Θ Δ} → Perm Δ (Θ ++ Δ₂) → ⊗Leaf A B Θ →
        Sp (⊗Leaf A (B ⊗ D)) Δ
evkαi {Δ₂ = Δ₂} vd ρ' (Θ₁ , (Θ₂ , (ρᵢ , (va , vb)))) =
  ret (Θ₁ , ((Θ₂ ++ Δ₂) ,
    ( ((ρ' ⊙P padʳ Δ₂ ρᵢ) ⊙P passoc Θ₁ Θ₂ Δ₂)
    , (va , ret (Θ₂ , (Δ₂ , (pid (Θ₂ ++ Δ₂) , (vb , vd))))))))

evkα : ∀ {A B D Δ} → ⊗Leaf (A ⊗ B) D Δ → Val (A ⊗ (B ⊗ D)) Δ
evkα (Δ₁ , (Δ₂ , (ρ , (vab , vd)))) = withSpˡ ρ vab (evkαi vd)

evkαli : ∀ {A B D Δ₁} → Val A Δ₁ →
         ∀ {Θ Δ} → Perm Δ (Δ₁ ++ Θ) → ⊗Leaf B D Θ →
         Sp (⊗Leaf (A ⊗ B) D) Δ
evkαli {Δ₁ = Δ₁} va ρ' (Θ₁ , (Θ₂ , (ρᵢ , (vb , vd)))) =
  ret ((Δ₁ ++ Θ₁) , (Θ₂ ,
    ( ((ρ' ⊙P padˡ Δ₁ ρᵢ) ⊙P passocInv Δ₁ Θ₁ Θ₂)
    , (ret (Δ₁ , (Θ₁ , (pid (Δ₁ ++ Θ₁) , (va , vb)))) , vd))))

evkαl : ∀ {A B D Δ} → ⊗Leaf A (B ⊗ D) Δ → Val ((A ⊗ B) ⊗ D) Δ
evkαl (Δ₁ , (Δ₂ , (ρ , (va , vbd)))) = withSpʳ ρ vbd (evkαli va)

evkƛ : ∀ A {Δ₂} → Val A Δ₂ →
       ∀ {Δ₁' Δ} → Perm Δ (Δ₁' ++ Δ₂) → Δ₁' ≡ ε → Sp (Val A) Δ
evkƛ A va ρ' refl = ret (vmap A ρ' va)

evkƛo : ∀ {A Δ} → ⊗Leaf I A Δ → Sp (Val A) Δ
evkƛo {A} (Δ₁ , (Δ₂ , (ρ , (vI , va)))) = withSpˡ ρ vI (evkƛ A va)

evkρ : ∀ A {Δ₁} → Val A Δ₁ →
       ∀ {Δ₂' Δ} → Perm Δ (Δ₁ ++ Δ₂') → Δ₂' ≡ ε → Sp (Val A) Δ
evkρ A {Δ₁} va ρ' refl = ret (vmap A (ρ' ⊙P pidRInv Δ₁) va)

evkρo : ∀ {A Δ} → ⊗Leaf A I Δ → Sp (Val A) Δ
evkρo {A} (Δ₁ , (Δ₂ , (ρ , (va , vI)))) = withSpʳ ρ vI (evkρ A va)

evalV : ∀ {A B} → CTm A B → ∀ {Γ} → Val A Γ → Val B Γ
evalV idc      v = v
evalV (f ∘c g) v = evalV f (evalV g v)
evalV (f ⊗c g) v =
  mapSp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
          Δ₁ , (Δ₂ , (ρ , (evalV f va , evalV g vb)))) v
evalV αrc v = bindSp v evkα
evalV αlc v = bindSp v evkαl
evalV {B = A} ƛrc v = absorb A (bindSp v evkƛo)
evalV ƛlc {Γ} v = ret (ε , (Γ , (pid Γ , (ret refl , v))))
evalV {B = A} ρrc v = absorb A (bindSp v evkρo)
evalV ρlc {Γ} v =
  ret (Γ , (ε , (pidR Γ , (v , ret refl))))
evalV σc v =
  mapSp (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
          Δ₂ , (Δ₁ , ((ρ ⊙P bswapW Δ₁ Δ₂) , (vb , va)))) v
evalV (Λc f) {Γ} v =
  λ Δ w → evalV f (ret (Γ , (Δ , (pid (Γ ++ Δ) , (v , w)))))
evalV {B = B} evc v =
  absorb B (bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (vf , va)))) →
    ret (vmap B ρ (vf Δ₂ va))))

------------------------------------------------------------------------
-- HOISTING: Core values are surface-node-free; `hoist` pulls every
-- component node up to the enclosing boundary before emission.
------------------------------------------------------------------------

Core : CTy → Ctx → Set
Core ι₁      Δ = AtCore ι₁ Δ
Core ι₂      Δ = AtCore ι₂ Δ
Core I       Δ = Δ ≡ ε
Core (A ⊗ B) Δ =
  Σ Ctx (λ Δ₁ → Σ Ctx (λ Δ₂ →
    Σ (Perm Δ (Δ₁ ++ Δ₂)) (λ _ → Σ (Core A Δ₁) (λ _ → Core B Δ₂))))
Core (A ⊸ B) Δ = Val (A ⊸ B) Δ

hoist : ∀ A {Γ} → Val A Γ → Sp (Core A) Γ
hoist ι₁      v = v
hoist ι₂      v = v
hoist I       v = v
hoist (A ⊗ B) v =
  bindSp v (λ (Δ₁ , (Δ₂ , (ρ , (va , vb)))) →
    withSpˡ ρ (hoist A va) (λ ρ' ca →
      withSpʳ ρ' (hoist B vb) (λ ρ'' cb →
        ret (_ , (_ , (ρ'' , (ca , cb)))))))
hoist (A ⊸ B) f = ret f

------------------------------------------------------------------------
-- Reify and reflect — the canonical (hoisting) emission.
------------------------------------------------------------------------

mutual
  reify : ∀ A {Γ} → Val A Γ → CTm ⟪ Γ ⟫ A
  reify A v = reifySp (emit A) (hoist A v)

  emit : ∀ A {Δ} → Core A Δ → CTm ⟪ Δ ⟫ A
  emit ι₁ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  emit ι₂ (Γ₀ , (ρ₀ , n)) = n ∘c permC ρ₀
  emit I  refl = idc
  emit (A ⊗ B) (Δ₁ , (Δ₂ , (ρ , (ca , cb)))) =
    ((emit A ca ⊗c emit B cb) ∘c mult Δ₁ Δ₂) ∘c permC ρ
  emit (A ⊸ B) {Δ} f =
    Λc (reify B (f (ctxOf A) (reflectTy A)) ∘c
        (multInv Δ (ctxOf A) ∘c (idc ⊗c splitTm A)))

  reflectTy : ∀ A → Val A (ctxOf A)
  reflectTy ι₁ = ret ((ι₁ ∷ ε) , (pid (ι₁ ∷ ε) , ρrc))
  reflectTy ι₂ = ret ((ι₂ ∷ ε) , (pid (ι₂ ∷ ε) , ρrc))
  reflectTy I  = ret refl
  reflectTy (A ⊗ B) =
    ret (ctxOf A , (ctxOf B ,
      (pid (ctxOf A ++ ctxOf B) , (reflectTy A , reflectTy B))))
  reflectTy (A ⊸ B) =
    λ Δ v → reflectNe B (evc ∘c (idc ⊗c reify A v))

  reflectNe : ∀ B {Γ} → CTm ⟪ Γ ⟫ B → Val B Γ
  reflectNe ι₁ {Γ} n = ret (Γ , (pid Γ , n))
  reflectNe ι₂ {Γ} n = ret (Γ , (pid Γ , n))
  reflectNe I  {Γ} n =
    usI (pidR Γ) n (ret refl)
  reflectNe (X ⊗ Y) {Γ} n =
    spl (pidR Γ) n
        (ret ((X ∷ ε) , ((Y ∷ ε) ,
          ( pid (X ∷ (Y ∷ ε))
          , (reflectNe X ρrc , reflectNe Y ρrc)))))
  reflectNe (A ⊸ B) {Γ} n =
    λ Δ v → reflectNe B ((evc ∘c (n ⊗c reify A v)) ∘c mult Γ Δ)

------------------------------------------------------------------------
-- THE CANONICAL NORMALIZER.
------------------------------------------------------------------------

NF : ∀ {A B} → CTm A B → CTm A B
NF {A} f = reify _ (evalV f (reflectTy A)) ∘c splitTm A

------------------------------------------------------------------------
-- Demos — the L3.3 suite, plus the placement-variance equality that
-- L3.3 could NOT decide.
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

  _ : NF (Λc (evc ∘c (idc {ι₁ ⊸ I} ⊗c idc))) ≡ NF idc
  _ = refl

  _ : NF (flipC (flipC (idc {I ⊸ ι₂}))) ≡ NF idc
  _ = refl

  -- PLACEMENT CANONICITY: rebuild a unit-carrying neutral pair through
  -- the ƛ-eliminators — one route hoists the unit-use, the other
  -- leaves it in the component. L3.3 reified these DIFFERENTLY; the
  -- hoisting normalizer decides the equality by refl.
  _ : NF (Λc ((ƛlc ∘c ƛrc) ∘c evc)) ≡ NF (idc {ι₁ ⊸ (I ⊗ ι₂)})
  _ = refl

  -- STABILITY: normal forms are fixed points of NF (idempotence, on
  -- the suite's shapes) — the checkable face of "NF lands in normal
  -- forms", ahead of the full adequacy theorem.
  _ : NF (NF (flipC (flipC (idc {ι₁ ⊸ ι₂})))) ≡ NF (flipC (flipC idc))
  _ = refl

  _ : NF (NF (Λc ((ƛlc ∘c ƛrc) ∘c evc {ι₁} {I ⊗ ι₂})))
      ≡ NF (Λc ((ƛlc ∘c ƛrc) ∘c evc))
  _ = refl
